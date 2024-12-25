using Microsoft.VisualBasic;
using ndev.LicenseKey;
using System;
using System.Collections;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.ComponentModel;
using System.Data;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Runtime.CompilerServices;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using System.Timers;
using Microsoft.VisualBasic.CompilerServices;
using System.Drawing;
using System.Drawing.Imaging;
using System.Windows.Forms;

namespace KGKJetPrinterLib
{
    public sealed class KGKJetPrinter : Component
    {
        private enum SendCommandType
        {
            CheckState,
            Control,
            GetData
        }
        public enum FontType
        {
            hi5 = 5,
            hi7 = 7,
            hi9 = 9,
            hi12 = 12,
            hi16 = 16,
            hi24 = 24,
            hi34 = 34
        }
        public enum Direction
        {
            Decrement,
            Increment
        }
        public enum PrintHeadState
        {
            Unknown,
            Stopping, // 0
            StoppingAndCoverOpen, // 1
            PreparationOfRunning, // 2
            PreparationOfRunningAndCoverOpen, // 3
            Running, // 4
            PreparationOfStopping, // 5
            Maintenance // 6
        }
        public enum PrintHeadHeaterState
        {
            Unknown,
            OFF, // 0
            ON // 1
        }
        public enum VisicosityState
        {
            Unknown,
            Normal, // 0
            Low, // 1
            High, // 2
            NotPerformed // 3
        }
        public enum LiquidQuantity
        {
            Unknown,
            Low, // 0
            Full, // 1
            Empty, // 2
            SensorTrouble // 3
        }
        public enum ConnectionState
        {
            Closed,
            Open,
            Listening,
            ConnectionPending,
            ResolvingHost,
            HostResolved,
            Connecting,
            Connected,
            Closing,
            Error
        }

        #region variables

        [Browsable(false)]
        public ConnectionState GetState => _State;

        [Browsable(false)]
        public PrintHeadState GetPrinterState => _PrintHeadState;

        private static List<WeakReference> __ENCList = new List<WeakReference>();

        public string _RemoteIP;

        public int _LocalPort;

        public int _RemotePort;

        private ConnectionState _State;

        private string _sBuffer;

        private byte[] _buffer;

        private Collection _bufferCol;

        private byte[] _byteBuffer;

        private Socket _sockList;

        private IContainer components;

        private Socket _Client;

        private clsRegistration registration;

        private PrintHeadState _PrintHeadState;

        private PrintHeadHeaterState _PrintHeadHeaterState;

        private LiquidQuantity _LiquidQuantityInkTankState;

        private LiquidQuantity _LiquidQuantitySolventTankState;

        private LiquidQuantity _LiquidQuantityMainTankState;

        private VisicosityState _VisicosityState;

        private string _PrinterArrivalData;

        private bool _IsDataArrival;

        private SendCommandType _SendCommandType;

        private bool _WaitingData;

        private byte[] _ArrivalData;

        private string _ATTRIB;

        public uint _LastPrintCount;

        public int _diff;

        private System.Timers.Timer Timer1;

        private System.Timers.Timer Timer2;

        private System.Timers.Timer Timer3;

        private System.Timers.Timer CheckFinishPrintTimer;

        private int LocalPort
        {
            get
            {
                return _LocalPort;
            }
            set
            {
                if (GetState == ConnectionState.Closed)
                {
                    _LocalPort = value;
                    return;
                }

                throw new Exception("Must be idle to change the local port");
            }
        }
        private int RemotePort
        {
            get
            {
                return _RemotePort;
            }
            set
            {
                if (GetState != ConnectionState.Connected)
                {
                    _RemotePort = value;
                    return;
                }

                throw new Exception("Can't be connected to a server and change the remote port.");
            }
        }
        public string RemoteIP
        {
            get
            {
                return _RemoteIP;
            }
            set
            {
                if (GetState == ConnectionState.Closed)
                {
                    _RemoteIP = value;
                    return;
                }

                throw new Exception("Must be closed to set the remote ip.");
            }
        }
        private bool m_bAutoReconnect = false;
        public bool AutoReconnect
        {
            get => m_bAutoReconnect;
            set
            {
                m_bAutoReconnect = value;
            }
        }

        private int m_nCurrentMessageNo = -1;
        public int CurrentMessageNo
        {
            get => m_nCurrentMessageNo;
            set
            {
                if (m_nCurrentMessageNo != value)
                {
                    m_nCurrentMessageNo = value;
                }
            }
        }
        #endregion

        #region Constructor
        public KGKJetPrinter()
        : this(1024)
        {
        }

        public KGKJetPrinter(long Port)
            : this("192.168.1.12", Port)
        {
        }

        public KGKJetPrinter(string IP)
            : this(IP, 1024L)
        {
        }

        public KGKJetPrinter(string IP, long Port)
        {
            base.Disposed += VideoJetPrinterW_Disposed;
            DataArrival += ProcessDataArrival;
            StateChanged += CheckConnectionState;
            __ENCAddToList(this);
            _RemoteIP = "192.168.1.12";
            _LocalPort = 1024;
            _RemotePort = 1024;
            _State = ConnectionState.Closed;
            _byteBuffer = new byte[1025];
            registration = new clsRegistration();
            _PrintHeadState = PrintHeadState.Unknown;
            _PrintHeadHeaterState = PrintHeadHeaterState.Unknown;
            _LiquidQuantityInkTankState = LiquidQuantity.Unknown;
            _LiquidQuantitySolventTankState = LiquidQuantity.Unknown;
            _LiquidQuantityMainTankState = LiquidQuantity.Unknown;
            _VisicosityState = VisicosityState.Unknown;
            _IsDataArrival = false;
            _SendCommandType = SendCommandType.Control;
            _WaitingData = false;
            _ATTRIB = "000000";
            _LastPrintCount = 0;
            _diff = 0;
            checked
            {
                if (registration.GetRegistered)
                {
                    RemoteIP = IP;
                    RemotePort = (int)Port;
                    LocalPort = (int)Port;
                    _bufferCol = new Collection();
                    SetTimer();
                }
                else
                {
                    Dispose();
                }
            }
        }
        #endregion

        #region delegates and events
        public delegate void ConnectedEventHandler(KGKJetPrinter sender);

        public delegate void DisconnectedEventHandler(KGKJetPrinter sender);

        private delegate void DataArrivalEventHandler(KGKJetPrinter sender, int BytesTotal);

        private delegate void ConnectionRequestEventHandler(KGKJetPrinter sender, Socket requestID);

        public delegate void HandleErrorEventHandler(KGKJetPrinter sender, string Description, string Method, string myEx);

        private delegate void StateChangedEventHandler(KGKJetPrinter sender, ConnectionState state);

        public delegate void ConnectionStateChangedEventHandler(KGKJetPrinter sender, ConnectionState state);

        public delegate void PrinterStateChangedEventHandler(KGKJetPrinter sender, PrintHeadState printHeadState, PrintHeadHeaterState heaterState,
                                                             LiquidQuantity inkTankState, LiquidQuantity solventState, LiquidQuantity mainTankState, VisicosityState visState);

        public delegate void PrintCountChangedHandler(KGKJetPrinter sender);

        private delegate void MessagePrintCompletedEventHandler(KGKJetPrinter sender);


        [method: DebuggerNonUserCode]
        public event ConnectedEventHandler Connected;

        [method: DebuggerNonUserCode]
        public event DisconnectedEventHandler Disconnected;

        [method: DebuggerNonUserCode]
        private event DataArrivalEventHandler DataArrival;

        [method: DebuggerNonUserCode]
        private event ConnectionRequestEventHandler ConnectionRequest;

        [method: DebuggerNonUserCode]
        public event HandleErrorEventHandler HandleError;

        [method: DebuggerNonUserCode]
        private event StateChangedEventHandler StateChanged;

        [method: DebuggerNonUserCode]
        public event ConnectionStateChangedEventHandler ConnectionStateChanged;

        [method: DebuggerNonUserCode]
        public event PrinterStateChangedEventHandler PrinterStateChanged;

        [method: DebuggerNonUserCode]
        public event PrintCountChangedHandler PrintCountChanged;

        [method: DebuggerNonUserCode]
        private event MessagePrintCompletedEventHandler MessagePrintCompleted;
        #endregion

        #region Functions
        [DebuggerNonUserCode]
        private static void __ENCAddToList(object value)
        {
            checked
            {
                lock (__ENCList)
                {
                    if (__ENCList.Count == __ENCList.Capacity)
                    {
                        int num = 0;
                        int num2 = __ENCList.Count - 1;
                        int num3 = 0;
                        while (true)
                        {
                            int num4 = num3;
                            int num5 = num2;
                            if (num4 > num5)
                            {
                                break;
                            }

                            WeakReference weakReference = __ENCList[num3];
                            if (weakReference.IsAlive)
                            {
                                if (num3 != num)
                                {
                                    __ENCList[num] = __ENCList[num3];
                                }

                                num++;
                            }

                            num3++;
                        }

                        __ENCList.RemoveRange(num, __ENCList.Count - num);
                        __ENCList.Capacity = __ENCList.Count;
                    }

                    __ENCList.Add(new WeakReference(RuntimeHelpers.GetObjectValue(value)));
                }
            }
        }

        private void Listen()
        {
            Thread thread = new Thread(DoListen);
            thread.Start();
        }

        private void Close()
        {
            try
            {
                switch ((int)GetState)
                {
                    case 2:
                        ChangeState(ConnectionState.Closing);
                        _sockList.Close();
                        break;
                    case 1:
                    case 3:
                    case 4:
                    case 5:
                    case 6:
                    case 7:
                        ChangeState(ConnectionState.Closing);
                        _Client.Close();
                        break;
                }

                ChangeState(ConnectionState.Closed);
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                ChangeState(ConnectionState.Error);
                HandleError?.Invoke(this, ex2.Message, ex2.TargetSite.Name, ex2.ToString());
                ProjectData.ClearProjectError();
            }
        }
        private void Accept(Socket requestID)
        {
            try
            {
                ChangeState(ConnectionState.ConnectionPending);
                _Client = requestID;
                Connected?.Invoke(this);
                ChangeState(ConnectionState.Connected);
                _Client.BeginReceive(_byteBuffer, 0, 1024, SocketFlags.None, DoStreamReceive, null);
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                ChangeState(ConnectionState.Error);
                HandleError?.Invoke(this, ex2.Message, ex2.TargetSite.Name, ex2.ToString());
                ProjectData.ClearProjectError();
            }
        }

        private void Connect()
        {
            if ((GetState == ConnectionState.Connected) | (GetState == ConnectionState.Listening))
            {
                HandleError?.Invoke(this, "Already open, must be closed first", "Connect", "Nothing here");
                return;
            }

            try
            {
                ChangeState(ConnectionState.ResolvingHost);
                string ipString = default(string);
                try
                {
                    IPAddress iPAddress = IPAddress.Parse(_RemoteIP);
                    ipString = iPAddress.ToString();
                }
                catch (Exception ex)
                {
                    ProjectData.SetProjectError(ex);
                    Exception ex2 = ex;
                    try
                    {
                        IPHostEntry hostByName = Dns.GetHostByName(_RemoteIP);
                        IPAddress[] addressList = hostByName.AddressList;
                        ipString = addressList[0].ToString();
                    }
                    catch (Exception ex3)
                    {
                        ProjectData.SetProjectError(ex3);
                        Exception ex4 = ex3;
                        ChangeState(ConnectionState.Error);
                        HandleError?.Invoke(this, ex4.Message, ex4.TargetSite.Name, ex4.ToString());
                        ProjectData.ClearProjectError();
                    }

                    ProjectData.ClearProjectError();
                }

                ChangeState(ConnectionState.HostResolved);
                _Client = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp);
                IPEndPoint remoteEP = new IPEndPoint(IPAddress.Parse(ipString), RemotePort);
                ChangeState(ConnectionState.Connecting);
                _Client.BeginConnect(remoteEP, OnConnected, null);
            }
            catch (Exception ex5)
            {
                ProjectData.SetProjectError(ex5);
                Exception ex6 = ex5;
                ChangeState(ConnectionState.Error);
                HandleError?.Invoke(this, ex6.Message, ex6.TargetSite.Name, ex6.ToString());
                ProjectData.ClearProjectError();
            }
        }

        private void Connect(string IP, int Port)
        {
            RemoteIP = IP;
            RemotePort = Port;
            Connect();
        }

        public string LocalIP()
        {
            IPHostEntry hostByName = Dns.GetHostByName(Dns.GetHostName());
            return ((IPAddress)hostByName.AddressList.GetValue(0)).ToString();
        }

        public string RemoteHostIP()
        {
            IPEndPoint iPEndPoint = (IPEndPoint)_Client.RemoteEndPoint;
            return iPEndPoint.Address.ToString();
        }

        private void Send(string Data)
        {
            byte[] bytes = Encoding.ASCII.GetBytes(Data);
            Send(bytes);
        }

        private void Send(byte[] Data)
        {
            switch ((int)GetState)
            {
                case 0:
                    break;
                case 2:
                    break;
                case 7:
                    try
                    {
                        Data = (byte[])Utils.CopyArray(Data, new byte[checked(Information.UBound(Data) + 1 + 1)]);
                        Data[Information.UBound(Data)] = 4;
                        _Client.Send(Data);
                        break;
                    }
                    catch (Exception ex)
                    {
                        ProjectData.SetProjectError(ex);
                        Exception ex2 = ex;
                        Close();
                        ChangeState(ConnectionState.Error);
                        HandleError?.Invoke(this, ex2.Message, ex2.TargetSite.Name, ex2.ToString());
                        ProjectData.ClearProjectError();
                        break;
                    }
                case 1:
                case 3:
                case 4:
                case 5:
                case 6:
                    break;
            }
        }

        private void Send(Bitmap Data)
        {
            MemoryStream memoryStream = new MemoryStream();
            Data.Save(memoryStream, ImageFormat.Bmp);
            checked
            {
                byte[] array = new byte[(int)(memoryStream.Length - 1) + 1];
                memoryStream.Position = 0L;
                memoryStream.Read(array, 0, (int)memoryStream.Length);
                Send(array);
            }
        }

        private object GetData(ref string data)
        {
            byte[] bytes = default(byte[]);
            GetData(ref bytes);
            int num = Information.UBound(bytes);
            int num2 = 0;
            while (true)
            {
                int num3 = num2;
                int num4 = num;
                if (num3 > num4)
                {
                    break;
                }

                if (bytes[num2] == 10)
                {
                    data += "\n";
                }
                else
                {
                    data += Conversions.ToString(Strings.ChrW(bytes[num2]));
                }

                num2 = checked(num2 + 1);
            }

            object result = default(object);
            return result;
        }

        private object GetData(ref byte[] bytes)
        {
            if (_bufferCol.Count == 0)
            {
                throw new IndexOutOfRangeException("Nothing in buffer.");
            }

            byte[] array = (byte[])_bufferCol[1];
            _bufferCol.Remove(1);
            bytes = new byte[checked(Information.UBound(array) + 1)];
            array.CopyTo(bytes, 0);
            object result = default(object);
            return result;
        }

        private object GetData(ref Bitmap bitmap)
        {
            byte[] bytes = default(byte[]);
            GetData(ref bytes);
            MemoryStream stream = new MemoryStream(bytes, writable: false);
            bitmap = (Bitmap)System.Drawing.Image.FromStream(stream);
            object result = default(object);
            return result;
        }

        private void ChangeState(ConnectionState new_state)
        {
            _State = new_state;
            StateChanged?.Invoke(this, _State);
        }

        private void OnConnected(IAsyncResult asyn)
        {
            try
            {
                _Client.EndConnect(asyn);
                ClientFinalizeConnection();
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                ChangeState(ConnectionState.Error);
                HandleError?.Invoke(this, ex2.Message, ex2.TargetSite.Name, ex2.ToString());
                ProjectData.ClearProjectError();
            }
        }

        private void ClientFinalizeConnection()
        {
            ChangeState(ConnectionState.Connected);
            _Client.BeginReceive(_byteBuffer, 0, 1024, SocketFlags.None, DoRead, null);
            Connected?.Invoke(this);
        }

        private void DoListen()
        {
            try
            {
                _sockList = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp);
                IPEndPoint localEP = new IPEndPoint(IPAddress.Any, LocalPort);
                _sockList.Bind(localEP);
                _sockList.Listen(1);
                ChangeState(ConnectionState.Listening);
                _sockList.BeginAccept(OnClientConnect, null);
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                Close();
                ChangeState(ConnectionState.Error);
                HandleError?.Invoke(this, ex2.Message, ex2.TargetSite.Name, ex2.ToString());
                ProjectData.ClearProjectError();
            }
        }

        private void OnClientConnect(IAsyncResult asyn)
        {
            try
            {
                if (GetState == ConnectionState.Listening)
                {
                    Socket requestID = _sockList.EndAccept(asyn);
                    ConnectionRequest?.Invoke(this, requestID);
                    _sockList.BeginAccept(OnClientConnect, null);
                }
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                Close();
                ChangeState(ConnectionState.Error);
                HandleError?.Invoke(this, ex2.Message, ex2.TargetSite.Name, ex2.ToString());
                ProjectData.ClearProjectError();
            }
        }

        private void DoStreamReceive(IAsyncResult ar)
        {
            try
            {
                int num;
                lock (_Client)
                {
                    num = _Client.EndReceive(ar);
                }

                if (num < 1)
                {
                    Close();
                    _byteBuffer = new byte[1025];
                    Disconnected?.Invoke(this);
                    return;
                }

                AddToBuffer(_byteBuffer, num);
                Array.Clear(_byteBuffer, 0, num);
                lock (_Client)
                {
                    _Client.BeginReceive(_byteBuffer, 0, 1024, SocketFlags.None, DoStreamReceive, null);
                }
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                Close();
                _byteBuffer = new byte[1025];
                Disconnected?.Invoke(this);
                ProjectData.ClearProjectError();
            }
        }

        private void DoRead(IAsyncResult ar)
        {
            try
            {
                int num = _Client.EndReceive(ar);
                if (num < 1)
                {
                    Close();
                    _byteBuffer = new byte[1025];
                    Disconnected?.Invoke(this);
                }
                else
                {
                    AddToBuffer(_byteBuffer, num);
                    Array.Clear(_byteBuffer, 0, num);
                    _Client.BeginReceive(_byteBuffer, 0, 1024, SocketFlags.None, DoRead, null);
                }
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                Close();
                _byteBuffer = new byte[1025];
                Disconnected?.Invoke(this);
                ProjectData.ClearProjectError();
            }
        }

        private void BuildString(byte[] Bytes, int offset, int count)
        {
            checked
            {
                try
                {
                    int num = offset + count - 1;
                    int num2 = offset;
                    while (true)
                    {
                        int num3 = num2;
                        int num4 = num;
                        if (num3 > num4)
                        {
                            break;
                        }

                        if (Bytes[num2] == 10)
                        {
                            _sBuffer += "\n";
                        }
                        else
                        {
                            _sBuffer += Conversions.ToString(Strings.ChrW(Bytes[num2]));
                        }

                        num2++;
                    }

                    if (_sBuffer.IndexOf("\r\n") != -1)
                    {
                        DataArrival?.Invoke(this, count);
                        Array.Clear(_byteBuffer, 0, _byteBuffer.Length);
                    }
                }
                catch (Exception ex)
                {
                    ProjectData.SetProjectError(ex);
                    Exception ex2 = ex;
                    HandleError?.Invoke(this, ex2.Message, ex2.TargetSite.Name, ex2.ToString());
                    ProjectData.ClearProjectError();
                }
            }
        }

        private void AddToBuffer(byte[] bytes, int count)
        {
            int num = ((_buffer == null) ? (-1) : Information.UBound(_buffer));
            checked
            {
                int num2 = num + count;
                _buffer = (byte[])Utils.CopyArray(_buffer, new byte[num2 + 1]);
                Array.Copy(bytes, 0, _buffer, num + 1, count);
                byte value = 4;
                for (int num3 = Array.IndexOf(_buffer, value); num3 != -1; num3 = Array.IndexOf(_buffer, value))
                {
                    int num4 = _buffer.Length - (num3 + 1);
                    byte[] array = new byte[num3 - 1 + 1];
                    byte[] array2 = new byte[num4 - 1 + 1];
                    Array.Copy(_buffer, 0, array, 0, num3);
                    Array.Copy(_buffer, num3 + 1, array2, 0, num4);
                    _buffer = new byte[Information.UBound(array2) + 1];
                    Array.Copy(array2, _buffer, array2.Length);
                    _bufferCol.Add(array);
                    DataArrival?.Invoke(this, array.Length);
                }

                if ((count < bytes.Length - 1) & (_buffer.Length > 0))
                {
                    _bufferCol.Add(_buffer);
                    DataArrival?.Invoke(this, _buffer.Length);
                    _buffer = null;
                }
            }
        }

        public void ConnectPrinter()
        {
            if (registration.GetRegistered)
            {
                Connect();
                return;
            }

            Dispose();
            Interaction.MsgBox("License Key is invalid");
        }
        public void DisconnectPrinter()
        {
            if (registration.GetRegistered)
            {
                Close();
                Disconnected?.Invoke(this);
                return;
            }

            Dispose();
            Interaction.MsgBox("License Key is invalid");
        }

        #region KGK Cmd
        public bool StartPrinting()
        {
            return SendControlCommand("\u0002SRC:0:1:1:\u0003");
        }

        public bool StopPrinting()
        {
            return SendControlCommand("\u0002SRC:0:1:0:\u0003");
        }

        /// <summary>
        /// Choose message in at all messages
        /// </summary>
        /// <param name="nMessageNo"></param>
        /// <returns></returns>
        public bool SelectMessage(int nMessageNo)
        {
            string text = "\u0002SMN:0:1:" + nMessageNo + ":\u0003";
            return SendCommand(text, SendCommandType.Control);
        }
        /// <summary>
        /// Data return: 0:1:xx , where: xx is Message No
        /// </summary>
        /// <returns>0:1:xx</returns>
        public bool GetMessageCurrent()
        {
            return SendCommand("\u0002GMN:0:1:\u0003", SendCommandType.GetData);
        }
        public void UpdateTextModule(TextModuleParameters textModule)
        {

        }
        /// <summary>
        /// Update Text Module without change attributes it is
        /// </summary>
        /// <param name="content"></param>
        /// <returns></returns>
        public bool UpdateTextModuleNoChangeAttributes(string content, int nNoModule)
        {
            string text = "\u0002STM:1:" + nNoModule + "::3" + content + ":\u0003";
            return SendCommand(text, SendCommandType.Control);
        }

        public bool ResetPrintCounter(int nMessageNo)
        {
            string cmd = "\u0002RDP:0:1:" + nMessageNo + ":\u0003";
            return SendCommand(cmd, SendCommandType.Control);
        }

        private string GetPrintCounter()
        {
            string cmd = "\u0002GDP:0:1:" + m_nCurrentMessageNo + ":\u0003";
            string printerData = GetPrinterData(cmd);
            if (Versioned.IsNumeric(printerData))
            {
                return printerData;
            }

            return null;
        }

        /// <summary>
        /// Just get status of print head
        /// </summary>
        /// <returns>data return - 0:1:3:x: , where x is status of print head 
        /// <list>
        /// 0: Stopping, 
        /// 1: Stopping and the cover opens, 
        /// 2: Preparation of running, 
        /// 3: Preparation of running and the cover opens, 
        /// 4: Running, 
        /// 5: Preparation of stopping, 
        /// 6: While maintenance</list></returns>
        public bool GetMachineStatus()
        {
            return SendCommand("\u0002GSS:0:1:350124:\u0003", SendCommandType.CheckState); // head print -> head print heater -> ink tank -> solvent tank -> main tank -> visicosity
        }

        #endregion

        public bool StartJet()
        {
            return SendControlCommand("\u0002J\u0003");
        }
        public bool StopJet()
        {
            return SendControlCommand("\u0002K\u0003");
        }
        public bool ResetPrintCount()
        {
            return SendControlCommand("\u0002RA\u0003");
        }
        public bool ResetProductCount()
        {
            return SendControlCommand("\u0002RB\u0003");
        }
        public bool SelectMessage(string pMessageName)
        {
            if ((pMessageName.Length < 31) & (pMessageName.Length > 0))
            {
                return SendControlCommand("\u0002M" + pMessageName + "\u0003");
            }

            return false;
        }
        public bool DeleteMessageText()
        {
            return SendControlCommand("\u0002C\u0003");
        }
        public bool UpdateMessageText(MessageDataField[] pDataField)
        {
            if (pDataField.Count() > 0)
            {
                string text = "\u0002T";
                foreach (MessageDataField messageDataField in pDataField)
                {
                    if (!(Information.IsNothing(messageDataField.VERC) | Information.IsNothing(messageDataField.TextData)))
                    {
                        string fontCode = GetFontCode(messageDataField.Font);
                        string hORCCode = GetHORCCode(messageDataField.HORC);
                        string vERCCode = GetVERCCode(messageDataField.VERC);
                        if (Information.IsNothing(fontCode) | Information.IsNothing(hORCCode))
                        {
                            return false;
                        }

                        text = text + fontCode + hORCCode + vERCCode + _ATTRIB + messageDataField.TextData + "\n";
                        continue;
                    }

                    return false;
                }

                text = Strings.Left(text, checked(text.Length - 1));
                text += "\u0003";
                return SendControlCommand(text);
            }

            return false;
        }
        public bool UpdateMessage(MessageDataField[] pDataField)
        {
            checked
            {
                if (pDataField.Count() > 0)
                {
                    pDataField[0].HORC = 1;
                    pDataField[0].VERC = 34;
                    if (pDataField.Count() > 1)
                    {
                        int num = pDataField.Count() - 1;
                        int num2 = 1;
                        while (true)
                        {
                            int num3 = num2;
                            int num4 = num;
                            if (num3 > num4)
                            {
                                break;
                            }

                            pDataField[num2].HORC = 1;
                            if (pDataField[num2 - 1].VERC - 2 - pDataField[num2 - 1].Font < (FontType)0)
                            {
                                return false;
                            }

                            pDataField[num2].VERC = (byte)(pDataField[num2 - 1].VERC - 2 - pDataField[num2 - 1].Font);
                            num2++;
                        }
                    }

                    return UpdateMessageText(pDataField);
                }

                return false;
            }
        }
        public bool UpdateParameters(MessageParameters pParameter)
        {
            string booleanCode = GetBooleanCode(pParameter.Reverse);
            string booleanCode2 = GetBooleanCode(pParameter.Invert);
            string widthCode = GetWidthCode(pParameter.Width);
            string heightCode = GetHeightCode(pParameter.Height);
            string gapCode = GetGapCode(pParameter.Gap);
            string expireCode = GetExpireCode(pParameter.Expiry);
            string hejraCode = GetHejraCode(pParameter.Hejra);
            string delayCode = GetDelayCode(pParameter.Delay);
            string repeatCode = GetRepeatCode(pParameter.Repeat);
            string printedDotsCode = GetPrintedDotsCode(pParameter.PrintedDot);
            string booleanCode3 = GetBooleanCode(pParameter.RASSUB);
            string rLENCode = GetRLENCode(pParameter.RLEN);
            if (Information.IsNothing(widthCode) | Information.IsNothing(heightCode) | Information.IsNothing(gapCode) | Information.IsNothing(expireCode) | Information.IsNothing(hejraCode) | Information.IsNothing(delayCode) | Information.IsNothing(repeatCode) | Information.IsNothing(printedDotsCode) | Information.IsNothing(rLENCode))
            {
                return false;
            }

            string pCommand = "\u0002P" + booleanCode + booleanCode2 + widthCode + heightCode + gapCode + expireCode + hejraCode + delayCode + repeatCode + printedDotsCode + booleanCode3 + rLENCode + pParameter.Raster + "\u0003";
            return SendControlCommand(pCommand);
        }
        public bool ClearUserFieldData(string pUserFieldName)
        {
            return SendControlCommand("\u0002D" + pUserFieldName + "\u0003");
        }
        public bool UpdateCounterField(string pFieldName, string pStartValue, string pEndValue, byte pStep, Direction pDirection, byte pRepeat, string pPadding)
        {
            string pCommand = "\u0002U" + pFieldName + "\n" + pStartValue + "\n" + pEndValue + "\n" + Conversions.ToString(pStep) + "\n" + Conversions.ToString((int)pDirection) + "\n" + Conversions.ToString(pRepeat) + "\n" + pPadding + "\u0003";
            return SendControlCommand(pCommand);
        }
        public bool UpdateUserField(string pFieldName, string pUserData)
        {
            return SendControlCommand("\u0002U" + pFieldName + "\n" + pUserData + "\u0003");
        }
        public bool SetPrinterDateTime(DateTime pDate)
        {
            return SendControlCommand("\u0002Z" + pDate.ToString("yyMMddHHmmss") + "\u0003");
        }
        public string GetPrintCount()
        {
            string printerData = GetPrinterData("\u0002GA\u0003");
            if (Versioned.IsNumeric(printerData))
            {
                return printerData;
            }

            return null;
        }
        public string GetProductCount()
        {
            string printerData = GetPrinterData("\u0002GB\u0003");
            if (Versioned.IsNumeric(printerData))
            {
                return printerData;
            }

            return null;
        }
        public string GetCurrentSelectedMessageName()
        {
            return GetPrinterData("\u0002Q\u0003");
        }

        private void VideoJetPrinterW_Disposed(object sender, EventArgs e)
        {
            Close();
        }

        private void StartTimer3()
        {
            if (Information.IsNothing(Timer3))
            {
                iniTimer3();
            }

            Timer3.Start();
        }

        private bool SendCommand(string pCommand, SendCommandType pSendCommandType)
        {
            if (registration.GetRegistered)
            {
                if (GetState == ConnectionState.Connected && !_WaitingData)
                {
                    try
                    {
                        _WaitingData = true;
                        _IsDataArrival = false;
                        _SendCommandType = pSendCommandType;
                        Send(pCommand);
                        Timer3.Start();
                        return true;
                    }
                    catch (NullReferenceException ex)
                    {
                        ProjectData.SetProjectError(ex);
                        NullReferenceException ex2 = ex;
                        ProjectData.ClearProjectError();
                    }
                    catch (Exception ex3)
                    {
                        ProjectData.SetProjectError(ex3);
                        Exception ex4 = ex3;
                        ProjectData.ClearProjectError();
                    }
                }
            }
            else
            {
                Dispose();
                Interaction.MsgBox("License Key is invalid");
            }

            return false;
        }

        private bool SendControlCommand(string pCommand)
        {
            bool result;
            if (SendCommand(pCommand, SendCommandType.Control))
            {
                int num = 1;
                while (true)
                {
                    if (_IsDataArrival)
                    {
                        _IsDataArrival = false;
                        try
                        {
                            byte[] arrivalData = _ArrivalData;
                            result = arrivalData.Count() > 0 && arrivalData[0] == 6;
                        }
                        catch (Exception ex)
                        {
                            ProjectData.SetProjectError(ex);
                            Exception ex2 = ex;
                            result = false;
                            ProjectData.ClearProjectError();
                        }

                        break;
                    }

                    num = checked(num + 1);
                    int num2 = num;
                    int num3 = 10000000;
                    if (num2 > num3)
                    {
                        result = false;
                        break;
                    }
                }
            }
            else
            {
                result = false;
            }

            return result;
        }

        private void CheckPrinterState()
        {
            byte[] arrivalData = _ArrivalData;
            PrintHeadState prindHeadState = _PrintHeadState;
            if (arrivalData.Count() >= 26)
            {
                //byte[] bytes = new byte[1] { arrivalData[7] };
                //BitArray bitArray = new BitArray(bytes);
                //_PrinterState = PrinterState.NotPrinting;
                //if (bitArray[0])
                //{
                //    _PrinterState = PrinterState.Printing;
                //}
                //else if (bitArray[2])
                //{
                //    _PrinterState = PrinterState.Fault;
                //}

                //                                  13             15            17          19          21           23
                // example ACK: 6 2 0:1:350124:[PrintHead]:[PrintHeadHeater]:[InkTank]:[SolventTank]:[MainTank]:[Visicosity]:3
                // index 13: print head state
                char chPrintHead = Encoding.ASCII.GetChars(arrivalData)[13];
                switch (chPrintHead)
                {
                    case '0':
                        _PrintHeadState = PrintHeadState.Stopping;
                        break;
                    case '1':
                        _PrintHeadState = PrintHeadState.StoppingAndCoverOpen;
                        break;
                    case '2':
                        _PrintHeadState = PrintHeadState.PreparationOfRunning;
                        break;
                    case '3':
                        _PrintHeadState = PrintHeadState.PreparationOfRunningAndCoverOpen;
                        break;
                    case '4':
                        _PrintHeadState = PrintHeadState.Running;
                        break;
                    case '5':
                        _PrintHeadState = PrintHeadState.PreparationOfStopping;
                        break;
                    case '6':
                        _PrintHeadState = PrintHeadState.Maintenance;
                        break;
                }
                if (prindHeadState != _PrintHeadState)
                {
                    //InvokeMethod(OnPrinterStateChanged);
                    PrinterStateChanged?.Invoke(this, _PrintHeadState, _PrintHeadHeaterState,
                        _LiquidQuantityInkTankState, _LiquidQuantitySolventTankState, _LiquidQuantityMainTankState, _VisicosityState);
                    
                    //PrinterStateChangedHandle(); tam thoi tat timer get print count
                }
            }
        }
        private void CheckLiquidQuantityState()
        {

        }
        private void CheckPrintHeadHeaterStateAndViscosity()
        {

        }

        private string GetArrivalData()
        {
            int num = 1;
            checked
            {
                string result;
                while (true)
                {
                    if (_IsDataArrival)
                    {
                        _IsDataArrival = false;
                        try
                        {
                            byte[] arrivalData = _ArrivalData;
                            byte[] array = new byte[arrivalData.Length - 10]; // sub 10 byte format, the byte remain is indicator for print count
                            Array.Copy(arrivalData, 8, array, 0, arrivalData.Length - 10);
                            _PrinterArrivalData = ASCIIBytesToString(array);
                            result = _PrinterArrivalData;
                        }
                        catch (Exception ex)
                        {
                            ProjectData.SetProjectError(ex);
                            Exception ex2 = ex;
                            Interaction.MsgBox("Get arrival data Error");
                            result = null;
                            ProjectData.ClearProjectError();
                        }

                        break;
                    }

                    num++;
                    int num2 = num;
                    int num3 = 1000000000;
                    if (num2 > num3)
                    {
                        result = null;
                        break;
                    }
                }

                return result;
            }
        }

        private string GetPrinterData(string pCommand)
        {
            if (SendCommand(pCommand, SendCommandType.GetData))
            {
                return GetArrivalData();
            }

            return null;
        }

        private string BytesToString(byte[] Input)
        {
            StringBuilder stringBuilder = new StringBuilder(checked(Input.Length * 2));
            foreach (byte number in Input)
            {
                string text = Conversion.Hex(number);
                if (text.Length == 1)
                {
                    text = "0" + text;
                }

                stringBuilder.Append(text);
            }

            return stringBuilder.ToString();
        }

        private string ASCIIBytesToString(byte[] bytes)
        {
            return Encoding.ASCII.GetString(bytes);
        }

        private void StopTimer3()
        {
            if (Timer3 == null)
            {
                iniTimer3();
            }

            Timer3.Stop();
        }

        private void ProcessDataArrival(KGKJetPrinter sender, int BytesTotal)
        {
            Timer3.Stop();
            GetData(ref _ArrivalData);
            switch ((int)_SendCommandType)
            {
                case 0:
                    CheckPrinterState();
                    break;
                case 2:
                    _IsDataArrival = true;
                    break;
                default:
                    _IsDataArrival = true;
                    break;
            }

            _WaitingData = false;
        }

        private void CheckConnectionState(KGKJetPrinter sender, ConnectionState state)
        {
            //InvokeAction(OnConnectionStateChanged, sender);
            ConnectionStateChanged?.Invoke(sender, _State);
        }

        private void OnConnectionStateChanged(KGKJetPrinter sender)
        {
            ConnectionStateChanged?.Invoke(sender, _State);
        }

        private void OnPrinterStateChanged()
        {
            PrinterStateChanged?.Invoke(this, _PrintHeadState, _PrintHeadHeaterState,
                        _LiquidQuantityInkTankState, _LiquidQuantitySolventTankState, _LiquidQuantityMainTankState, _VisicosityState);
        }

        private string GetFontCode(FontType pFont)
        {
            switch ((int)pFont)
            {
                case 7: return "00";
                case 9:
                    return "01";
                case 12:
                    return "02";
                case 16:
                    return "03";
                case 24:
                    return "04";
                case 34:
                    return "05";
                case 5:
                    return "06";
                default:
                    return null;
            };
        }

        private string Get5CharCode(int pValue)
        {
            string text = Convert.ToString(pValue);
            switch (text.Length)
            {
                case 1:
                    text = "0000" + text;
                    break;
                case 2:
                    text = "000" + text;
                    break;
                case 3:
                    text = "00" + text;
                    break;
                case 4:
                    text = "0" + text;
                    break;
            }

            return text;
        }

        private string Get4CharCode(ushort pValue)
        {
            string text = Convert.ToString(pValue);
            switch (text.Length)
            {
                case 1:
                    text = "000" + text;
                    break;
                case 2:
                    text = "00" + text;
                    break;
                case 3:
                    text = "0" + text;
                    break;
            }

            return text;
        }

        private string Get3CharCode(ushort pValue)
        {
            string text = Convert.ToString(pValue);
            switch (text.Length)
            {
                case 1:
                    text = "00" + text;
                    break;
                case 2:
                    text = "0" + text;
                    break;
            }

            return text;
        }

        private string Get2CharCode(byte pValue)
        {
            string text = Convert.ToString(pValue);
            int length = text.Length;
            if (length == 1)
            {
                text = "0" + text;
            }

            return text;
        }

        private string GetHORCCode(int pHORC)
        {
            if (pHORC < 1000)
            {
                return Get4CharCode(checked((ushort)pHORC));
            }

            return null;
        }

        private string GetVERCCode(byte pVerc)
        {
            return Get3CharCode(pVerc);
        }

        private string GetBooleanCode(bool pValue)
        {
            if (pValue)
            {
                return "1";
            }

            return "0";
        }

        private string GetWidthCode(int pWidth)
        {
            if (pWidth < 3937)
            {
                return Get4CharCode(checked((ushort)pWidth));
            }

            return null;
        }

        private string GetHeightCode(int pHeight)
        {
            if (pHeight < 11)
            {
                return Get2CharCode(checked((byte)pHeight));
            }

            return null;
        }

        private string GetGapCode(byte pGap)
        {
            if (pGap < 10)
            {
                return Convert.ToString(pGap);
            }

            return null;
        }

        private string GetExpireCode(ushort pExpire)
        {
            if (pExpire < 32768)
            {
                return Get5CharCode(pExpire);
            }

            return null;
        }

        private string GetHejraCode(ushort pExpire)
        {
            if (pExpire < 32768)
            {
                return Get5CharCode(pExpire);
            }

            return null;
        }

        private string GetDelayCode(ushort pDelay)
        {
            if (pDelay < 10000)
            {
                return Get5CharCode(pDelay);
            }

            return null;
        }

        private string GetRepeatCode(byte pRepeat)
        {
            if (pRepeat < 11)
            {
                return Get2CharCode(pRepeat);
            }

            return null;
        }

        private string GetPrintedDotsCode(byte pValue)
        {
            if (pValue < 35)
            {
                return Get2CharCode(pValue);
            }

            return null;
        }

        private string GetRLENCode(ushort pValue)
        {
            if (pValue < 256)
            {
                return Get3CharCode(pValue);
            }

            return null;
        }

        /// <summary>
        /// Invoke Window Form
        /// </summary>
        /// <typeparam name="T"></typeparam>
        /// <param name="anAction"></param>
        /// <param name="Arg"></param>
        /// <param name="ThrowMainFormMissingError"></param>
        private void InvokeAction<T>(Action<T> anAction, T Arg, bool ThrowMainFormMissingError = true)
        {
            try
            {
                if ((ThrowMainFormMissingError || Application.OpenForms.Count != 0) && 0 == 0)
                {
                    Form form = Application.OpenForms[0];
                    if (form.InvokeRequired)
                    {
                        form.Invoke(anAction, Arg);
                    }
                    else
                    {
                        anAction(Arg);
                    }

                    form = null;
                }
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                ProjectData.ClearProjectError();
            }
        }
        /// <summary>
        /// Invoke Wpf
        /// </summary>
        /// <typeparam name="T"></typeparam>
        /// <param name="anAction"></param>
        /// <param name="Arg"></param>
        private void InvokeAction<T>(Action<T> anAction, T Arg)
        {
            try
            {
                if (System.Windows.Application.Current.Windows.Count != 0 && 0 == 0)
                {
                    var form = System.Windows.Application.Current.Windows[0];
                    if (form.Dispatcher.CheckAccess())
                    {
                        form.Dispatcher.Invoke(anAction, Arg);
                    }
                    else
                    {
                        anAction(Arg);
                    }

                    form = null;
                }
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                ProjectData.ClearProjectError();
            }
        }

        /// <summary>
        /// Invoke Method Winform
        /// </summary>
        /// <param name="aMethod"></param>
        /// <param name="ThrowMainFormMissingError"></param>
        private void InvokeMethod(MethodInvoker aMethod, bool ThrowMainFormMissingError = true)
        {
            try
            {
                if ((ThrowMainFormMissingError || Application.OpenForms.Count != 0) && 0 == 0)
                {
                    Form form = Application.OpenForms[0];
                    if (form.InvokeRequired)
                    {
                        form.Invoke(aMethod);
                    }
                    else
                    {
                        aMethod();
                    }

                    form = null;
                }
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                ProjectData.ClearProjectError();
            }
        }

        /// <summary>
        /// Invoke Method WPF
        /// </summary>
        /// <param name="aMethod"></param>
        private void InvokeMethod(MethodInvoker aMethod)
        {
            try
            {
                if (System.Windows.Application.Current.Windows.Count != 0 && 0 == 0)
                {
                    var form = System.Windows.Application.Current.Windows[0];
                    if (form.Dispatcher.CheckAccess())
                    {
                        form.Dispatcher.Invoke(aMethod);
                    }
                    else
                    {
                        aMethod();
                    }

                    form = null;
                }
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                ProjectData.ClearProjectError();
            }
        }

        private void startTimer()
        {
            try
            {
                if (Timer1 == null)
                {
                    iniTimer1();
                }

                if (Timer2 == null)
                {
                    iniTimer2();
                }

                Timer1.Start();
                Timer2.Stop();
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                Interaction.MsgBox("Start timer error");
                ProjectData.ClearProjectError();
            }
        }

        private void stopTimer()
        {
            try
            {
                if (Timer1 == null)
                {
                    iniTimer1();
                }

                if (Timer2 == null)
                {
                    iniTimer2();
                }

                Timer1.Stop();
                if (m_bAutoReconnect)
                    Timer2.Start();
                _WaitingData = false;
                _SendCommandType = SendCommandType.Control;
                _PrintHeadState = PrintHeadState.Unknown;
                _PrintHeadHeaterState = PrintHeadHeaterState.Unknown;
                _LiquidQuantityInkTankState = LiquidQuantity.Unknown;
                _LiquidQuantitySolventTankState = LiquidQuantity.Unknown;
                _LiquidQuantityMainTankState = LiquidQuantity.Unknown;
                _VisicosityState = VisicosityState.Unknown;
                //InvokeMethod(OnPrinterStateChanged);
                PrinterStateChanged?.Invoke(this, _PrintHeadState, _PrintHeadHeaterState,
                        _LiquidQuantityInkTankState, _LiquidQuantitySolventTankState, _LiquidQuantityMainTankState, _VisicosityState);
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                Interaction.MsgBox("Stop timer error");
                ProjectData.ClearProjectError();
            }
        }

        private void iniTimer1()
        {
            Timer1 = new System.Timers.Timer(1000.0);
            Timer1.Elapsed += OnTimedEvent1;
            Timer1.AutoReset = true;
        }

        private void iniTimer2()
        {
            Timer2 = new System.Timers.Timer(5000.0);
            Timer2.Elapsed += OnTimedEvent2;
            Timer2.AutoReset = true;
        }

        private void iniTimer3()
        {
            Timer3 = new System.Timers.Timer(6000.0);
            Timer3.Elapsed += OnTimedEvent3;
            Timer3.AutoReset = true;
        }

        private void SetTimer()
        {
            iniTimer1();
            Timer1.Enabled = false;
            iniTimer2();
            Timer2.Enabled = false;
            iniTimer3();
            Timer3.Enabled = false;
            CheckFinishPrintTimer = new System.Timers.Timer(500.0);
            CheckFinishPrintTimer.Elapsed += OnTimedEventCheckFinishPrintTimer;
            CheckFinishPrintTimer.AutoReset = true;
            CheckFinishPrintTimer.Enabled = false;
            Connected += (KGKJetPrinter a0) =>
            {
                startTimer();
            };
            Disconnected += (KGKJetPrinter a0) =>
            {
                stopTimer();
            };
            HandleError += (KGKJetPrinter a0, string a1, string a2, string a3) =>
            {
                stopTimer();
            };
        }

        private void OnTimedEvent1(object source, ElapsedEventArgs e)
        {
            GetMachineStatus();
        }

        private void OnTimedEvent2(object source, ElapsedEventArgs e)
        {
            if ((GetState == ConnectionState.Closed) | (GetState == ConnectionState.Error))
            {
                ConnectPrinter();
            }
        }

        private void OnTimedEvent3(object source, ElapsedEventArgs e)
        {
            Timer3.Stop();
            _SendCommandType = SendCommandType.Control;
            _WaitingData = false;
        }

        private void OnTimedEventCheckFinishPrintTimer(object source, ElapsedEventArgs e)
        {
            try
            {
                string printCount = GetPrintCounter();
                if (!Information.IsNothing(printCount))
                {
                    uint num = Conversions.ToUInteger(printCount);
                    if (num > _LastPrintCount)
                    {
                        _diff = checked((int)(num - _LastPrintCount));
                        //InvokeMethod(OnPrintCompleted);
                        //MessagePrintCompleted?.Invoke(this);
                        _LastPrintCount = num;
                        PrintCountChanged?.Invoke(this);
                        return;
                    }

                    _LastPrintCount = num;
                }
            }
            catch (Exception ex)
            {
                ProjectData.SetProjectError(ex);
                Exception ex2 = ex;
                Interaction.MsgBox("On complete printing event error");
                ProjectData.ClearProjectError();
            }
        }

        private void PrinterStateChangedHandle()
        {
            if (_PrintHeadState == PrintHeadState.Running)
            {
                CheckFinishPrintTimer.Start();
            }
            else
            {
                CheckFinishPrintTimer.Stop();
            }
        }

        private void OnPrintCompleted()
        {
            MessagePrintCompleted?.Invoke(this);
        }
        #endregion

        public class TextModuleParameters
        {
            public string CommandVersion; // 1 fixed
            public string ModuleNo; // 1 ~ 500: No. 1 ~ 500, D: Default data
            public string VerticalDots; // 1: 5dots, 2: 7dots, 3: 9dots, 4: 10dots, 5: 12dots, 6: 16dots, 7: 20dots, 8: 22dots, 9: 24dots, A: 26dots, E: 11 dots, F: 15 dots
            public string FontSize; // 2: 24x24, 3: 24x18, 4: 16x16, 5: 16x12, 6: 12x10, 7: 10x8, 8: 9x9, 9: 9x7, A: 7x8, B: 7x5, C: 5x5, D: 5xN, E: 7xN
            public string FontBottomPos; // 00 ~ 25: The font bottom is located at the 0th ~ 25th dot from the lowermost dot
            public string MultiWidth; // 1 ~ 8: 1 ~ 8-fold
            public string CharDirection; // 0: ↑, 1: ←, 2: →, 3: ↓
            public string CharSpacingDot; // 00 ~ 31: 0 ~ 31 dots
            public string CharSpacingOfFinalChar; // 0: Disabled, 1: Enabled
            public string FullWidthToCharSpacingDot; // 0: Disabled, 1: Enabled
            public string Reverse; // 0: Disabled, 1: Enabled
            public string CharInversion; // 0: Disabled, 1: Horizontal inversion, 2: Vertical inversion
            public string CharPlacement; // 0: Places the character left to right, 1: Right to left, 2: Top to bottom, 3: Bottom to top
            public string CodeSystem; // 0: JIS, 1: ASCII, 2: Shift-JIS, 3: ASCII + Shift-JIS, 4: UNICODE, 6: GB, 7: ASCII + GB, 8: KS, 9: ASCII + KS, A: BIG5, B: ASCII + BIG5
            public string Content;

            public TextModuleParameters()
            {
                CommandVersion = "1";
                ModuleNo = "1";
                VerticalDots = "A";
                FontSize = "2";
                FontBottomPos = "00";
                MultiWidth = "1";
                CharDirection = "0";
                CharSpacingDot = "00";
                CharSpacingOfFinalChar = "0";
                FullWidthToCharSpacingDot = "1";
                Reverse = "0";
                CharInversion = "0";
                CharPlacement = "0";
                CodeSystem = "3";
                Content = "";

            }
        }
        public class MessageParameters
        {
            public bool Reverse;

            public bool Invert;

            public ushort Width;

            public byte Height;

            public byte Gap;

            public ushort Expiry;

            public ushort Hejra;

            public ushort Delay;

            public byte Repeat;

            public byte PrintedDot;

            public bool RASSUB;

            public ushort RLEN;

            public string Raster;

            public MessageParameters()
            {
                Reverse = true;
                Invert = false;
                Width = 100;
                Height = 6;
                Gap = 1;
                Expiry = 0;
                Hejra = 0;
                Delay = 10;
                Repeat = 2;
                PrintedDot = 24;
                RASSUB = true;
                RLEN = 7;
                Raster = "16-high";
            }
        }
        public class MessageDataField
        {
            public FontType Font;

            public int HORC;

            public byte VERC;

            public string TextData;

            public MessageDataField()
            {
                Font = FontType.hi7;
                HORC = 1;
                VERC = 34;
            }
        }
        public class PrinterStatus
        {

        }
    }
}
