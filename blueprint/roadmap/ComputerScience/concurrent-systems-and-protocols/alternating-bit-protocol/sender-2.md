# Sender states of the alternating-bit protocol with data

For bits $b$ and $d$, a sender
state is $\mathsf{accept}(b)$, ready to accept a message to be sent with sequence bit $b$;
$\mathsf{transmit}(b, d)$, about to transmit the data bit $d$ with sequence bit $b$; or
$\mathsf{await}(b, d)$, waiting for the acknowledgement of $b$ while holding $d$ for
retransmission.
