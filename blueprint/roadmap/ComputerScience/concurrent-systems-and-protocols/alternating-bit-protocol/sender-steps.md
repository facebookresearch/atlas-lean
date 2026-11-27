# Alternating-bit sender transitions

The sender of the alternating-bit protocol has the
following transitions. Ready to accept with bit $b$, it can input on $\mathit{acc}$ and become
about to transmit $b$. About to transmit $b$, it can output on $\mathit{send}_b$ and then await
the acknowledgement of $b$. Awaiting the acknowledgement of $b$, it can input on
$\mathit{ack}_b$ and become ready to accept with bit $\lnot b$, input on
$\mathit{ack}_{\lnot b}$ and keep waiting, or time out by a silent step and become about to
transmit $b$ again.
