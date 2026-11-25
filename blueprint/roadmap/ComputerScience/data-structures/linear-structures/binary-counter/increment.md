# Binary counter increment

A $k$-bit counter is a vector $b = (b_0, \dots, b_{k-1})$ of bits
stored lowest bit first. Incrementing $b$ changes the initial run of $1$ bits $b_0, \dots, b_{t-1}$
to $0$ and then changes the first $0$ bit $b_t$, if there is one, to $1$; if every bit is $1$, all
bits become $0$ and no new bit is added. The result is again a $k$-bit counter, and the cost of
the increment is the number of bits changed, one unit per changed bit.
