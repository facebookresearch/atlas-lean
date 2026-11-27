# Number of padding zeros

For a block length $B > 0$ and a length-field width $L$, the padding of a message of length $m$ uses
$(B - (m + 1 + L) \bmod B) \bmod B$ zero bits: the least $k$ with $B \mid m + 1 + k + L$. For $B = 0$
the number of zero bits is taken to be $0$.
