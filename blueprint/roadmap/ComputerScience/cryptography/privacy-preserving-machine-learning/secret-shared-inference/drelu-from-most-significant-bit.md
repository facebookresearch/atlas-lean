# Sign bit of an additively shared ring element from a carry

For $\ell\ge2$ and $a\equiv a_0+a_1\pmod{2^\ell}$ with each share written $a_b=\mathrm{msb}_b\|x_b$, $\mathrm{MSB}(a)=\mathrm{msb}_0\oplus\mathrm{msb}_1\oplus\mathrm{carry}$, where $\mathrm{carry}=\mathbf 1\{x_0+x_1>2^{\ell-1}-1\}=\mathbf 1\{2^{\ell-1}-1-x_0<x_1\}$; hence $\mathrm{DReLU}(a)=1\oplus\mathrm{msb}_0\oplus\mathrm{msb}_1\oplus\mathrm{carry}$.

Here $\mathrm{msb}_b\in\{0,1\}$ is the top bit of the share and $x_b\in[0,2^{\ell-1})$ its lower $\ell-1$ bits. In two's complement $\mathrm{DReLU}(a)=1$ if $a\ge0$ (so $\mathrm{DReLU}(0)=1$) and $0$ otherwise, i.e. $\mathrm{DReLU}(a)=1\oplus\mathrm{MSB}(a)$. The carry is a comparison of the private values $2^{\ell-1}-1-x_0$ and $x_1$, so CrypTFlow2's Algorithm 2 computes Boolean shares of $\mathrm{DReLU}(a)$ with one $(\ell-1)$-bit [millionaires' comparison](block-recursive-millionaires-protocol.md), party $b$ outputting $\mathrm{msb}_b\oplus\langle\mathrm{carry}\rangle_b\oplus b$.

## Depends on

None.

## Proof depends on

None.

## Expansion

The top bit of $a_0+a_1$ is the XOR of the two top bits and the carry out of the lower $\ell-1$ bits, which is $1$ exactly when $x_0+x_1\ge2^{\ell-1}$. Algorithm 2 as a protocol, and ReLU from DReLU by a separate multiplexer, are further pages.

## Sources

- Deevashwer Rathee, Mayank Rathee, Nishant Kumar, Nishanth Chandran, Divya Gupta, Aseem Rastogi, Rahul Sharma, "CrypTFlow2: Practical 2-Party Secure Inference", ACM CCS 2020, DOI 10.1145/3372297.3417274; numbers and equations from the author-deposited arXiv:2010.06457v1: rendered p. 6, §3.2 and Algorithm 2.
