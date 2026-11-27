# Padded blocks of a message

Write $\langle c \rangle_w$ for the $w$-bit little-endian encoding of $c \in \mathbb{N}$: its $i$-th bit ($0 \le i < w$) is $\lfloor c / 2^i \rfloor \bmod 2$, so only the low $w$ bits of $c$ are kept and decoding returns $c \bmod 2^w$. For a block length $n$ and a length-field width $L$, put $z(\ell) = (n - (\ell + 1 + L) \bmod n) \bmod n$ (in natural-number arithmetic; for $n > 0$ this is the least $k$ with $n \mid \ell + 1 + k + L$, and for $n = 0$ it is $0$). The strengthened padding of a bit string $M$ is

$$
\mathrm{pad}_{n,L}(M) = M \,\|\, 1 \,\|\, 0^{z(|M|)} \,\|\, \langle |M| \rangle_L ,
$$

and the padded blocks of $M$ are the [$n$-bit blocks](blocks.md) of $\mathrm{pad}_{n,L}(M)$. For $n > 0$ the padded length is a multiple of $n$, so no bit is dropped; for $n = 0$ the list is empty. The length field records $|M| \bmod 2^L$, which is $|M|$ only when $|M| < 2^L$.

Katz and Lindell's Construction 5.3 instead zero-pads and appends $|M|$ as a separate block.
