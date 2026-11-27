# Padding behind a prefix

For a block length $n$, a length-field width $L$, an offset $\mathrm{off} \in \mathbb{N}$ and a bit string $m$, write $\langle c \rangle_L$ for the $L$-bit little-endian encoding of $c$, which keeps only $c \bmod 2^L$ and $z(\ell) = (n - (\ell + 1 + L) \bmod n) \bmod n$ (the least $k$ with $n \mid \ell + 1 + k + L$ when $n > 0$, and $0$ when $n = 0$). The padding of $m$ behind an $\mathrm{off}$-bit prefix is

$$
m \,\|\, 1 \,\|\, 0^{z(\mathrm{off} + |m|)} \,\|\, \langle \mathrm{off} + |m| \rangle_L ,
$$

the tail that the strengthened padding appends after a prefix of length $\mathrm{off}$: its zeros and its length field are computed for the total length $\mathrm{off} + |m|$.
