# All-zero payloads yield the zero final CRC register

For every register width $r \in \mathbb{N}$, every width-$r$ taps word $g$, and every declared payload length $\ell \in \mathbb{N}$, feeding the all-zero payload $0^\ell$ produces the zero polynomial in the final register:

$$P_{\mathrm{final}_{r, g}(0^\ell)} = 0.$$
