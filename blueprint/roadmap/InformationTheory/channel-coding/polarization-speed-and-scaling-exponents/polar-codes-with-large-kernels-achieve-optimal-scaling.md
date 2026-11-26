# Fazeli-Hassani-Mondelli-Vardy: large kernels achieve the optimal scaling exponent on the erasure channel

For the binary erasure channel and every $\delta > 0$ there exist binary $\ell \times \ell$ polarization kernels (for large $\ell$, chosen randomly among kernels containing a suitable fixed structure) such that the corresponding polar codes achieve scaling exponent at most $2 + \delta$, with encoding and successive cancellation decoding complexity $O_\ell(N \log N)$.

## Proof sketch

For erasure channels the erasure probabilities of synthesized subchannels evolve by explicit polynomials determined by the kernel. Random kernels with dense rows behave like random linear codes on the erasure channel, so the fraction of unpolarized subchannels after one kernel step shrinks by a factor $\ell^{-1/2 + o(1)}$; iterating gives gap to capacity $N^{-1/2 + o(1)}$.

## Depends on

- [Scaling exponent of polar codes](scaling-exponent-of-a-code-family.md)
- [Polar codes and successive cancellation decoding](polar-codes-and-successive-cancellation-decoding.md)

## Proof depends on

- [Hassani-Alishahi-Urbanke and Mondelli-Hassani-Urbanke: bounds on the polar scaling exponent](finite-length-scaling-bounds-for-polar-codes.md)

## Sources

- Arman Fazeli, S. Hamed Hassani, Marco Mondelli, Alexander Vardy, "Binary linear codes with optimal scaling: polar codes with large kernels", IEEE Transactions on Information Theory 67(9) (2021); arXiv:1711.01339.
