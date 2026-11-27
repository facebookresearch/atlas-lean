# Rounding error of CKKS encoding

For every $\mathbf{z}\in\mathbb{C}^{N/2}$ such that $\Delta\tau^{-1}(\mathbf{z})$ has real coefficients, $\|\mathrm{Dcd}(\mathrm{Ecd}(\mathbf{z}))-\mathbf{z}\|_\infty\le N/(2\Delta)$. Moreover, for any $m,m'\in R$, the slotwise product of decodings satisfies $\mathrm{Dcd}(mm')=\Delta\cdot\mathrm{Dcd}(m)\odot\mathrm{Dcd}(m')$, so ring multiplication implements slotwise complex multiplication with a doubling of the scale.

## Proof sketch

The rounding error $r=\mathrm{Ecd}(\mathbf{z})-\Delta\tau^{-1}(\mathbf{z})$ has coefficients of absolute value at most $1/2$, so $\|\tau(r)\|_\infty\le\|r\|_1\le N/2$, and dividing by $\Delta$ gives the bound. Multiplicativity follows because $\tau$ is a ring homomorphism (evaluation at roots).

## Depends on

- [CKKS encoding via the canonical embedding](canonical-embedding-encoding.md)

## Sources

- Jung Hee Cheon, Andrey Kim, Miran Kim, Yongsoo Song, "Homomorphic Encryption for Arithmetic of Approximate Numbers", ASIACRYPT (2017), IACR ePrint 2016/421.
