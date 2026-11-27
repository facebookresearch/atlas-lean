# Reconstruction and uniqueness of the ML-DSA decompositions

For every $r \in \mathbb{Z}_q$: $r \equiv r_1 2^d + r_0$ for the outputs of Power2Round, and $r \equiv \mathrm{HighBits}(r)\cdot 2\gamma_2 + \mathrm{LowBits}(r) \pmod q$ with $|\mathrm{LowBits}(r)| \le \gamma_2$. Decompose is the unique such representation: if $r \equiv a\cdot 2\gamma_2 + b$ with $0 \le a < (q-1)/(2\gamma_2)$ and $-\gamma_2 < b \le \gamma_2$, then $(\mathrm{HighBits}(r), \mathrm{LowBits}(r)) = (a, b)$. Consequently, if $\|\mathrm{LowBits}(r)\|_\infty < \gamma_2 - \beta$ and $\|s\|_\infty \le \beta$, then $\mathrm{HighBits}(r + s) = \mathrm{HighBits}(r)$.

## Proof sketch

Reconstruction is immediate from the definition (the boundary case shifts by $q - 1 + 1 \equiv 0$). Uniqueness holds because the intervals for $b$ have length exactly $2\gamma_2$ and the values of $a$ cover $[0, q-1)$ without overlap.

## Depends on

- [Power2Round, Decompose, HighBits and LowBits](ml-dsa-decompositions.md)

## Sources

- Léo Ducas et al., "CRYSTALS-Dilithium: A Lattice-Based Digital Signature Scheme", IACR Transactions on Cryptographic Hardware and Embedded Systems, 2018.
- National Institute of Standards and Technology, "Module-Lattice-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
