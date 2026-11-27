# Power2Round, Decompose, HighBits and LowBits

Let $q$ be an odd prime and $r \in \mathbb{Z}_q$ with canonical representative $r^+ \in [0, q)$. *Power2Round* with parameter $d$ writes $r^+ = r_1 2^d + r_0$ with $r_0 \in (-2^{d-1}, 2^{d-1}]$. For an even divisor $\alpha = 2\gamma_2$ of $q - 1$ with $q > 2\alpha$ (equivalently $m = (q-1)/\alpha \ge 2$; the ML-DSA parameter sets have $m \in \{16, 44\}$), *Decompose* writes $r^+ = r_1 \alpha + r_0$ with $r_0 \in (-\gamma_2, \gamma_2]$, except that when $r^+ - r_0 = q - 1$ it sets $r_1 = 0$ and $r_0 \leftarrow r_0 - 1$; then $\mathrm{HighBits}(r) = r_1 \in [0, (q-1)/\alpha)$ and $\mathrm{LowBits}(r) = r_0$. Both maps act coefficientwise on polynomials and vectors over $R_q$.

## Sources

- Léo Ducas et al., "CRYSTALS-Dilithium: A Lattice-Based Digital Signature Scheme", IACR Transactions on Cryptographic Hardware and Embedded Systems, 2018.
- National Institute of Standards and Technology, "Module-Lattice-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
