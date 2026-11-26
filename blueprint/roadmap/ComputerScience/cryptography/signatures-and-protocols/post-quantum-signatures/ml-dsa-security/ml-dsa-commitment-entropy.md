# Min-entropy of ML-DSA signing commitments

Fix the public matrix $\mathbf{A} \in R_q^{k\times\ell}$ and let the mask $\mathbf{y}$ be uniform with coefficients in $(-\gamma_1, \gamma_1]$. The largest probability of any value of the rounded commitment $\mathbf{w}_1 = \mathrm{HighBits}(\mathbf{A}\mathbf{y})$ is at most the number of masks in the box that map to one product of rounding buckets, divided by $(2\gamma_1)^{\ell n}$; this count is at most the size of the kernel (within the box of mask differences) of the square submatrix formed by the first $\ell$ rows of $\mathbf{A}$ times the number of points of $R_q^{\ell}$ in one product of buckets, i.e. at most $|\ker| \cdot (2\gamma_2 + 1)^{\ell n}$-many masks per commitment value. Averaged over a uniform $\mathbf{A}$, for which the square submatrix is invertible except with small probability, this is negligible for the standard parameter sets. Every individual mask has probability exactly $(2\gamma_1)^{-\ell n}$. This bounds the probability that a fresh signing commitment collides with a previously queried random-oracle input, which is the cost of programming the challenge hash during signing simulation.

## Proof sketch

Masks producing the same $\mathbf{w}_1$ have images under the first $\ell$ rows lying in a common product of rounding buckets; two masks with the same image differ by a kernel vector, so each bucket product has at most (kernel size) times (bucket volume) preimages in the box.

## Depends on

- [The ML-DSA signature scheme](../ml-dsa-signatures/ml-dsa-scheme.md)
- [Power2Round, Decompose, HighBits and LowBits](../ml-dsa-signatures/ml-dsa-decompositions.md)

## Sources

- Manuel Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium", Cryptology ePrint Archive, Paper 2023/246, 2023.
- Pouria Fallahpour, Serge Fehr and Yu-Hsuan Huang, "Tighter Quantum Security for Fiat-Shamir-with-Aborts and Hash-and-Sign-with-Retry Signatures", Cryptology ePrint Archive, Paper 2025/985, 2025.
