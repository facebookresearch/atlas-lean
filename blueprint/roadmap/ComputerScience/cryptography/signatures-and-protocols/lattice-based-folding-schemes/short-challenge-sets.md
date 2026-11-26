# Strong sampling sets of short challenges in power-of-two cyclotomic rings

Let $d$ be a power of two, $R=\mathbb{Z}[X]/(X^{d}+1)$ and $R_q=R/qR$. For $a\in R$ let $\|a\|_\infty$ be the maximum absolute value of its centered coefficients and $\|a\|_{\mathrm{op}}=\sup_{b\ne 0}\|ab\|_\infty/\|b\|_\infty$ its operator norm. A finite set $\mathcal{C}\subseteq R_q$ is a *strong sampling set* if the difference of any two distinct elements of $\mathcal{C}$ is invertible in $R_q$. Lattice-based folding draws its challenges $r$ from such a set with $\max_{c\in\mathcal{C}}\|c\|_{\mathrm{op}}$ small, so that $\|w_1+rw_2\|_\infty\le\|w_1\|_\infty+\|r\|_{\mathrm{op}}\|w_2\|_\infty$ stays bounded, while invertibility of differences enables extraction from two transcripts.

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems", ASIACRYPT (2025), IACR ePrint 2024/257.
- Vadim Lyubashevsky, Gregor Seiler, "Short, Invertible Elements in Partially Splitting Cyclotomic Rings and Applications to Lattice-Based Zero-Knowledge Proofs", EUROCRYPT (2018).
