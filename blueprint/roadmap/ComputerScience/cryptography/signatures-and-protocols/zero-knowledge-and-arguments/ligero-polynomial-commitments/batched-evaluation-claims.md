# Random linear combination batching of evaluation claims

Let $p_1, \dots, p_k$ be committed polynomials over $\mathbb{F}$ with claimed evaluations $p_i(z) = y_i$ at a common point. The verifier sends a uniform $r \in \mathbb{F}$ and the claim is reduced to the single claim $\bigl(\sum_i r^{i-1} p_i\bigr)(z) = \sum_i r^{i-1} y_i$ (or with independent uniform coefficients $r_i$, to $\sum_i r_i p_i(z) = \sum_i r_i y_i$). The reduction is perfectly complete, and it is round-by-round sound: if some claim is false, the batched claim holds with probability at most $(k-1)/|\mathbb{F}|$ for powers of $r$, and at most $1/|\mathbb{F}|$ with independent coefficients.

## Proof sketch

The difference $\sum_i r^{i-1} (p_i(z) - y_i)$ is a nonzero polynomial in $r$ of degree at most $k - 1$ (respectively a nonzero linear form in independent coefficients).

## Depends on

- [Polynomial commitment schemes](../polynomial-commitment-schemes.md)

## Sources

- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
