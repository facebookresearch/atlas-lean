---
article_id: af_92a1299c3b29d64cf740e006
declaration: structure
origin: cited
statement: formalized
lean: PollardRhoDPConfig
---

# Algorithm 9.6 (Pollard-ρ using distinguished points)

1. Pick random $c_i, d_i, a_0, b_0 \in \mathbb{Z}/N\mathbb{Z}$, compute $\delta_i = c_i \alpha + d_i \beta$ and $\gamma_0 = a_0 \alpha + b_0 \beta$, and initialize $D \leftarrow \emptyset$.
2. For $j = 1, 2, 3, \ldots$:
  a. Compute $(a_j, b_j, \gamma_j) = f(a_{j-1}, b_{j-1}, \gamma_{j-1})$.
  b. If $B(\gamma_j) = 1$ then
    i. If there exists $(a_k, b_k, \gamma_k) \in D$ with $\gamma_j = \gamma_k$ then return $\log_{\alpha} \beta = (a_j - a_k)/(b_k - b_j)$ if $\gcd(b_k - b_j, N) = 1$ and restart at step 1 otherwise.
    ii. If not, replace $D$ by $D \cup \{(a_j, b_j, \gamma_j)\}$ and continue.

## Depends on

- [Algorithm 9.5 (Pollard-$\rho$)](114-pollard-rho.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 9.10](../../../../../sources/v1/EllipticCurves.md)
