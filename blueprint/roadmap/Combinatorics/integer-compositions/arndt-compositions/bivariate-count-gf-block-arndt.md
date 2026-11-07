# Generating function of block Arndt compositions

Let $k \ge 1$, let $a^{(k)}(n, m)$ be
the number of $k$-block Arndt compositions of $n$ with $m$ parts, and let
$A^{(k)}(x, y) = \sum_{n \ge 0} \sum_{m=0}^{n} a^{(k)}(n, m)\, x^n y^m \in \mathbb{Z}[y][[x]]$.
Then
$A^{(k)}(x, y) \bigl(\prod_{\ell=1}^{k} (1 - x^\ell) - x^{\binom{k+1}{2}} y^k\bigr) =
\sum_{j=0}^{k-1} x^{\binom{j+1}{2}} y^j \prod_{\ell=j+1}^{k} (1 - x^\ell)$.
Equivalently, with $J_j(x, y) = x^{\binom{j+1}{2}} y^j \prod_{\ell=1}^{j} (1 - x^\ell)^{-1}$,
$A^{(k)}(x, y) = \bigl(\sum_{j=0}^{k-1} J_j(x, y)\bigr) / (1 - J_k(x, y))$.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Theorem 12 (`integers-2024-A35-thm-12`).
