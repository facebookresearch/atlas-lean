# Symmetric formula for the rook domination polynomial

For natural numbers $n, m \ge 1$,
the rook domination polynomial $D_{n,m}(x)$ of the $n \times m$ board, an integer polynomial,
satisfies

$$D_{n,m}(x) = ((1+x)^n - 1)^m + ((1+x)^m - 1)^n -
(-1)^{n+m} \sum_{\ell=0}^{n} \sum_{k=0}^{m} (-1)^{k+\ell}
\binom{n}{\ell} \binom{m}{k} (1+x)^{k\ell}.$$

## Sources

- Stephan Mertens, "Domination Polynomial of the Rook Graph", Corollary 5 (`cor:domination-polynomial`).
