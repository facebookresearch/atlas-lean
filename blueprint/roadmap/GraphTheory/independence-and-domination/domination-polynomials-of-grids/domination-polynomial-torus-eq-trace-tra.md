# Transfer-matrix formula for the domination polynomial of the torus

For all natural
numbers $m$ and $n$ with $n \ge 1$, let $C_k$ denote the cycle graph on the vertices
$0, \dots, k - 1$, in which distinct $i$ and $j$ are adjacent when $i - j \equiv \pm 1 \pmod k$,
and let $\bar A$ be the domination transfer matrix of the row graph $C_m$. Then the domination
polynomial of the torus $C_m \mathbin{\square} C_n$ equals the trace of $\bar A^n$.

The hypothesis $n \ge 1$ is needed: for $n = 0$ the trace counts the signatures of $C_m$, while
the torus $C_m \mathbin{\square} C_0$ has no vertices, so its domination polynomial is $1$. For
$n = 1$ and $n = 2$ the cycle $C_n$ is a single vertex and a single edge respectively.

## Sources

- Stephan Mertens, *Domination Polynomials of the Grid, the Cylinder, the Torus, and the King Graph*, Journal of Integer Sequences 27 (2024), Article 24.7.6, Theorem 8 (`jis-2024-24.7.6-thm-8`).
