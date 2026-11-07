# Dominating rook placements at high density

For natural numbers $n, m \ge 1$ and $k$ with
$k > nm - n - m - \min(n, m) + 2$, let $d_{n,m}(k)$ be the number of $k$-element sets of cells
of the $n \times m$ board that are dominating sets of the rook graph on that board. Then

$$d_{n,m}(k) = \binom{nm}{k} - nm \binom{(n-1)(m-1)}{k}.$$

## Sources

- Stephan Mertens, "Domination Polynomial of the Rook Graph", Corollary 3 (`cor:high-density`).
