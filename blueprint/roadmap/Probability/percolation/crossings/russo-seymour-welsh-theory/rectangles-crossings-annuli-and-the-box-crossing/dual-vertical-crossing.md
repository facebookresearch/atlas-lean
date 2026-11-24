# Dual bottom–top crossing of a rectangle

Let $\omega$ assign a bit to each unordered pair of primal sites in $\mathbb{Z}^2$, including pairs with repeated sites. Only the nearest-neighbor bonds matter here. On the shifted dual lattice $(\mathbb{Z}^2)^\ast = (\tfrac12, \tfrac12) + \mathbb{Z}^2$, the [dual configuration](dual-horizontal-crossing.md) opens a dual bond $e^\ast$ exactly when the primal bond $e$ it crosses is closed, so $\omega^\ast(e^\ast) = 1 - \omega(e)$.

For $a, b, c, d \in \mathbb{Z}$, the configuration $\omega$ has a dual bottom–top crossing of $R = [a, b] \times [c, d]$ if $\omega^\ast$ has an open path inside $R^\ast = (\tfrac12, \tfrac12) + R$ from its bottom side $\{x_2 = c + \tfrac12\}$ to its top side $\{x_2 = d + \tfrac12\}$. If $c = d$ and $a \le b$, a single dual vertex is a crossing of length zero. If $b < a$ or $d < c$, the rectangle is empty and there is no crossing.

## Sources

- Hugo Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes, IHÉS (version of 7 October 2018), §4.1 (dual lattice and dual configuration).
