# Grid edge costs

Let $d$ and $k$ be natural numbers and let $w_0, \dots, w_{d-1}$ be
natural numbers. The grid cost with cost $w_i$ in coordinate $i$ assigns to each unordered pair
$\{x, y\}$ of points of $\{0, \dots, k-1\}^d$ the sum of the $w_i$ over the coordinates $i$ with
$x_i \ne y_i$. On an edge of the grid exactly one coordinate differs, so an edge in coordinate
$i$ costs $w_i$.

## Sources

- Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 3.2 (cost `wᵢ` in coordinate `i`).
