# Stacked permutation patterns in three dimensions

Let $P \subseteq \mathbb{R}^2$ be a
finite set of at least two points with pairwise distinct $x$-coordinates and pairwise distinct
$y$-coordinates, and for $i \in \{2, 3\}$ let
$P_i = \{(x, y, j) : (x, y) \in P,\ j \in \{1, \dots, i\}\} \subseteq \mathbb{R}^3$. Then, as $n$
tends to infinity through the natural numbers, $\mathrm{opx}(n, P_2, 3) = \Theta(n^{5/2})$ and
$\mathrm{opx}(n, P_3, 3) = \Theta(n^{8/3})$.

The requirement of at least two points is the paper's standing assumption on the permutation
matrix: for a single point, $P_2$ is two points on a vertical line and
$\mathrm{opx}(n, P_2, 3) \le n^2$.

## Sources

- Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.15.
