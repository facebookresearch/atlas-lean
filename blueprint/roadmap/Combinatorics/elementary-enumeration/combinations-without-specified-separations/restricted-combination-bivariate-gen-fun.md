# Bivariate generating function for well-based forbidden differences

Let $Q$ be a finite
set of positive integers that is well based, and write $S^Q_{n,k}$ for the number of $k$-subsets
of $\{1, \dots, n\}$ in which no two elements differ by an element of $Q$. In the ring
$\mathbb{Z}[y][[x]]$ of formal power series in $x$ with coefficients in $\mathbb{Z}[y]$, let
$g(x, y) = \sum_{n \ge 0} \sum_{k=0}^{n} S^Q_{n,k} \, y^k x^n$ and
$c = 1 + \sum_{q \in Q} x^q y$. Then $g(x, y) \, \bigl((1 - x) \, c - x y\bigr) = c$; since
$(1 - x) c - x y$ has constant term $1$, this says $g = c / ((1 - x) c - x y)$.

The empty set counts as well based, so the case $Q = \emptyset$, where $g = 1/(1 - x - xy)$,
is included.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Corollary 24.
