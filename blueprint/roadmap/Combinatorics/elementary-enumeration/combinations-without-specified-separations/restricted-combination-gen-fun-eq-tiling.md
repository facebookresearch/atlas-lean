# Generating functions of restricted combinations and restricted-overlap tilings

Let $Q$
be a finite set of natural numbers and let $q$ be its largest element ($q = 0$ if $Q$ is empty).
Write $S^Q_{n,k}$ for the number of $k$-subsets of $\{1, \dots, n\}$ in which no two elements
differ by an element of $Q$, and $B^Q_{n,k}$ for the number of restricted-overlap tilings of an
$n$-board with squares and $k$ $Q$-combs. In the ring $\mathbb{Z}[y][[x]]$ of power series in
$x$ with coefficients in $\mathbb{Z}[y]$, let
$g^Q(x, y) = \sum_{n \ge 0} \sum_{k=0}^{n} S^Q_{n,k} x^n y^k$ and
$G(x, y) = \sum_{n \ge 0} \sum_{k=0}^{n} B^Q_{n,k} x^n y^k$. Then

$$x^q g^Q(x, y) = G(x, y) - \sum_{n=0}^{q-1} x^n.$$

This is the paper's formula $g^Q = \bigl(G - (1 - x^q)/(1 - x)\bigr)/x^q$ with the denominators
cleared.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Corollary 7.
