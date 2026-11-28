# Dynamic weighted orthogonal range counting

In *dynamic weighted orthogonal range counting* in two dimensions, the structure maintains a multiset of points $p \in [n]^2$, each with a weight $\omega(p) \in \{0, \dots, 2^{\Theta(\lg n)} - 1\}$, under insertion of weighted points, and answers queries $q = (x, y)$ with $\sum \omega(p)$ over the points $p = (x', y')$ dominated by $q$, i.e. with $x' \le x$ and $y' \le y$.

## Depends on

- [Amortized update and query cost of a dynamic cell-probe structure](../dynamic-information-transfer-lower-bounds/amortized-cell-probe-costs.md)

## Sources

- Kasper Green Larsen, "The Cell Probe Complexity of Dynamic Range Counting", STOC (2012), arXiv:1105.5933.
