# Dynamic two-dimensional range parity

*Dynamic range counting over $\mathbb{F}_2$* (range parity) maintains a set of points in $[n]^2$ under insertions and answers queries $q = (x, y)$ with the parity of the number of points dominated by $q$. It is a *Boolean* dynamic problem: every query returns a single bit, so lower-bound techniques that rely on each query revealing $\Theta(\lg n)$ bits about the updates, such as Larsen's cell-sampling bound for weighted range counting, do not apply directly.

## Depends on

- [Dynamic weighted orthogonal range counting](../cell-sampling-and-range-counting-lower-bounds/weighted-dominance-range-counting.md)

## Sources

- Kasper Green Larsen, Omri Weinstein, Huacheng Yu, "Crossing the Logarithmic Barrier for Dynamic Boolean Data Structure Lower Bounds", STOC (2018); SIAM Journal on Computing (2020), arXiv:1703.03575.
