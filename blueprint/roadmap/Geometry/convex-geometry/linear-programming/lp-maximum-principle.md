# Maximum principle for linear programming

Consider a linear program with $m$ variables
and objective vector $c \in \mathbb{R}^m$, let $P \subseteq \mathbb{R}^m$ be its feasible region
and $f(x) = c \cdot x$ its objective function, and let $x \in P$ be a local maximiser of $f$ on
$P$, that is, $f(y) \le f(x)$ for all $y \in P$ in some neighbourhood of $x$. Then $x$ is a
global maximiser of $f$ on $P$, and if $c \ne 0$ then $x$ lies on the topological boundary of
$P$ in $\mathbb{R}^m$.

## Sources

- G. B. Dantzig (1947), simplex algorithm. Listed as §101 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Problem `lp_maximum_principle` of the lean-eval benchmark.
