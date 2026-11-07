# Optimal vertices of linear programs

Consider a linear program with $m$ variables and
objective vector $c \in \mathbb{R}^m$, and let $P \subseteq \mathbb{R}^m$ be its feasible region
and $f(x) = c \cdot x$ its objective function. If $P$ is nonempty and bounded, then some
$x \in P$ maximises $f$ on $P$ and is an extreme point of $P$, that is, $x$ does not lie in the
open segment between two distinct points of $P$.

## Sources

- G. B. Dantzig (1947), simplex algorithm. Listed as §101 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `lp_maximum_principle`.
