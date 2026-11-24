# Shadow prices are derivatives when unique

Let $S \in \mathbb{R}^{m \times n}$ be a stoichiometric matrix, $l, u, c \in \mathbb{R}^n$ flux bounds and objective, let $b \in \mathbb{R}^m$ be an interior point of the set of right-hand sides with
nonempty [feasible set](fba-feasible.md), and let $y \in \mathbb{R}^m$ be the only metabolite price vector
of an optimal dual solution (a [dual feasible](fba-dual-feasible.md) point minimizing the [dual objective](fba-dual-value.md)
at $b$). Then the [optimal value](fba-value.md) $V$ is differentiable at $b$ with derivative
$b' \mapsto y \cdot b'$.

## Sources

- R. T. Rockafellar, *Convex Analysis*, Princeton University Press (1970).
- J. D. Orth, I. Thiele and B. Ø. Palsson, *What is flux balance analysis?*, Nat. Biotechnol. 28 (2010) 245–248 (the flux balance formulation).
