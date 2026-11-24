# The FBA value is piecewise linear

Let $S \in \mathbb{R}^{m \times n}$ be a stoichiometric matrix, $l, u, c \in \mathbb{R}^n$ flux bounds and objective. There is a finite set $T \subseteq \mathbb{R}^m \times \mathbb{R}$ of affine functions
$b \mapsto y \cdot b + \kappa$ such that for every $b \in \mathbb{R}^m$ with nonempty
[feasible set](fba-feasible.md), the [optimal value](fba-value.md) $V(b)$ is the least of the values
$y \cdot b + \kappa$, $(y, \kappa) \in T$.

## Sources

- R. T. Rockafellar, *Convex Analysis*, Princeton University Press (1970).
- J. D. Orth, I. Thiele and B. Ø. Palsson, *What is flux balance analysis?*, Nat. Biotechnol. 28 (2010) 245–248 (the flux balance formulation).
