# First-order form of the mass equation

For a real $n \times n$ matrix $M$ and vectors $F, v \in \mathbb{R}^n$, the first-order right-hand side is the pair $(v, M^{-1}F)$, where the inverse of a singular matrix is taken to be the zero matrix. This is a totalised definition: it is defined for every $M$, and its second component is $0$ whenever $M$ is singular.

Only when $\det M \ne 0$ does it describe the mass equation $M\ddot q = F$: then $M^{-1}F$ is the unique acceleration solving it, as the [characterization of the first-order form](eq-first-order-rhs-iff.md) states. For a singular $M$ the second component need not be an acceleration solving the equation; for $M = 0$ and $F \ne 0$ the pair is $(v, 0)$, while $M\ddot q = F$ has no solution at all.
