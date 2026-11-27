# Strict refinement of a weakly feasible spherical-code tuple

Let $r\ge0$, let $a=(a_0,\ldots,a_r)$ and $b=(b_0,\ldots,b_{r-1})$ interlace, and suppose the real cutoff $s$ satisfies $0<s\le2\Gamma(a,b)$. There exist a level $r'\ge0$ and interlacing arrays $A=(A_0,\ldots,A_{r'})$ and $B=(B_0,\ldots,B_{r'-1})$ such that

$$ s<2\Gamma(A,B),\qquad \Phi(A,B)<\Phi(a,b). $$

The input may have equality in the spectral constraint. The conclusion is strict in both the spectral constraint and the objective, and the level may change. For positive final coordinate $a_r$, the source raises the level by one. If $a_r=0$ and $r>0$, it opens the final coordinate at the same level. With $a_0=0$ at level zero the premise is impossible, since then $\Gamma(a,b)=0$.

## Depends on

- [Interlaced variational objectives for spherical codes](interlaced-spherical-code-objectives.md)

## Expansion

Separate the next-level construction for positive final coordinate from the same-level opening at a zero final coordinate. Establish the spectral and objective inequalities for each construction, and rule out the zero-final-coordinate case at level zero. The assertion is not continuity of an infimum with a relaxed constraint.

## Sources

- [Pinned strict-refinement theorem and case split](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MetricCodes.lean#L42924-L42949)
