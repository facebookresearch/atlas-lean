---
article_id: af_5b6b0a6c366998f1aebcee08
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.newton_method_local_quadratic_convergence
---

# Newton method local quadratic convergence

Newton's method converges locally quadratically to a simple root: near
`c` the iterates stay in the basin, satisfy a quadratic error recursion, and
converge to `c`.

Proof: Continuity keeps `f'` away from zero near `c`, and `C²` regularity makes `f'` Lipschitz
on a compact interval around `c`. The mean value theorem then bounds one Newton step by
`(K / m) * |x - c| ^ 2`; this replaces the Lagrange remainder in Wikipedia's "Proof of quadratic
convergence for Newton's iterative method". Shrinking the neighborhood gives an invariant
half-contraction and geometric convergence.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Newton step sub root abs le](newton-step-sub-root-abs-le.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.NewtonMethod](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` / `Iterative methods of solving systems of real and vector-valued equations`, entries `Newton's method` and `rate of convergence and estimation of error` (unmapped); R. L. Burden and J. D. Faires, Numerical Analysis, 10th ed., Theorem 2.6; stable ref https://en.wikipedia.org/wiki/Newton%27s_method.
