---
article_id: af_059a9ecd5c2bf9a8ba8579f0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.ArgumentPrinciple.argumentPrinciple_closedBall
---

# Argument Principle closed Ball

Argument principle on a closed disc: if `f : ℂ → ℂ` is meromorphic on `closedBall c R` with no zeros
or poles on the boundary `sphere c R`, then the contour integral of `f'/f` equals `2πi` times the
divisor sum (zeros minus poles with multiplicity) inside `ball c R`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Argument Principle closed Ball general](argument-principle-closed-ball-general.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.ArgumentPrinciple](../../../../../../../sources/v2/MathlibExt.md)
- L. V. Ahlfors, Complex Analysis, 3rd ed., §5.2. It follows from `argumentPrinciple_closedBall_general`; the hypothesis `hint` is unused and keeps the source's shape. Proves `Wanted` entry `argumentPrinciple_closedBall`.
