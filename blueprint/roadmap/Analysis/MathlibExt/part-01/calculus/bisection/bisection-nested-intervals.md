---
article_id: af_4fc29179d2365b160dc48ad0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bisection_nested_intervals
---

# Bisection nested intervals

Bisection method: nested bracketing intervals halving in length at each
step while keeping a sign change.

Proof: The endpoint pairs are defined recursively by the sign of each midpoint, and induction
proves the nesting, sign, and exact halving invariants from Burden and Faires, Section 2.1.

## Depends on

- [Is Bisection Sequence](is-bisection-sequence.md)

## Proof depends on

- [Exists is Bisection Sequence nested](exists-is-bisection-sequence-nested.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.Bisection](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` / `Iterative methods of solving systems of real and vector-valued equations`, entry `bisection method` (unmapped); R. L. Burden and J. D. Faires, Numerical Analysis, 10th ed., Section 2.1; stable ref https://en.wikipedia.org/wiki/Bisection_method.
