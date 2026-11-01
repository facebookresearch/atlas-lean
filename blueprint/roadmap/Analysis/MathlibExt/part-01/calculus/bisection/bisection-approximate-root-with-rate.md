---
article_id: af_12fe3df78099c7dea0b74b04
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bisection_approximate_root_with_rate
---

# Bisection approximate root with rate

Bisection correctness with linear rate: the midpoints converge to a root
with error at most `(b - a) / 2 ^ (n + 1)`.

Proof: Monotone convergence gives the common endpoint limit, continuity makes it a root, and the
halved interval length gives the midpoint error bound, following Burden and Faires, Theorem 2.1.

## Depends on

- [Is Bisection Sequence](is-bisection-sequence.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.Bisection](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` / `Iterative methods of solving systems of real and vector-valued equations`, entries `bisection method` and `rate of convergence and estimation of error` (unmapped); R. L. Burden and J. D. Faires, Numerical Analysis, 10th ed., Theorem 2.1.
