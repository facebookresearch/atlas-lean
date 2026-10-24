---
article_id: af_7ca0f1db21dcaf0a59330e5a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.MeasureTheory.Integral.LyapunovConvexityWanted.lyapunov_convexity
---

# Lyapunov convexity

If `μ` is atomless finite and `f : α → E` is Bochner-integrable with `E` finite-dimensional over
`ℝ`, then `lyapunovRange μ f` is compact and convex. Source: A. Lyapunov, Izv. Akad. Nauk SSSR 4
(1940) 465–478; Diestel-Uhl, Vector Measures; Lean states atomless finite measure case with
Bochner integrable finite-dim integrand, infinite-dim fails.

## Depends on

- [Lyapunov Range](lyapunov-range.md)
- [Is Atomless](../../measure/atomless/is-atomless.md)

## Proof depends on

- [Is Atomless exists subset measure eq](../../measure/atomless/is-atomless-exists-subset-measure-eq.md)
- [Is Atomless restrict](../../measure/atomless/is-atomless-restrict.md)

## Sources

- [MathlibExt, MathlibExt.MeasureTheory.Integral.LyapunovConvexity](../../../../../sources/v2/MathlibExt.md)
