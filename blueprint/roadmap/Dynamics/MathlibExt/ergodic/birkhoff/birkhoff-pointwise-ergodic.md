---
article_id: af_d3133a59675dfe1cb50e3730
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Dynamics.Ergodic.BirkhoffWanted.birkhoff_pointwise_ergodic
---

# Birkhoff pointwise ergodic

If `μ` is a probability measure, `T` is ergodic measure-preserving, and `g : α → ℝ` is integrable,
then `birkhoffAverage ℝ T g n x` converges for `μ`-a.e. `x` to `∫ y, g y ∂μ`. Source: G. D.
Birkhoff, Proc. Natl. Acad. Sci. USA 17 (1931); Walters, Intro to Ergodic Theory; Lean states
ergodic case for ℝ-valued integrable functions while general theorem gives conditional expectation
onto invariant σ-algebra.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Dick Set](dick-set.md)
- [Dick inv](dick-inv.md)
- [Dick iter](dick-iter.md)
- [Dick measurable](dick-measurable.md)
- [Dick mem](dick-mem.md)
- [Dick sum in](dick-sum-in.md)
- [Dick sum out](dick-sum-out.md)
- [Maximal ergodic](maximal-ergodic.md)

## Sources

- [MathlibExt, MathlibExt.Dynamics.Ergodic.Birkhoff](../../../../../sources/v2/MathlibExt.md)
