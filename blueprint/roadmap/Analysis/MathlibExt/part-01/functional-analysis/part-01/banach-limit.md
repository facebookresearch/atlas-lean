---
article_id: af_419f77f392253db3ab8d4a12
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.BanachLimit.banach_limit
---

# Banach Limit

There exists a Banach limit `L : (ℕ →ᵇ ℝ) →L[ℝ] ℝ` on bounded real sequences that is positive on
pointwise nonnegative sequences, satisfies `L 1 = 1` for the constant-one sequence, is invariant
under the left shift `g n = f (n+1)`, and extends ordinary limits in that `f n → l` implies `L f =
l`. Source: S. Banach, Theorie des operations lineaires, 1932, definition of generalised limit; G.
Lorentz, Acta Math. 80 (1948) 167-190; Lean formalizes ℓ∞ via `BoundedContinuousFunction ℕ ℝ` and
real field `ℝ` with all four classical axioms.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.BanachLimit](../../../../../../sources/v2/MathlibExt.md)
