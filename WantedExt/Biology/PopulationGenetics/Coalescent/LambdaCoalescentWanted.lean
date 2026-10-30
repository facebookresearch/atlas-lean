/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pitman's representation of consistent merger rates (existence)

A family of rates `r b k` (`2 ≤ k ≤ b`: the rate at which a given set of `k` among `b` blocks
merges) is **consistent** if `r b k = r (b + 1) k + r (b + 1) (k + 1)`. Pitman (1999,
Theorem 1) showed that the consistent families of nonnegative rates are exactly the families
`λ_{b,k} = ∫ x ^ (k - 2) (1 - x) ^ (b - k) Λ(dx)` for a finite measure `Λ` on `[0, 1]`
(`MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent.mergerRate`), and that
`Λ` is unique.

Consistency and uniqueness are proved in
`MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent`
(`mergerRate_consistent`, `mergerRate_nonneg`, `eq_of_mergerRate_eq`). The existence half
recorded here is a Hausdorff moment problem: consistency gives
`r (i + 2 + c) (i + 2) = ((I - E) ^ c m) i` for the sequence `m i = r (i + 2) (i + 2)` and the
shift `E`, so nonnegativity says that `m` is completely monotone, and Hausdorff's theorem
yields a finite measure on `[0, 1]` whose moments are `m`. The one-dimensional case of
`MathlibExt.Analysis.HausdorffMomentsWanted.Analysis.hausdorff_positivity` would therefore
give this statement; neither is proved yet.

Sources: J. Pitman, "Coalescents with multiple collisions", Ann. Probab. 27 (1999)
1870–1902, Theorem 1; F. Hausdorff, "Summationsmethoden und Momentfolgen I", Math. Z. 9
(1921) 74–109; W. Feller, *An Introduction to Probability Theory and Its Applications*,
vol. II, 2nd ed. (1971), §VII.3.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescentWanted

open MeasureTheory unitInterval
open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent

/-- **Pitman's representation theorem, existence half** (Pitman 1999, Theorem 1): every
consistent family of nonnegative merger rates `r b k`, `2 ≤ k ≤ b`, is the family of merger
rates `λ_{b,k}` of some finite measure `Λ` on `[0, 1]`. (Uniqueness of `Λ` is
`LambdaCoalescent.eq_of_mergerRate_eq`.)

Source: Pitman (1999), Theorem 1; Hausdorff (1921). -/
theorem_wanted exists_measure_of_consistent (r : ℕ → ℕ → ℝ)
    (hnonneg : ∀ b k, 2 ≤ k → k ≤ b → 0 ≤ r b k)
    (hcons : ∀ b k, 2 ≤ k → k ≤ b → r b k = r (b + 1) k + r (b + 1) (k + 1)) :
    ∃ Λ : Measure I, IsFiniteMeasure Λ ∧ ∀ b k, 2 ≤ k → k ≤ b → r b k = mergerRate Λ b k

end MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescentWanted
