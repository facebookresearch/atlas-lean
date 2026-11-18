/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Helpers
public import MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent

/-!
# Tests for consistency and complete monotonicity of merger rates

Kingman's rates give the diagonal sequence `(1, 0, 0, …)` and the uniform rates give
`m i = 1 / (i + 1)`. The smallest off-diagonal entry checks `λ_{3,2} = m₀ - m₁ = 1/2`.
-/

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.Helpers

/-! ### Record acceptance items and instantiation with Atlas's Λ-coalescent rates -/

open MeasureTheory unitInterval
open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent

/-- Atlas's merger rates satisfy the hypotheses, so `k ↦ λ_{k,k}` is completely monotone. -/
example (Λ : Measure I) [IsFiniteMeasure Λ] (i c : ℕ) :
    0 ≤ (-1) ^ c * (fwdDiff 1)^[c] (fun j => mergerRate Λ (j + 2) (j + 2)) i :=
  completelyMonotone_diag_of_consistent (mergerRate Λ) (fun b k _ _ => mergerRate_nonneg Λ b k)
    (fun _ _ hk hkb => mergerRate_consistent Λ hk hkb) i c

/-- Acceptance: Kingman's rates (`Λ = δ₀`) give `m = (1, 0, 0, …)`. -/
example : (fun j => mergerRate (Measure.dirac (0 : I)) (j + 2) (j + 2)) =
    fun j => if j = 0 then 1 else 0 := by
  funext j
  rw [mergerRate_dirac_zero]
  by_cases hj : j = 0 <;> simp [hj]

/-- Acceptance: the uniform `Λ` (Bolthausen–Sznitman) gives `m i = 1 / (i + 1)`. -/
example (i : ℕ) : mergerRate volume (i + 2) (i + 2) = 1 / ((i : ℝ) + 1) := by
  rw [mergerRate_volume (by omega) le_rfl]
  simp only [show i + 2 - 2 = i by omega, Nat.sub_self, Nat.factorial_zero,
    show i + 2 - 1 = i + 1 by omega, Nat.factorial_succ]
  push_cast
  field_simp

/-- Non-vacuity at the smallest off-diagonal entry (`i = 0`, `c = 1`): `λ_{3,2} = m₀ - m₁`,
which is `1 - 1/2 = 1/2` for the uniform `Λ`. -/
example : mergerRate volume 3 2 = mergerRate volume 2 2 - mergerRate volume 3 3 := by
  have h := consistent_eq_iterate_sub_shift (mergerRate volume)
    (fun _ _ hk hkb => mergerRate_consistent volume hk hkb) 0 1
  simpa using h

example : mergerRate volume 3 2 = 1 / 2 := by
  rw [mergerRate_volume (by norm_num) (by norm_num)]
  norm_num [Nat.factorial]

#print axioms
  MathlibExt.Biology.PopulationGenetics.Coalescent.iterate_sub_shift_eq_neg_one_pow_mul_fwdDiff_iter
#print axioms MathlibExt.Biology.PopulationGenetics.Coalescent.consistent_eq_iterate_sub_shift
#print axioms
  MathlibExt.Biology.PopulationGenetics.Coalescent.completelyMonotone_diag_of_consistent

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.Helpers
