/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.LogarithmicPotentialEquilibriumFree
import Mathlib.Analysis.PSeries

namespace MathlibExt.Analysis.LogarithmicPotentialEquilibriumFreeWanted

example : ¬ conjecture := conjecture_refuted

/-- Every charge sequence with pairwise distinct, nonzero positions and `∑ 1/|z_n| < ∞` has an
equilibrium point: a point off the charges where the field vanishes. -/
private theorem exists_fieldSum_eq_zero (c : ChargeSeq) (hc : PointsDistinct c)
    (hs : IsSummable c) : ∃ z : ℂ, (∀ n, z ≠ c n) ∧ FieldSum c z = 0 := by
  by_contra h
  exact conjecture_refuted ⟨c, hc, hs, fun z hz hz0 => h ⟨z, hz, hz0⟩⟩

/-- The charges at the squares `1, 4, 9, …`. -/
private noncomputable def squares : ChargeSeq := fun n => ((n + 1 : ℕ) : ℂ) ^ 2

/-- The charges at the squares have pairwise distinct positions. -/
private theorem pointsDistinct_squares : PointsDistinct squares := by
  intro m n h
  have h' : ((m + 1 : ℕ) : ℂ) ^ 2 = ((n + 1 : ℕ) : ℂ) ^ 2 := h
  have h'' : (m + 1) ^ 2 = (n + 1) ^ 2 := by exact_mod_cast h'
  exact Nat.succ_injective (Nat.pow_left_injective two_ne_zero h'')

/-- The charges at the squares form a summable charge sequence, so the hypotheses of the refuted
conjecture can be met. -/
private theorem isSummable_squares : IsSummable squares := by
  refine ⟨fun n => pow_ne_zero 2 (Nat.cast_ne_zero.mpr n.succ_ne_zero), ?_⟩
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine h.congr fun n => ?_
  rw [squares, norm_pow, Complex.norm_natCast]

/-- Hence the field of the charges at the squares vanishes somewhere off the charges. -/
example : ∃ z : ℂ, (∀ n : ℕ, z ≠ ((n + 1 : ℕ) : ℂ) ^ 2) ∧ FieldSum squares z = 0 :=
  exists_fieldSum_eq_zero squares pointsDistinct_squares isSummable_squares

/-- `FieldSum` takes the junk value `0` when the family `1 / (z - z_n)` is not summable, here for
the constant charge sequence at `0` and the point `1`. -/
example : FieldSum (fun _ => 0) 1 = 0 := by
  simp [FieldSum]

end MathlibExt.Analysis.LogarithmicPotentialEquilibriumFreeWanted
