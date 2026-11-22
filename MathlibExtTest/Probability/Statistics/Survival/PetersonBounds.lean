/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.PetersonBounds
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

namespace MathlibExtTest.Probability.Statistics.PetersonBounds

/-! ### Point masses, computed from the definitions -/

/-- The observed-data law of a point-mass joint law is the point mass at the observation. -/
theorem jointCensoredObsLaw_dirac (s c : ℝ) :
    jointCensoredObsLaw (Measure.dirac (s, c)) = Measure.dirac (censoredObsMap (s, c)) := by
  rw [jointCensoredObsLaw, Measure.map_dirac' measurable_censoredObsMap]

/-- The failure-time law of a point-mass joint law, evaluated on `(-∞, t]`. -/
theorem fst_dirac_Iic (s c t : ℝ) :
    (Measure.dirac (s, c)).fst (Iic t) = if s ≤ t then 1 else 0 := by
  rw [Measure.fst, Measure.map_dirac' measurable_fst, Measure.dirac_apply' _ measurableSet_Iic]
  by_cases h : s ≤ t <;> simp [h, indicator]

open Classical in
/-- A point mass on `ℝ × Bool`, evaluated on a product set. -/
theorem dirac_prod (x : ℝ) (b : Bool) (A : Set ℝ) (B : Set Bool) :
    Measure.dirac (x, b) (A ×ˢ B) = if x ∈ A ∧ b ∈ B then 1 else 0 := by
  rw [Measure.dirac_apply]
  by_cases h : x ∈ A ∧ b ∈ B <;> simp [h, indicator, mem_prod]

/-! ### A subject censored at `0`: the bounds are `[0, 1]` at `t = 1` -/

/-- Censoring at `0` (`T = 2`, `C = 0`) is observed as `(0, censored)`. -/
example : jointCensoredObsLaw (Measure.dirac ((2 : ℝ), (0 : ℝ))) =
    Measure.dirac ((0 : ℝ), false) := by
  rw [jointCensoredObsLaw_dirac]
  congr 1
  simp only [censoredObsMap, obsTime, Prod.mk.injEq]
  norm_num

/-- `T = 1/2`, `C = 0` gives the same observation `(0, censored)`. -/
example : jointCensoredObsLaw (Measure.dirac ((1 / 2 : ℝ), (0 : ℝ))) =
    Measure.dirac ((0 : ℝ), false) := by
  rw [jointCensoredObsLaw_dirac]
  congr 1
  simp only [censoredObsMap, obsTime, Prod.mk.injEq]
  norm_num

/-- **Non-identification, computed directly**: the two joint laws above have the same
observed-data law but `P(T ≤ 1)` is `0` for one and `1` for the other. -/
example : (Measure.dirac ((2 : ℝ), (0 : ℝ))).fst (Iic 1) = 0 ∧
    (Measure.dirac ((1 / 2 : ℝ), (0 : ℝ))).fst (Iic 1) = 1 := by
  rw [fst_dirac_Iic, fst_dirac_Iic]
  norm_num

/-- The Peterson bounds of `P = δ_(0, censored)` at `t = 1`, computed from the definitions. -/
theorem petersonLower_censored_one : petersonLower (Measure.dirac ((0 : ℝ), false)) 1 = 0 := by
  rw [petersonLower, dirac_prod]
  simp

theorem petersonUpper_censored_one : petersonUpper (Measure.dirac ((0 : ℝ), false)) 1 = 1 := by
  rw [petersonUpper, dirac_prod, dirac_prod]
  norm_num

/-- The two endpoints are attained by the explicit point-mass joint laws above. -/
example : (Measure.dirac ((2 : ℝ), (0 : ℝ))).fst (Iic 1) =
      petersonLower (Measure.dirac ((0 : ℝ), false)) 1 ∧
    (Measure.dirac ((1 / 2 : ℝ), (0 : ℝ))).fst (Iic 1) =
      petersonUpper (Measure.dirac ((0 : ℝ), false)) 1 := by
  rw [fst_dirac_Iic, fst_dirac_Iic, petersonLower_censored_one,
    petersonUpper_censored_one]
  norm_num

/-- The couplings of the main file, evaluated: the lower coupling puts `T = 2 > 1`, the upper
coupling puts `T = 1`. -/
example : lowerCoupling 1 ((0 : ℝ), false) = (2, 0) ∧
    upperCoupling 1 ((0 : ℝ), false) = (1, 0) := by
  simp only [lowerCoupling, upperCoupling, Bool.cond_false, Prod.mk.injEq]
  norm_num

/-! ### Boundary: censoring exactly at `t` -/

/-- **Ties.** At `t = 0`, the subject censored at `0` has `T > 0` (ties count as failures), so the
interval collapses to `{0}`: the upper bound uses `X < t`. The textbook form with `X ≤ t` adds
the censored mass `P(X ≤ 0, δ = 0) = 1`; it is still an upper bound, but not sharp. -/
example : petersonLower (Measure.dirac ((0 : ℝ), false)) 0 = 0 ∧
    petersonUpper (Measure.dirac ((0 : ℝ), false)) 0 = 0 ∧
    Measure.dirac ((0 : ℝ), false) (Iic 0 ×ˢ {false}) = 1 := by
  rw [petersonLower, petersonUpper, dirac_prod, dirac_prod, dirac_prod]
  simp

/-- An observed failure at `0` gives the point interval `{1}` at `t = 0`. -/
example : petersonLower (Measure.dirac ((0 : ℝ), true)) 0 = 1 ∧
    petersonUpper (Measure.dirac ((0 : ℝ), true)) 0 = 1 := by
  rw [petersonLower, petersonUpper, dirac_prod, dirac_prod]
  simp

/-! ### Usage of the main theorems -/

/-- **The identified set is the nondegenerate interval `[0, 1]`.** -/
example : petersonIdentifiedSet (Measure.dirac ((0 : ℝ), false)) 1 = Icc 0 1 := by
  rw [petersonIdentifiedSet_eq, petersonLower_censored_one, petersonUpper_censored_one]

/-- An interior value `1/2` is attained by some compatible joint law. -/
example : ∃ μ : Measure (ℝ × ℝ), IsProbabilityMeasure μ ∧
    jointCensoredObsLaw μ = Measure.dirac ((0 : ℝ), false) ∧ μ.fst (Iic 1) = 2⁻¹ := by
  refine exists_jointCensoredObsLaw_eq_fst_Iic_eq _ ?_ ?_
  · rw [petersonLower_censored_one]
    exact zero_le
  · rw [petersonUpper_censored_one]
    exact ENNReal.inv_le_one.2 one_le_two

/-- The non-identification theorem applies: `P(X < 1, δ = 0) = 1 ≠ 0`. -/
example : ∃ μ μ' : Measure (ℝ × ℝ), IsProbabilityMeasure μ ∧ IsProbabilityMeasure μ' ∧
    jointCensoredObsLaw μ = Measure.dirac ((0 : ℝ), false) ∧
    jointCensoredObsLaw μ' = Measure.dirac ((0 : ℝ), false) ∧
    μ.fst (Iic 1) ≠ μ'.fst (Iic 1) :=
  exists_fst_Iic_ne_of_jointCensoredObsLaw_eq _ (by rw [dirac_prod]; norm_num)

/-- Point identification at `t = 0` for laws observed as `(0, censored)`: the two joint laws above
agree on `P(T ≤ 0)`. -/
example : (Measure.dirac ((2 : ℝ), (0 : ℝ))).fst (Iic 0) =
    (Measure.dirac ((1 / 2 : ℝ), (0 : ℝ))).fst (Iic 0) := by
  have h₁ : jointCensoredObsLaw (Measure.dirac ((2 : ℝ), (0 : ℝ))) =
      Measure.dirac ((0 : ℝ), false) := by
    rw [jointCensoredObsLaw_dirac]
    congr 1
    simp only [censoredObsMap, obsTime, Prod.mk.injEq]
    norm_num
  have h₂ : jointCensoredObsLaw (Measure.dirac ((1 / 2 : ℝ), (0 : ℝ))) =
      Measure.dirac ((0 : ℝ), false) := by
    rw [jointCensoredObsLaw_dirac]
    congr 1
    simp only [censoredObsMap, obsTime, Prod.mk.injEq]
    norm_num
  refine fst_Iic_eq_of_jointCensoredObsLaw_eq (h₁.trans h₂.symm) ?_
  rw [h₁, dirac_prod]
  simp

/-- The bounds hold for an arbitrary joint law. -/
example (μ : Measure (ℝ × ℝ)) (t : ℝ) :
    μ.fst (Iic t) ∈ Icc (petersonLower (jointCensoredObsLaw μ) t)
      (petersonUpper (jointCensoredObsLaw μ) t) :=
  ⟨petersonLower_le_fst_Iic μ t, fst_Iic_le_petersonUpper μ t⟩

/-- Under independent censoring (`T = 0`, `C = 1`), the bounds contain `F(-∞, 0] = 1`. -/
example : petersonLower (censoredObsLaw (Measure.dirac 0) (Measure.dirac 1)) 0 ≤
      Measure.dirac (0 : ℝ) (Iic 0) ∧
    Measure.dirac (0 : ℝ) (Iic 0) ≤
      petersonUpper (censoredObsLaw (Measure.dirac 0) (Measure.dirac 1)) 0 :=
  ⟨petersonLower_le_censoredObsLaw _ _ 0, le_petersonUpper_censoredObsLaw _ _ 0⟩

end MathlibExtTest.Probability.Statistics.PetersonBounds
