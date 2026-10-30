/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.LpGeometry

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the geometry of finite `ℓ^p` spaces

* At `p = 3` the parallelogram identity fails on `(1, 1)` and `(1, -1)`,
  and no inner product induces the `ℓ^3` norm; at `p = 2` it holds.
* At `p = 4` the midpoint of the two unit coordinate vectors has norm `< 1`
  (strict convexity), and the norm of `(1, 1)` is `2 ^ (1 / 4)`.
* At `p = 1` the midpoint of the two unit coordinate vectors has norm `1`
  (strict convexity fails), and at `p = ∞` the norm of `(1, 1)` is `1`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.FunctionalAnalysis.LpGeometryTests

open MathlibExt.Analysis.FunctionalAnalysis.LpGeometry

/-- Local `Fact` instances for the concrete exponents used below. -/
instance fact_one_le_two_ennreal : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
instance fact_one_le_three_ennreal : Fact (1 ≤ (3 : ENNReal)) := ⟨by norm_num⟩
instance fact_one_le_four_ennreal : Fact (1 ≤ (4 : ENNReal)) := ⟨by norm_num⟩

/-- The `i`-th unit coordinate vector in `PiLp p (Fin 2 → ℝ)`. -/
noncomputable def testSingle (p : ENNReal) (i : Fin 2) : PiLp p (fun _ : Fin 2 => ℝ) :=
  PiLp.single p i 1

/-- At `p = 3` the parallelogram identity fails on `(1, 1)` and `(1, -1)`. -/
theorem parallelogram_fails_at_p3 :
    ‖lpTwoPlus (3 : ENNReal) + lpTwoMinus (3 : ENNReal)‖ ^ 2 +
        ‖lpTwoPlus (3 : ENNReal) - lpTwoMinus (3 : ENNReal)‖ ^ 2 ≠
      2 * (‖lpTwoPlus (3 : ENNReal)‖ ^ 2 + ‖lpTwoMinus (3 : ENNReal)‖ ^ 2) := by
  have hfact : Fact (1 ≤ (3 : ENNReal)) := ⟨by norm_num⟩
  exact parallelogram_fails_piLp_two (by norm_num)

/-- At `p = 2` the parallelogram identity holds on `(1, 1)` and `(1, -1)`. -/
theorem parallelogram_holds_at_p2 :
    ‖lpTwoPlus (2 : ENNReal) + lpTwoMinus (2 : ENNReal)‖ ^ 2 +
        ‖lpTwoPlus (2 : ENNReal) - lpTwoMinus (2 : ENNReal)‖ ^ 2 =
      2 * (‖lpTwoPlus (2 : ENNReal)‖ ^ 2 + ‖lpTwoMinus (2 : ENNReal)‖ ^ 2) := by
  have hfact : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  exact (parallelogram_eq_iff_piLp_two (p := (2 : ENNReal))).mpr rfl

/-- At `p = 3`, no inner product on `PiLp 3 (Fin 2 → ℝ)` induces its norm. -/
theorem not_innerProductSpace_at_p3 :
    ¬ Nonempty (InnerProductSpace ℝ (PiLp (3 : ENNReal) (fun _ : Fin 2 => ℝ))) := by
  have hfact : Fact (1 ≤ (3 : ENNReal)) := ⟨by norm_num⟩
  exact not_innerProductSpace_piLp_two (by norm_num)

/-- The norm of `(1, 1)` in `PiLp 3 (Fin 2 → ℝ)` is `2 ^ (1 / 3)`. -/
theorem norm_lpTwoPlus_at_p3 : ‖lpTwoPlus (3 : ENNReal)‖ = (2 : ℝ) ^ ((1 : ℝ) / 3) := by
  have hfact : Fact (1 ≤ (3 : ENNReal)) := ⟨by norm_num⟩
  rw [norm_lpTwoPlus_of_ne_top (by simp), show (3 : ENNReal).toReal = (3 : ℝ) from by simp]

/-- The norm of `(1, 1)` in `PiLp 4 (Fin 2 → ℝ)` is `2 ^ (1 / 4)`. -/
theorem norm_lpTwoPlus_at_p4 : ‖lpTwoPlus (4 : ENNReal)‖ = (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [norm_lpTwoPlus_of_ne_top (by simp), show (4 : ENNReal).toReal = (4 : ℝ) from by simp]

/-- The norm of `(1, 1) + (1, -1)` in `PiLp 3 (Fin 2 → ℝ)` is `2`. -/
theorem norm_add_at_p3 :
    ‖lpTwoPlus (3 : ENNReal) + lpTwoMinus (3 : ENNReal)‖ = 2 := by
  have hfact : Fact (1 ≤ (3 : ENNReal)) := ⟨by norm_num⟩
  exact norm_add_lpTwo

/-- The norm of `(1, 1)` in `PiLp ∞ (Fin 2 → ℝ)` is `1`. -/
theorem norm_lpTwoPlus_at_top : ‖lpTwoPlus (⊤ : ENNReal)‖ = 1 :=
  norm_lpTwoPlus_top

/-- At `p = 4`, the midpoint of the two unit coordinate vectors has norm `< 1`. -/
theorem midpoint_lt_one_at_p4 :
    ‖(1 / 2 : ℝ) • (testSingle (4 : ENNReal) 0 + testSingle (4 : ENNReal) 1)‖ < 1 := by
  have hfact : Fact (1 ≤ (4 : ENNReal)) := ⟨by norm_num⟩
  have hp1 : (1 : ℝ) < (4 : ENNReal).toReal := by norm_num [ENNReal.toReal_ofNat]
  have hp : (4 : ENNReal) ≠ ⊤ := by simp
  have hne : testSingle (4 : ENNReal) 0 ≠ testSingle (4 : ENNReal) 1 := by
    intro h
    have h1 := congrArg (fun z : PiLp (4 : ENNReal) (fun _ : Fin 2 => ℝ) => z (1 : Fin 2)) h
    simp only [testSingle, PiLp.single_eq_same] at h1
    norm_num at h1
  refine piLp_two_strictConvex hp1 hp _ _ ?_ ?_ hne
  · simp [testSingle, PiLp.norm_single]
  · simp [testSingle, PiLp.norm_single]

/-- At `p = 1`, the midpoint of the two unit coordinate vectors has norm `1`. -/
theorem midpoint_eq_one_at_p1 :
    ‖(1 / 2 : ℝ) • (testSingle (1 : ENNReal) 0 + testSingle (1 : ENNReal) 1)‖ = 1 := by
  have hfact : Fact (1 ≤ (1 : ENNReal)) := ⟨le_rfl⟩
  show ‖(1 / 2 : ℝ) • lpTwoPlus (1 : ENNReal)‖ = 1
  rw [norm_smul, norm_lpTwoPlus_of_ne_top (by simp)]
  norm_num [ENNReal.toReal_one, Real.rpow_one]

/-- At `p = 4`, the standard strict-convexity API handles unequal positive weights. -/
theorem convex_combination_lt_one_at_p4 :
    ‖(1 / 4 : ℝ) • testSingle (4 : ENNReal) 0 +
      (3 / 4 : ℝ) • testSingle (4 : ENNReal) 1‖ < 1 := by
  let _ := strictConvexSpace_piLp_two (p := (4 : ENNReal))
    (by norm_num [ENNReal.toReal_ofNat]) (by simp)
  refine norm_combo_lt_of_ne ?_ ?_ ?_ (by norm_num) (by norm_num) (by norm_num)
  · simp [testSingle, PiLp.norm_single]
  · simp [testSingle, PiLp.norm_single]
  · intro h
    have h1 := congrArg
      (fun z : PiLp (4 : ENNReal) (fun _ : Fin 2 => ℝ) => z (1 : Fin 2)) h
    simp only [testSingle, PiLp.single_eq_same] at h1
    norm_num at h1

#print axioms parallelogram_eq_iff_piLp_two
#print axioms not_innerProductSpace_piLp_two
#print axioms piLp_two_strictConvex

end MathlibExtTest.Analysis.FunctionalAnalysis.LpGeometryTests
