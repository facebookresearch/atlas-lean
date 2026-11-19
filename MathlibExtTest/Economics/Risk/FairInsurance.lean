/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Risk.FairInsurance
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Risk.FairInsurance`

Two equally likely states, wealth `3`, losses `0` and `2`, utility `4 t - t²`: no insurance gives
expected utility `3`, fair full insurance gives `4`. -/

open Convexity
open MathlibExt.Economics.ExpectedUtility
open MathlibExt.Economics.Risk

namespace MathlibExtTest.Economics.Risk.FairInsurance

noncomputable def exP : StdSimplex ℝ (Fin 2) :=
  StdSimplex.duple (0 : Fin 2) 1 (s := (1/2 : ℝ)) (t := (1/2 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num)

theorem exP_w0 : exP.weights 0 = 1 / 2 := by unfold exP; simp

theorem exP_w1 : exP.weights 1 = 1 / 2 := by unfold exP; simp

theorem exUtil_concave : ConcaveOn ℝ Set.univ (fun t : ℝ => 4 * t - t ^ 2) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    have hdecomp : (4 * (a * x + b * y) - (a * x + b * y) ^ 2) -
        (a * (4 * x - x ^ 2) + b * (4 * y - y ^ 2)) = a * b * (x - y) ^ 2 := by
      linear_combination (-(a * x ^ 2 + b * y ^ 2)) * hab
    have hnn : 0 ≤ a * b * (x - y) ^ 2 := by positivity
    linarith

theorem exW0 : insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) 0 0 = 3 := by
  unfold insuredWealth expectedUtility
  simp [exP]

theorem exW1 : insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) 0 1 = 1 := by
  unfold insuredWealth expectedUtility
  simp [exP]
  norm_num

-- (a) no insurance gives final wealth ![3, 1]
example : insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) 0 = ![3, 1] := by
  funext i
  fin_cases i
  · simp [exW0]
  · simp [exW1]

-- (a) no insurance gives expected utility 3
example : expectedUtility ((fun t : ℝ => 4 * t - t ^ 2) ∘
    insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) 0) exP = 3 := by
  simp only [expectedUtility, Fin.sum_univ_two, Function.comp_apply, exP_w0, exP_w1, exW0,
    exW1]
  norm_num

theorem exELoss : expectedUtility (![0, 2] : Fin 2 → ℝ) exP = 1 := by
  simp only [expectedUtility, Fin.sum_univ_two, exP_w0, exP_w1]
  simp

theorem exWfull0 :
    insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) (![0, 2] : Fin 2 → ℝ) 0 = 2 := by
  rw [insuredWealth_self, exELoss]
  norm_num

theorem exWfull1 :
    insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) (![0, 2] : Fin 2 → ℝ) 1 = 2 := by
  rw [insuredWealth_self, exELoss]
  norm_num

-- (b) full insurance gives expected utility 4
example : expectedUtility ((fun t : ℝ => 4 * t - t ^ 2) ∘
    insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) (![0, 2] : Fin 2 → ℝ)) exP = 4 := by
  simp only [expectedUtility, Fin.sum_univ_two, Function.comp_apply, exP_w0, exP_w1, exWfull0,
    exWfull1]
  norm_num

-- (c) strict inequality
example : expectedUtility ((fun t : ℝ => 4 * t - t ^ 2) ∘
    insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) 0) exP <
    expectedUtility ((fun t : ℝ => 4 * t - t ^ 2) ∘
      insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) (![0, 2] : Fin 2 → ℝ)) exP := by
  have h0 : expectedUtility ((fun t : ℝ => 4 * t - t ^ 2) ∘
      insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) 0) exP = 3 := by
    simp only [expectedUtility, Fin.sum_univ_two, Function.comp_apply, exP_w0, exP_w1, exW0,
      exW1]
    norm_num
  have hfull : expectedUtility ((fun t : ℝ => 4 * t - t ^ 2) ∘
      insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) (![0, 2] : Fin 2 → ℝ)) exP = 4 := by
    simp only [expectedUtility, Fin.sum_univ_two, Function.comp_apply, exP_w0, exP_w1,
      exWfull0, exWfull1]
    norm_num
  rw [h0, hfull]
  norm_num

-- (c) weak inequality via the main theorem
example : expectedUtility ((fun t : ℝ => 4 * t - t ^ 2) ∘
    insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) 0) exP ≤
    expectedUtility ((fun t : ℝ => 4 * t - t ^ 2) ∘
      insuredWealth exP 3 (![0, 2] : Fin 2 → ℝ) (![0, 2] : Fin 2 → ℝ)) exP :=
  expectedUtility_insuredWealth_le_full exUtil_concave exP 3 (![0, 2] : Fin 2 → ℝ) 0
    (fun _ => Set.mem_univ _)

end MathlibExtTest.Economics.Risk.FairInsurance
