/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.Separations.StageSteppingPinch
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact stage-stepping pinch example

The article's example has relative volatility `2`, reflux ratio `1`, and distillate composition
`3/4`. Its pinch is the smaller root of `4*x^2 - 9*x + 3 = 0`.
-/

open Set
open scoped Function

noncomputable section

namespace Chemistry.Separations

private def pinch : ℝ := (9 - Real.sqrt 33) / 8
private def equilibrium (x : ℝ) : ℝ := 2 * x / (1 + x)
private def operating (x : ℝ) : ℝ := (x + 3 / 4) / 2
private def inverse (y : ℝ) : ℝ := y / (2 - y)
private def step : ℝ → ℝ := inverse ∘ operating

private lemma pinch_bounds : pinch ∈ Ico (0 : ℝ) (3 / 5) := by
  have hlo : (5 : ℝ) < Real.sqrt 33 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hhi : Real.sqrt 33 < (9 : ℝ) := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  exact ⟨by dsimp [pinch]; linarith, by dsimp [pinch]; linarith⟩

private lemma pinch_polynomial : 4 * pinch ^ 2 - 9 * pinch + 3 = 0 := by
  dsimp [pinch]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 33 by norm_num)]

private lemma operating_pinch : operating pinch = equilibrium pinch := by
  have hp : 0 ≤ pinch := pinch_bounds.1
  dsimp [operating, equilibrium]
  apply (div_eq_div_iff (by norm_num) (by linarith)).2
  nlinarith [pinch_polynomial]

private lemma operating_lt_equilibrium (x : ℝ) (hx : x ∈ Ioc pinch (3 / 5)) :
    operating x < equilibrium x := by
  have hp : 0 ≤ pinch := pinch_bounds.1
  have hpx : pinch < x := hx.1
  have hfactor : 4 * (x - pinch) * (x + pinch - 9 / 4) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (by norm_num) (sub_pos.mpr hpx))
      (by linarith [hx.2, pinch_bounds.2])
  dsimp [operating, equilibrium]
  apply (div_lt_div_iff₀ (by norm_num) (by linarith)).2
  nlinarith [pinch_polynomial, hfactor]

-- The start is the inverse at the specified distillate composition, and the first step is exact.
example : inverse (3 / 4) = 3 / 5 ∧ step (3 / 5) = 27 / 53 := by
  norm_num [step, Function.comp_apply, operating, inverse]

example :
    let unit := Icc (0 : ℝ) 1
    MapsTo step unit unit ∧ InvOn inverse equilibrium unit unit ∧ StrictMonoOn step unit ∧
      step pinch = pinch ∧ (∀ x ∈ Ioc pinch (3 / 5), operating x < equilibrium x) ∧
      (∀ x ∈ Ioc pinch (3 / 5), pinch < step x ∧ step x < x) ∧
      (∀ n : ℕ, (step^[n]) (3 / 5) ∈ Ioc pinch (3 / 5)) ∧
      StrictAnti (fun n : ℕ ↦ (step^[n]) (3 / 5)) := by
  have h := stageStepping_cannotCrossPinch (α := 2) (R := 1) (xD := 3 / 4)
    (xp := pinch) (x₀ := 3 / 5) (by norm_num) (by norm_num)
    (by constructor <;> norm_num) pinch_bounds.1 pinch_bounds.2 (by norm_num)
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, one_mul, show (1 : ℝ) + 1 = 2 by norm_num] at h
  obtain ⟨_, hOperating, hInverse, hInvOn, hMono, hIterates⟩ := h
  have hfixed : step pinch = pinch := by
    change inverse (operating pinch) = pinch
    rw [operating_pinch]
    exact hInvOn.1 ⟨pinch_bounds.1, pinch_bounds.2.le.trans (by norm_num)⟩
  exact ⟨hInverse.comp hOperating, hInvOn, hMono, hfixed, operating_lt_equilibrium,
    hIterates hfixed operating_lt_equilibrium⟩

end Chemistry.Separations
