/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.BinomialOptimalStopping
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Finance.BinomialOptimalStopping

open MathlibExt.Economics.Finance.BinomialOptimalStopping

example (g : List Bool → ℝ) (s : List Bool) : snell (1/2) 1 g 0 s = g s := rfl

def g₁ : List Bool → ℝ := fun s => if s = [] then 1 else if s = [false] then 3 else 0

example : snell (1/2) 1 g₁ 1 [] = 3/2 := by
  simp only [snell, continuation, snell, g₁]
  simp
  have h : ((1 - 2⁻¹) * 3 : ℝ) = 3/2 := by norm_num
  rw [h]
  exact max_eq_right (by norm_num)

example : ruleValue (1/2) 1 g₁ (fun _ _ => true) 1 [] = 1 := by
  simp [ruleValue, g₁]

example : ruleValue (1/2) 1 g₁ (snellRule (1/2) 1 g₁) 1 [] = 3/2 := by
  rw [ruleValue_snellRule]
  simp only [snell, continuation, snell, g₁]
  simp
  have h : ((1 - 2⁻¹) * 3 : ℝ) = 3/2 := by norm_num
  rw [h]
  exact max_eq_right (by norm_num)

noncomputable def g₂ : List Bool → ℝ := fun s => (s.count false : ℝ) - (s.length : ℝ) / 3

example : snell (1/2) (9/10) g₂ 2 [] = 27/100 := by
  have h1 : snell (1/2) (9/10) g₂ 1 [true] = -3/20 := by
    simp only [snell, continuation, snell, g₂]
    simp
    have hcont : (9/10 : ℝ) * (-(2⁻¹*(2/3)) + (1-2⁻¹)*(1-2/3)) = -3/20 := by norm_num
    rw [hcont]
    exact max_eq_right (by norm_num)
  have h2 : snell (1/2) (9/10) g₂ 1 [false] = 3/4 := by
    simp only [snell, continuation, snell, g₂]
    simp
    have hcont : (9/10 : ℝ) * (2⁻¹*(1-2/3) + (1-2⁻¹)*(2-2/3)) = 3/4 := by norm_num
    rw [hcont]
    exact max_eq_right (by norm_num)
  have h0 : g₂ [] = 0 := by simp [g₂]
  have houter : snell (1/2) (9/10) g₂ 2 [] =
      max (g₂ []) ((9/10 : ℝ) * ((1/2 : ℝ) * snell (1/2) (9/10) g₂ 1 [true] +
        (1 - 1/2) * snell (1/2) (9/10) g₂ 1 [false])) := rfl
  rw [houter, h0, h1, h2]
  have hcont : (9/10 : ℝ) * ((1/2 : ℝ) * (-3/20) + (1 - 1/2) * (3/4)) = 27/100 := by norm_num
  rw [hcont]
  exact max_eq_right (by norm_num)

example : IsGreatest (Set.range fun stop : ℕ → List Bool → Bool => ruleValue (1/2) (9/10) g₂ stop 2 []) (27/100) := by
  have hsnell : snell (1/2) (9/10) g₂ 2 [] = 27/100 := by
    have h1 : snell (1/2) (9/10) g₂ 1 [true] = -3/20 := by
      simp only [snell, continuation, snell, g₂]
      simp
      have hcont : (9/10 : ℝ) * (-(2⁻¹*(2/3)) + (1-2⁻¹)*(1-2/3)) = -3/20 := by norm_num
      rw [hcont]
      exact max_eq_right (by norm_num)
    have h2 : snell (1/2) (9/10) g₂ 1 [false] = 3/4 := by
      simp only [snell, continuation, snell, g₂]
      simp
      have hcont : (9/10 : ℝ) * (2⁻¹*(1-2/3) + (1-2⁻¹)*(2-2/3)) = 3/4 := by norm_num
      rw [hcont]
      exact max_eq_right (by norm_num)
    have h0 : g₂ [] = 0 := by simp [g₂]
    have houter : snell (1/2) (9/10) g₂ 2 [] =
        max (g₂ []) ((9/10 : ℝ) * ((1/2 : ℝ) * snell (1/2) (9/10) g₂ 1 [true] +
          (1 - 1/2) * snell (1/2) (9/10) g₂ 1 [false])) := rfl
    rw [houter, h0, h1, h2]
    have hcont : (9/10 : ℝ) * ((1/2 : ℝ) * (-3/20) + (1 - 1/2) * (3/4)) = 27/100 := by norm_num
    rw [hcont]
    exact max_eq_right (by norm_num)
  rw [← hsnell]
  exact isGreatest_snell (by norm_num) (by norm_num) (by norm_num) g₂ 2

noncomputable def g₃ : List Bool → ℝ := fun s => if s = [true] then 1/3 else if s = [false, true] then 1 else 0

example : g₃ [false, true] ≠ g₃ [true, false] := by
  simp [g₃]

theorem snell_g₃_up : snell (1/2) 1 g₃ 1 [true] = 1/2 := by
  have e1 : g₃ [true] = 1/3 := by simp [g₃]
  have e2 : g₃ [true, true] = 0 := by simp [g₃]
  have e3 : g₃ [false, true] = 1 := by simp [g₃]
  have h : snell (1/2) 1 g₃ 1 [true] =
      max (g₃ [true]) ((1:ℝ) * ((1/2:ℝ) * g₃ [true, true] + (1 - 1/2) * g₃ [false, true])) := rfl
  rw [h, e1, e2, e3]
  have hcont : (1:ℝ) * ((1/2:ℝ) * 0 + (1 - 1/2) * 1) = 1/2 := by norm_num
  rw [hcont]
  exact max_eq_right (by norm_num)

example : snell (1/2) 1 g₃ 1 [true] = 1/2 := snell_g₃_up

theorem snell_g₃_down : snell (1/2) 1 g₃ 1 [false] = 0 := by
  have e1 : g₃ [false] = 0 := by simp [g₃]
  have e2 : g₃ [true, false] = 0 := by simp [g₃]
  have e3 : g₃ [false, false] = 0 := by simp [g₃]
  have h : snell (1/2) 1 g₃ 1 [false] =
      max (g₃ [false]) ((1:ℝ) * ((1/2:ℝ) * g₃ [true, false] + (1 - 1/2) * g₃ [false, false])) := rfl
  rw [h, e1, e2, e3]
  have hcont : (1:ℝ) * ((1/2:ℝ) * 0 + (1 - 1/2) * 0) = 0 := by norm_num
  rw [hcont]
  exact max_eq_right (by norm_num)

theorem snell_g₃_two : snell (1/2) 1 g₃ 2 [] = 1/4 := by
  have h0 : g₃ [] = 0 := by simp [g₃]
  have houter : snell (1/2) 1 g₃ 2 [] =
      max (g₃ []) ((1:ℝ) * ((1/2:ℝ) * snell (1/2) 1 g₃ 1 [true] +
        (1 - 1/2) * snell (1/2) 1 g₃ 1 [false])) := rfl
  rw [houter, h0, snell_g₃_up, snell_g₃_down]
  have hcont : (1:ℝ) * ((1/2:ℝ) * (1/2) + (1 - 1/2) * 0) = 1/4 := by norm_num
  rw [hcont]
  exact max_eq_right (by norm_num)

example : snell (1/2) 1 g₃ 2 [] = 1/4 := snell_g₃_two

example : IsGreatest (Set.range fun stop : ℕ → List Bool → Bool => ruleValue (1/2) 1 g₃ stop 2 []) (1/4) := by
  rw [← snell_g₃_two]
  exact isGreatest_snell (by norm_num) (by norm_num) (by norm_num) g₃ 2

example : ruleValue (1/2) 1 g₃ (fun _ _ => true) 2 [] = 0 := by
  simp [ruleValue, g₃]

end MathlibExtTest.Economics.Finance.BinomialOptimalStopping
