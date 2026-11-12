/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.RealOptionValue
import Mathlib.Tactic

/-!
# Tests for real option value

Tests for the real option value: a two-action two-state example with exact
values (`13/2` vs commitments `3` and `5`), the singleton equality case, and the
zero-weights case.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.RealOptionValue

open MathlibExt.Economics.Finance.RealOptionValue

/-- Test 1a: two actions, two states. The statewise maxima are `10` (at `true`) and `3`
(at `false`), so the option value is their average `13 / 2`. -/
example (hne : (({1, 2} : Finset ℕ).Nonempty)) :
    optionValue {1, 2} hne (fun _ : Bool => (1 / 2 : ℝ))
      (fun a b => if a = 1 then (3 : ℝ) else if b then 10 else 0) = 13 / 2 := by
  have hT : (({1, 2} : Finset ℕ).sup' hne
      (fun a => (if a = 1 then (3 : ℝ) else if True then 10 else 0))) = 10 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> simp; norm_num
    · have h2 : (2 : ℕ) ∈ ({1, 2} : Finset ℕ) := by simp
      calc (10 : ℝ)
          = (fun a => (if a = 1 then (3 : ℝ) else if True then 10 else 0)) 2 := by simp
        _ ≤ _ := Finset.le_sup'
          (fun a => (if a = 1 then (3 : ℝ) else if True then 10 else 0)) h2
  have hF : (({1, 2} : Finset ℕ).sup' hne
      (fun a => (if a = 1 then (3 : ℝ) else if (false : Bool) then 10 else 0))) = 3 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> simp
    · have h1 : (1 : ℕ) ∈ ({1, 2} : Finset ℕ) := by simp
      calc (3 : ℝ)
          = (fun a => (if a = 1 then (3 : ℝ) else if (false : Bool) then 10 else 0)) 1 := by simp
        _ ≤ _ := Finset.le_sup'
          (fun a => (if a = 1 then (3 : ℝ) else if (false : Bool) then 10 else 0)) h1
  simp only [optionValue, finiteExpectedValue, Fintype.sum_bool, hT, hF]
  norm_num

/-- Test 1b: committing to action `1` yields expected value `3`. -/
example : finiteExpectedValue (fun _ : Bool => (1 / 2 : ℝ))
    ((fun a b => if a = 1 then (3 : ℝ) else if b then 10 else 0) 1) = 3 := by
  have h1 : ((fun a b => if a = 1 then (3 : ℝ) else if b then 10 else 0) 1)
      = (fun _ : Bool => (3 : ℝ)) := by
    funext b
    simp
  rw [h1]
  simp only [finiteExpectedValue, Fintype.sum_bool]
  norm_num

/-- Test 1c: committing to action `2` yields expected value `5`. -/
example : finiteExpectedValue (fun _ : Bool => (1 / 2 : ℝ))
    ((fun a b => if a = 1 then (3 : ℝ) else if b then 10 else 0) 2) = 5 := by
  have h2 : ((fun a b => if a = 1 then (3 : ℝ) else if b then 10 else 0) 2)
      = (fun b : Bool => if b then (10 : ℝ) else 0) := by
    funext b
    simp
  rw [h2]
  simp only [finiteExpectedValue, Fintype.sum_bool, ite_true]
  norm_num

/-- Test 2 (equality case): with a single feasible action, the option value equals the
committed expected value. -/
example (hne : (({1} : Finset ℕ).Nonempty)) :
    optionValue {1} hne (fun _ : Bool => (1 / 2 : ℝ))
      (fun a b => if a = 1 then (3 : ℝ) else if b then 10 else 0)
      = finiteExpectedValue (fun _ : Bool => (1 / 2 : ℝ))
        ((fun a b => if a = 1 then (3 : ℝ) else if b then 10 else 0) 1) := rfl

/-- Test 3: with zero weights, the option value is `0` (no positivity of weights used). -/
example (hne : (({1, 2} : Finset ℕ).Nonempty)) :
    optionValue {1, 2} hne (fun _ : Bool => (0 : ℝ))
      (fun a b => if a = 1 then (3 : ℝ) else if b then 10 else 0) = 0 := by
  simp [optionValue, finiteExpectedValue]


end MathlibExtTest.Economics.Finance.RealOptionValue
