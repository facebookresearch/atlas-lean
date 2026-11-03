/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalMutualInformation

@[expose] public section

/-!
# Tests for conditional mutual information

The XOR law: `X`, `Y` independent fair bits and `Z = X xor Y`. Then `I(X; Y) = 0` but
`I(X; Y | Z) = 1` bit, so conditioning can increase mutual information, and the chain rule reads
`I(X; (Y, Z)) = I(X; Z) + I(X; Y | Z) = I(X; Z) + 1`. The Markov hypothesis of the
data-processing inequality is satisfiable (non-vacuity): a deterministic law meets it.
-/

open MeasureTheory Real InformationTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.ConditionalMutualInformation

/-- `X`, `Y` independent fair bits and `Z = X xor Y`. -/
noncomputable def xorLaw : PMF (Bool × Bool × Bool) :=
  PMF.ofFintype (fun t ↦ if t.2.2 = xor t.1 t.2.1 then ((1 / 4 : ℝ≥0) : ℝ≥0∞) else 0) (by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num
    rw [show (4 : ℝ≥0∞)⁻¹ + 4⁻¹ + (4⁻¹ + 4⁻¹) = 4 * 4⁻¹ by ring,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)])

theorem xorLaw_apply (t : Bool × Bool × Bool) :
    (xorLaw t).toReal = if t.2.2 = xor t.1 t.2.1 then 1 / 4 else 0 := by
  by_cases h : t.2.2 = xor t.1 t.2.1 <;> simp [xorLaw, h]

theorem toReal_map_apply {τ δ : Type*} [Fintype τ] [DecidableEq δ] (p : PMF τ) (f : τ → δ) (d : δ) :
    ((p.map f) d).toReal = ∑ t, if f t = d then (p t).toReal else 0 := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum fun t _ ↦ by
    split_ifs <;> simp [PMF.apply_ne_top]]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  by_cases h : f t = d
  · simp [h]
  · simp [h, Ne.symm h]

theorem negMulLog_quarter : negMulLog (1 / 4) = log 2 / 2 := by
  rw [negMulLog, show (4 : ℝ) = 2 ^ 2 by norm_num, one_div, log_inv, log_pow]
  ring

theorem negMulLog_half : negMulLog (1 / 2) = log 2 / 2 := by
  rw [negMulLog, one_div, log_inv]
  ring

theorem shannonEntropy_xorLaw : shannonEntropy xorLaw = 2 := by
  rw [shannonEntropy]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, xorLaw_apply]
  norm_num [negMulLog_quarter]
  field_simp
  ring

theorem shannonEntropy_xorLaw_xz : shannonEntropy (xorLaw.map fun t ↦ (t.1, t.2.2)) = 2 := by
  rw [shannonEntropy]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, toReal_map_apply, xorLaw_apply]
  norm_num [negMulLog_quarter]
  field_simp
  ring

theorem shannonEntropy_xorLaw_yz : shannonEntropy (xorLaw.map fun t ↦ t.2) = 2 := by
  rw [shannonEntropy]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, toReal_map_apply, xorLaw_apply]
  norm_num [negMulLog_quarter]
  field_simp
  ring

theorem shannonEntropy_xorLaw_xy : shannonEntropy (xorLaw.map fun t ↦ (t.1, t.2.1)) = 2 := by
  rw [shannonEntropy]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, toReal_map_apply, xorLaw_apply]
  norm_num [negMulLog_quarter]
  field_simp
  ring

theorem shannonEntropy_xorLaw_bit (f : Bool × Bool × Bool → Bool)
    (hf : f = (fun t ↦ t.1) ∨ f = (fun t ↦ t.2.1) ∨ f = (fun t ↦ t.2.2)) :
    shannonEntropy (xorLaw.map f) = 1 := by
  rw [shannonEntropy]
  rcases hf with rfl | rfl | rfl <;>
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool, toReal_map_apply, xorLaw_apply]
    norm_num [negMulLog_half]

/-- `X` and `Y` are independent: `I(X; Y) = 0`. -/
example : finiteMutualInformation (xorLaw.map fun t ↦ (t.1, t.2.1)) = 0 := by
  rw [finiteMutualInformation_eq, PMF.map_comp, PMF.map_comp]
  simp only [Function.comp_def]
  rw [shannonEntropy_xorLaw_bit _ (Or.inl rfl), shannonEntropy_xorLaw_bit _ (Or.inr (Or.inl rfl)),
    shannonEntropy_xorLaw_xy]
  norm_num

/-- Given `Z = X xor Y`, `X` determines `Y`: `I(X; Y | Z) = 1` bit. -/
theorem cmi_xorLaw : finiteConditionalMutualInformation xorLaw = 1 := by
  rw [finiteConditionalMutualInformation_eq, shannonEntropy_xorLaw_xz, shannonEntropy_xorLaw_yz,
    shannonEntropy_xorLaw, shannonEntropy_xorLaw_bit _ (Or.inr (Or.inr rfl))]
  norm_num

/-- Chain rule on the XOR law: `I(X; (Y, Z)) = I(X; Z) + I(X; Y | Z)`. -/
example : finiteMutualInformation xorLaw =
    finiteMutualInformation (xorLaw.map fun t ↦ (t.1, t.2.2)) + 1 := by
  rw [finiteMutualInformation_chain_rule, cmi_xorLaw]

/-- The deterministic law satisfies the Markov condition, so the data-processing inequality
applies to it. -/
example (a b c : Bool) :
    finiteMutualInformation ((PMF.pure (a, b, c)).map fun t ↦ (t.1, t.2.2)) ≤
      finiteMutualInformation ((PMF.pure (a, b, c)).map fun t ↦ (t.1, t.2.1)) := by
  refine finiteMutualInformation_le_left_of_markov _ ?_
  rw [finiteConditionalMutualInformation_eq]
  simp [PMF.pure_map]

end MathlibExtTest.InformationTheory.ConditionalMutualInformation
