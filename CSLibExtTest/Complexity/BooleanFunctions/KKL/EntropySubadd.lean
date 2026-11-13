/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.EntropySubadd
public import CSLibExtTest.Complexity.BooleanFunctions.OSSS

/-!
# Tests for the sub-additivity of entropy

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.EntropySubadd`:

* `esd_Phi` at `0`, `1` and `1/2`, and the bridge `esd_Phi_eq_neg_negMulLog`;
* `esd_ent` vanishes on constants;
* `esd_PosWeight` holds for the Bernoulli(`p`) weight with `0 < p < 1` (`esd_bernoulli_pos`) and
  fails at `p = 0`;
* `esd_subadditivity` for the coordinate function `g(ω) = ω 0` on `{0, 1}^{Fin 1}`: both sides
  equal `-p log p` for every `p ∈ (0, 1)`, so the inequality is attained;
* `esd_dpi` instantiated at the uniform weight.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

example : esd_Phi 0 = 0 := esd_Phi_zero
example : esd_Phi 1 = 0 := by simp [esd_Phi]
example : esd_Phi (1 / 2) = -(1 / 2) * Real.log 2 := by
  simp [esd_Phi, Real.log_inv]
example (x : ℝ) : esd_Phi x = -Real.negMulLog x := esd_Phi_eq_neg_negMulLog x

example (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    esd_ent (bernoulliWeight p) (fun _ : ConfigSpace Bool => c) = 0 := by
  have h := expect_one (bernoulliWeight_isProbWeight (E := Bool) hp0 hp1)
  have hc : expect (bernoulliWeight p) (fun _ : ConfigSpace Bool => c) = c := by
    have := expect_const_mul (bernoulliWeight (E := Bool) p) c (fun _ => 1)
    simpa [h] using this
  rw [esd_ent, hc]
  have := expect_const_mul (bernoulliWeight (E := Bool) p) (esd_Phi c) (fun _ => 1)
  simp only [mul_one] at this
  rw [this, h, mul_one, sub_self]

example : esd_PosWeight (E := Bool) (bernoulliWeight (1 / 3)) :=
  esd_bernoulli_pos (by norm_num) (by norm_num)

example : ¬ esd_PosWeight (E := Bool) (bernoulliWeight 0) := by
  intro h
  have := h true true
  simp [bernoulliWeight] at this

/-! ## Equality case of sub-additivity on one coordinate -/

/-- A sum over the configurations of `{0, 1}^{Fin 1}`. -/
lemma sum_configSpace_fin_one (f : (Fin 1 → Bool) → ℝ) :
    ∑ ω, f ω = f (fun _ => true) + f (fun _ => false) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  rfl

/-- The coordinate function `ω ↦ ω 0` on `{0, 1}^{Fin 1}`. -/
noncomputable def coordFun (ω : Fin 1 → Bool) : ℝ := if ω 0 then 1 else 0

lemma esd_ent_coordFun (p : ℝ) :
    esd_ent (bernoulliWeight p) coordFun = -(p * Real.log p) := by
  simp [esd_ent, expect, weight, sum_configSpace_fin_one, coordFun, bernoulliWeight, esd_Phi]

lemma esd_entCoord_sum_coordFun (p : ℝ) :
    ∑ e : Fin 1, expect (bernoulliWeight p) (esd_entCoord p coordFun e) = -(p * Real.log p) := by
  simp [esd_entCoord, expect, weight, sum_configSpace_fin_one, coordFun, bernoulliWeight,
    esd_Phi, condMean, setOpen, setClosed]
  ring

/-- `esd_subadditivity` at `coordFun`: `-p log p ≤ -p log p`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : -(p * Real.log p) ≤ -(p * Real.log p) := by
  have h := esd_subadditivity hp0 hp1 coordFun (fun ω => by unfold coordFun; split <;> norm_num)
  rw [esd_ent_coordFun, esd_entCoord_sum_coordFun] at h

example {g0 g1 : ConfigSpace Bool → ℝ} (hg0 : ∀ ω, 0 ≤ g0 ω) (hg1 : ∀ ω, 0 ≤ g1 ω) :
    (1 / 3) * esd_Phi (expect νHalf g1) + (1 - 1 / 3) * esd_Phi (expect νHalf g0)
        - esd_Phi ((1 / 3) * expect νHalf g1 + (1 - 1 / 3) * expect νHalf g0)
      ≤ expect νHalf (fun ω => (1 / 3) * esd_Phi (g1 ω) + (1 - 1 / 3) * esd_Phi (g0 ω)
          - esd_Phi ((1 / 3) * g1 ω + (1 - 1 / 3) * g0 ω)) :=
  esd_dpi (esd_bernoulli_pos (by norm_num) (by norm_num)) νHalf_isProbWeight (by norm_num)
    (by norm_num) hg0 hg1

end StatMechTest.BooleanFunctions
