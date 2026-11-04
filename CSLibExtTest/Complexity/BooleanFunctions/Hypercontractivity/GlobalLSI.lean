/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.GlobalLSI

/-!
# Tests for the log-Sobolev inequality on the `p`-biased hypercube

Tests for `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.GlobalLSI`, at the dictator
`ω ↦ ω 0` on `{0, 1}^{Fin 1}` and at constants:

* `bph_deriv` is `1` everywhere for the dictator and `0` for constants;
* `gls_entCoord_le_deriv_sq` at the dictator, `p = 1/2`;
* `gls_globalLSI` at the dictator: the entropy of `f²` is `-p log p` and the Dirichlet sum is `1`,
  so the theorem yields `-p log p ≤ 1` for every `p ∈ (0, 1)`, in particular `log 2 / 2 ≤ 1` at
  `p = 1/2`;
* `gls_globalLSI_weighted` at the dictator, `p = 1/2`, where the right side evaluates to `1`.

All hypotheses of these theorems are `0 < p < 1`; there is no conditional predicate to test.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.GlobalLSI

open StatMech StatMech.OSSS StatMech.Probability

/-- A sum over the configurations of `{0, 1}^{Fin 1}`. -/
lemma sum_fin_one (f : ConfigSpace (Fin 1) → ℝ) :
    ∑ ω, f ω = f (fun _ => true) + f (fun _ => false) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  rfl

/-- The dictator `ω ↦ ω 0` on `{0, 1}^{Fin 1}`, as a real function. -/
noncomputable def dict1 (ω : ConfigSpace (Fin 1)) : ℝ := if ω 0 then 1 else 0

/-- The discrete derivative of the dictator is identically `1`. -/
lemma bph_deriv_dict1 (ω : ConfigSpace (Fin 1)) : bph_deriv dict1 0 ω = 1 := by
  simp [bph_deriv, dict1, setOpen, setClosed]

example (c : ℝ) (e : Fin 2) (ω : ConfigSpace (Fin 2)) : bph_deriv (fun _ => c) e ω = 0 := by
  simp [bph_deriv]

/-- The Dirichlet sum of the dictator is `1` for every `p`. -/
lemma dirichlet_dict1 (p : ℝ) :
    ∑ e : Fin 1, expect (bernoulliWeight p) (fun ω => (bph_deriv dict1 e ω) ^ 2) = 1 := by
  simp [bph_deriv_dict1, expect, weight, sum_fin_one, bernoulliWeight]

/-- The entropy of the (squared) dictator is `-p log p`. -/
lemma ent_dict1 (p : ℝ) :
    esd_ent (bernoulliWeight p) (fun ω => (dict1 ω) ^ 2) = -(p * Real.log p) := by
  simp [esd_ent, expect, weight, sum_fin_one, dict1, bernoulliWeight, esd_Phi]

example (ω : ConfigSpace (Fin 1)) :
    esd_entCoord (1 / 2) (fun ω => (dict1 ω) ^ 2) 0 ω ≤ 1 := by
  have h := gls_entCoord_le_deriv_sq (p := 1 / 2) (by norm_num) (by norm_num) dict1 0 ω
  rwa [bph_deriv_dict1, one_pow] at h

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : -(p * Real.log p) ≤ 1 := by
  have h := gls_globalLSI hp0 hp1 dict1
  rwa [ent_dict1, dirichlet_dict1] at h

example : Real.log 2 / 2 ≤ 1 := by
  have h := gls_globalLSI (p := 1 / 2) (by norm_num) (by norm_num) dict1
  rw [ent_dict1, dirichlet_dict1, one_div, Real.log_inv] at h
  linarith

example : esd_ent (bernoulliWeight (1 / 2)) (fun ω => (dict1 ω) ^ 2) ≤ 1 := by
  have h := gls_globalLSI_weighted (p := 1 / 2) (by norm_num) (by norm_num) dict1
  simp only [Fin.sum_univ_one, bph_deriv_dict1] at h
  norm_num [expect, weight, sum_fin_one, bernoulliWeight] at h
  exact h

end StatMechTest.BooleanFunctions.GlobalLSI
