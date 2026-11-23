/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.PBiasedTensorize
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.BourgainPerCoord

/-!
# Tests for `p`-biased Fourier analysis and hypercontractivity

Tests for `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.PBiasedTensorize` at the `AND`
function on `{0, 1}^Bool`, for every `p ∈ (0, 1)`:

* `ptn_val`, `ptn_sigma`, `ptn_psi`, `ptn_pchar` and the four `p`-biased coefficients of `AND`
  (`ptn_coeff`), with squares `p⁴`, `p³(1-p)`, `p³(1-p)`, `p²(1-p)²`;
* `ptn_var_eq_fourierWeight` and `ptn_totalInfl_eq_fourierWeight` agree with the direct
  computations `Var_p(AND) = p²(1-p²)` and `∑ₑ Infₑ(AND) = 2p`;
* `ptn_hypercontractivity_fin`, `ptn_lowDegreeWeight` and `ptn_capped_hc` instantiated at
  `p = 3/4`, `q = 2`, `ρ = √3/2`, a point where the noise constraint `ρ² = (q-1) 4p(1-p)` is
  satisfied with `ρ > 0`;
* `ptn_kop_eq_noiseOp`, `ptn_rhoOptimise_c0`;
* `ptn_RhoOptimise q` for `q ≤ 1/2` holds because the parameter interval `(1/2, q)` is empty;
  this library proves it for no `q > 1/2`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

example : ptn_val true = 1 ∧ ptn_val false = 0 := ⟨rfl, rfl⟩

example : ptn_sigma (1 / 2) = 1 / 2 := by
  rw [ptn_sigma, show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

example : ptn_sigma (3 / 4) ^ 2 = 3 / 16 := by rw [ptn_sigma_sq] <;> norm_num

example (ω : ConfigSpace Bool) : ptn_pchar (3 / 4 : ℝ) ∅ ω = 1 := by simp

lemma ptn_psi_true_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ptn_psi p true ^ 2 = (1 - p) / p := by
  rw [ptn_psi, div_pow, ptn_sigma_sq hp0 hp1]
  simp
  field_simp

lemma ptn_psi_false_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ptn_psi p false ^ 2 = p / (1 - p) := by
  have : 0 < 1 - p := by linarith
  rw [ptn_psi, div_pow, ptn_sigma_sq hp0 hp1]
  simp
  field_simp

lemma ptn_coeff_andInd_empty (p : ℝ) : ptn_coeff p andInd ∅ = p * p := by
  simp [ptn_coeff, expect, weight, sum_configSpace_bool, andFun, bernoulliWeight]

lemma ptn_coeff_andInd_true (p : ℝ) : ptn_coeff p andInd {true} = p * p * ptn_psi p true := by
  simp [ptn_coeff, ptn_pchar, expect, weight, sum_configSpace_bool, andFun, bernoulliWeight]

lemma ptn_coeff_andInd_false (p : ℝ) : ptn_coeff p andInd {false} = p * p * ptn_psi p true := by
  simp [ptn_coeff, ptn_pchar, expect, weight, sum_configSpace_bool, andFun, bernoulliWeight]

lemma ptn_coeff_andInd_univ (p : ℝ) :
    ptn_coeff p andInd {true, false} = p * p * (ptn_psi p true * ptn_psi p true) := by
  simp [ptn_coeff, ptn_pchar, expect, weight, sum_configSpace_bool, andFun, bernoulliWeight]

/-- The `p`-biased Fourier weight of `AND` on nonempty sets, from the coefficients above. -/
lemma ptn_weight_andInd {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∑ S ∈ Finset.univ.erase (∅ : Finset Bool), (ptn_coeff p andInd S) ^ 2
      = p ^ 2 * (1 - p ^ 2) := by
  rw [sum_erase_empty_finset_bool, ptn_coeff_andInd_true, ptn_coeff_andInd_false,
    ptn_coeff_andInd_univ]
  have h := ptn_psi_true_sq hp0 hp1
  have e : (p * p * (ptn_psi p true * ptn_psi p true)) ^ 2 = p ^ 4 * (ptn_psi p true ^ 2) ^ 2 := by
    ring
  rw [mul_pow, e, h]
  field_simp
  ring

lemma ptn_coeff_andInd_empty_sq (p : ℝ) : (ptn_coeff p andInd ∅) ^ 2 = p ^ 4 := by
  rw [ptn_coeff_andInd_empty]; ring

lemma ptn_coeff_andInd_true_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (ptn_coeff p andInd {true}) ^ 2 = p ^ 3 * (1 - p) := by
  rw [ptn_coeff_andInd_true, mul_pow, ptn_psi_true_sq hp0 hp1]; field_simp

lemma ptn_coeff_andInd_false_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (ptn_coeff p andInd {false}) ^ 2 = p ^ 3 * (1 - p) := by
  rw [ptn_coeff_andInd_false, mul_pow, ptn_psi_true_sq hp0 hp1]; field_simp

lemma ptn_coeff_andInd_univ_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (ptn_coeff p andInd {true, false}) ^ 2 = p ^ 2 * (1 - p) ^ 2 := by
  have e : (p * p * (ptn_psi p true * ptn_psi p true)) ^ 2 = p ^ 4 * (ptn_psi p true ^ 2) ^ 2 := by
    ring
  rw [ptn_coeff_andInd_univ, e, ptn_psi_true_sq hp0 hp1]; field_simp

/-- Direct computation of `Var_p(AND)`. -/
lemma var_andInd (p : ℝ) : var (bernoulliWeight p) andInd = p ^ 2 * (1 - p ^ 2) := by
  simp [var, cov, expect, weight, sum_configSpace_bool, andFun, bernoulliWeight]
  ring

/-- `ptn_var_eq_fourierWeight` reproduces `Var_p(AND) = p²(1-p²)`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    var (bernoulliWeight p) andInd = p ^ 2 * (1 - p ^ 2) := by
  rw [ptn_var_eq_fourierWeight hp0 hp1, ptn_weight_andInd hp0 hp1]

/-- Direct computation of the influences of `AND` under `μ_p`. -/
lemma infl_andInd (p : ℝ) (e : Bool) : infl (bernoulliWeight p) andInd e = p := by
  cases e <;>
  · simp [infl, expect, weight, sum_configSpace_bool, andInd, andFun, bernoulliWeight, setOpen,
      setClosed]
    ring

lemma totalInfl_andInd_p (p : ℝ) : totalInfl (bernoulliWeight p) andInd = 2 * p := by
  rw [totalInfl, Fintype.sum_bool, infl_andInd, infl_andInd]; ring

lemma maxInfl_andInd_p (p : ℝ) : maxInfl (bernoulliWeight p) andInd = p := by
  unfold maxInfl
  rw [show infl (bernoulliWeight p) andInd = fun _ => p from funext (infl_andInd p)]
  exact Finset.sup'_const _ _

/-- `ptn_totalInfl_eq_fourierWeight` reproduces `∑ₑ Infₑ(AND) = 2p`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset Bool, (S.card : ℝ) * (ptn_coeff p andInd S) ^ 2
      = 2 * p := by
  rw [sum_finset_bool, ptn_coeff_andInd_empty, ptn_coeff_andInd_true, ptn_coeff_andInd_false,
    ptn_coeff_andInd_univ, ptn_sigma_sq hp0 hp1]
  have h := ptn_psi_true_sq hp0 hp1
  have : 0 < 1 - p := by linarith
  have e : (p * p * (ptn_psi p true * ptn_psi p true)) ^ 2 = p ^ 4 * (ptn_psi p true ^ 2) ^ 2 := by
    ring
  rw [mul_pow (p * p), e, h]
  simp
  field_simp
  ring

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    totalInfl (bernoulliWeight p) andInd
      = (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset Bool, (S.card : ℝ) * (ptn_coeff p andInd S) ^ 2 :=
  ptn_totalInfl_eq_fourierWeight hp0 hp1 andFun

/-! ## Hypercontractivity at a nondegenerate point -/

lemma rho_sq : (Real.sqrt 3 / 2) ^ 2 = (2 - 1) * 4 * (3 / 4 : ℝ) * (1 - 3 / 4) := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma rho_le_one : Real.sqrt 3 / 2 ≤ 1 := by
  rw [div_le_one (by norm_num), Real.sqrt_le_left (by norm_num)]; norm_num

example (f : (Fin 2 → Bool) → ℝ) :
    ptn_qnorm (3 / 4) 2 (ptn_kop (3 / 4) (Real.sqrt 3 / 2) f) ≤ ptn_qnorm (3 / 4) 2 f :=
  ptn_hypercontractivity_fin (by norm_num) (by norm_num) (by positivity) rho_le_one
    (by norm_num) le_rfl rho_sq 2 f

example (f : ConfigSpace Bool → ℝ) :
    (∑ S : Finset Bool, ((Real.sqrt 3 / 2) ^ S.card) ^ 2 * (ptn_coeff (3 / 4) f S) ^ 2)
      ≤ (ptn_qnorm (3 / 4) 2 f) ^ 2 :=
  ptn_lowDegreeWeight (by norm_num) (by norm_num) (by positivity) rho_le_one (by norm_num) le_rfl
    rho_sq f

example :
    (1 / (ptn_sigma (3 / 4)) ^ 2) * ∑ S : Finset Bool, (S.card : ℝ)
        * (((Real.sqrt 3 / 2) ^ (S.card - 1)) ^ 2 * (ptn_coeff (3 / 4) andInd S) ^ 2)
      ≤ (maxInfl (bernoulliWeight (3 / 4)) andInd) ^ (2 / 2 - 1 : ℝ)
        * totalInfl (bernoulliWeight (3 / 4)) andInd :=
  ptn_capped_hc (by norm_num) (by norm_num) (by positivity) rho_le_one (by norm_num) le_rfl
    rho_sq andFun

example (ρ : ℝ) (f : ConfigSpace Bool → ℝ) : ptn_kop (3 / 4) ρ f = ptn_noiseOp (3 / 4) ρ f :=
  ptn_kop_eq_noiseOp (by norm_num) (by norm_num) ρ f

/-! ## The predicate `ptn_RhoOptimise` -/

/-- For `q ≤ 1/2` the predicate is vacuous: no `p` lies in `(1/2, q)`. -/
lemma ptn_rhoOptimise_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : ptn_RhoOptimise q := by
  intro p hp
  exact absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : kpb_PBiasedHC (1 / 2) :=
  ptn_PBiasedHC_of_rhoOptimise (by norm_num) (ptn_rhoOptimise_of_le_half le_rfl)

example : (0 : ℝ) * var (bernoulliWeight (3 / 4)) andInd
      * Real.log (1 / maxInfl (bernoulliWeight (3 / 4)) andInd)
    ≤ totalInfl (bernoulliWeight (3 / 4)) andInd :=
  ptn_rhoOptimise_c0 (by norm_num) (by norm_num) andFun

end StatMechTest.BooleanFunctions
