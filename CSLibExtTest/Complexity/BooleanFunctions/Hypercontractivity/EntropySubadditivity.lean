/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.EntropySubadditivity
public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.CoupledTensorizeRefutations

/-!
# Tests for entropy subadditivity and the damping-hard route

Tests for `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.EntropySubadditivity`:

* `esa_dampedMass_le` at the dictator `ω ↦ ω 0` on `{0, 1}^{Fin 1}`;
* `esa_logBalance_threshold` at `p = 1/2`, where the threshold is `exp (-2)`;
* `esa_maxInfl_pos_of_var_pos` at the dictator (variance `1/4`);
* `esa_DampingHard` at the five-bit `AND` and `p = 11/20 ∈ (1/2, 1)`: all antecedents hold
  (positive variance, `0 < maxInfl = (11/20)⁴ < exp (-1/(2p(1-p)))`), and so does the conclusion,
  with `r = 1/7`. This uses the exact Fourier coefficients `p⁵ ψ_p(1)^|S|` and the closed form
  `pen_dampedMass p r = p¹⁰ ((1 + r(1-p)/p)⁵ - 1)`. So the predicate's body is neither vacuous
  nor false on this function;
* `esa_dampingHard_c0` at the dictator.

Not tested non-degenerately: `esa_DampingHard q` quantifies over all Boolean functions and all
`p ∈ (1/2, q)`; it is neither proved nor refuted for any `q > 1/2`. The conditional chain
(`esa_dampingWitness_of_hard`, `esa_rhoOptimise_of_hard`, `esa_kklHC_of_hard`,
`esa_PBiasedHC_of_hard`) is recorded at the degenerate window `q = 1/2`, where the predicate
holds because `(1/2, 1/2)` is empty.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.EntropySubadditivity

open StatMech StatMech.OSSS StatMech.Probability

/-- The dictator `ω ↦ ω 0` on `{0, 1}^{Fin 1}`. -/
def dict1 (ω : ConfigSpace (Fin 1)) : Bool := ω 0

/-- The variance of the dictator under `μ_p` is `p(1-p)`. -/
lemma var_dict1 (p : ℝ) :
    var (bernoulliWeight p) (fun ω => if dict1 ω then (1 : ℝ) else 0) = p * (1 - p) := by
  simp only [var, cov, ctc_expect_fin1, dict1]
  simp
  ring

example (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    pen_dampedMass (1 / 2) r (fun ω => if dict1 ω then (1 : ℝ) else 0)
      ≤ r * (∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin 1))),
          (ptn_coeff (1 / 2) (fun ω => if dict1 ω then (1 : ℝ) else 0) S) ^ 2) :=
  esa_dampedMass_le hr0 hr1 _

example : 0 < Real.exp (-2) ∧ Real.exp (-2) < 1
    ∧ 4 * ((1 / 2 : ℝ) * (1 - 1 / 2)) * Real.log (1 / Real.exp (-2)) = 2 := by
  have h := esa_logBalance_threshold (p := 1 / 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : 0 < maxInfl (bernoulliWeight (1 / 2)) (fun ω => if dict1 ω then (1 : ℝ) else 0) :=
  esa_maxInfl_pos_of_var_pos (bernoulliWeight_isProbWeight (by norm_num) (by norm_num)) dict1
    (by rw [var_dict1]; norm_num)

example :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      pen_dampedMass (3 / 4) r (fun ω => if dict1 ω then (1 : ℝ) else 0)
        ≤ (1 : ℝ) * var (bernoulliWeight (3 / 4)) (fun ω => if dict1 ω then (1 : ℝ) else 0)
      ∧ 4 * ((3 / 4 : ℝ) * (1 - 3 / 4)) * Real.log (1 / r) ≤ 2 :=
  esa_dampingHard_c0 (by norm_num) (by norm_num) dict1

/-! ## The antecedents of `esa_DampingHard` are satisfiable -/

/-- A sum over `{0, 1}^{Fin (n + 1)}`, split on coordinate `0`. -/
lemma sum_cons {n : ℕ} (g : ConfigSpace (Fin (n + 1)) → ℝ) :
    ∑ ω, g ω
      = ∑ ω : ConfigSpace (Fin n), (g (Matrix.vecCons false ω) + g (Matrix.vecCons true ω)) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp [Fin.consEquiv, add_comm, Matrix.vecCons]

/-- The `AND` of five bits. -/
def and5 (ω : ConfigSpace (Fin 5)) : Bool := ω 0 && ω 1 && ω 2 && ω 3 && ω 4

/-- Every coordinate of `and5` has influence `p⁴` under `μ_p`. -/
lemma infl_and5 (p : ℝ) (e : Fin 5) :
    infl (bernoulliWeight p) (fun ω => if and5 ω then (1 : ℝ) else 0) e = p ^ 4 := by
  fin_cases e <;>
  · simp [infl, expect, weight, sum_cons, Fin.prod_univ_succ, bernoulliWeight, and5, setOpen,
      setClosed]
    ring

/-- The maximal influence of `and5` under `μ_p` is `p⁴`. -/
lemma maxInfl_and5 (p : ℝ) :
    maxInfl (bernoulliWeight p) (fun ω => if and5 ω then (1 : ℝ) else 0) = p ^ 4 := by
  unfold maxInfl
  rw [show infl (bernoulliWeight p) (fun ω => if and5 ω then (1 : ℝ) else 0) = fun _ => p ^ 4
    from funext (infl_and5 p)]
  exact Finset.sup'_const _ _

/-- The variance of `and5` under `μ_p` is `p⁵ (1 - p⁵)`. -/
lemma var_and5 (p : ℝ) :
    var (bernoulliWeight p) (fun ω => if and5 ω then (1 : ℝ) else 0) = p ^ 5 * (1 - p ^ 5) := by
  simp [var, cov, expect, weight, sum_cons, Fin.prod_univ_succ, bernoulliWeight, and5]
  ring

/-- `(11/20)⁴` lies below the damping threshold `exp (-1/(2p(1-p)))` at `p = 11/20`. -/
lemma and5_below_threshold :
    (11 / 20 : ℝ) ^ 4 < Real.exp (-(1 / (2 * ((11 / 20 : ℝ) * (1 - 11 / 20))))) := by
  rw [show -(1 / (2 * ((11 / 20 : ℝ) * (1 - 11 / 20)))) = -(1 + 1 + 2 / 99) by norm_num,
    Real.exp_neg, Real.exp_add, Real.exp_add]
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hs := Real.exp_bound_div_one_sub_of_interval' (x := 2 / 99) (by norm_num) (by norm_num)
  have hs0 := Real.exp_pos (2 / 99)
  rw [lt_inv_comm₀ (by positivity) (by positivity)]
  have h1 : Real.exp 1 * Real.exp 1 * Real.exp (2 / 99) < 3 * 3 * (99 / 97) := by
    have h3 : Real.exp 1 < 3 := by linarith
    have hs' : Real.exp (2 / 99) < 99 / 97 := by norm_num at hs; linarith
    calc Real.exp 1 * Real.exp 1 * Real.exp (2 / 99) < 3 * 3 * Real.exp (2 / 99) := by
          gcongr
      _ < 3 * 3 * (99 / 97) := by linarith
  calc Real.exp 1 * Real.exp 1 * Real.exp (2 / 99) < 3 * 3 * (99 / 97) := h1
    _ < ((11 / 20 : ℝ) ^ 4)⁻¹ := by norm_num

/-- At `p = 11/20 ∈ (1/2, 1)`, the five-bit `AND` meets all antecedents of `esa_DampingHard`. -/
example :
    (11 / 20 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1
      ∧ 0 < var (bernoulliWeight (11 / 20)) (fun ω => if and5 ω then (1 : ℝ) else 0)
      ∧ 0 < maxInfl (bernoulliWeight (11 / 20)) (fun ω => if and5 ω then (1 : ℝ) else 0)
      ∧ maxInfl (bernoulliWeight (11 / 20)) (fun ω => if and5 ω then (1 : ℝ) else 0)
        < Real.exp (-(1 / (2 * ((11 / 20 : ℝ) * (1 - 11 / 20))))) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_⟩
  · rw [var_and5]; norm_num
  · rw [maxInfl_and5]; norm_num
  · rw [maxInfl_and5]; exact and5_below_threshold

/-! ## The conclusion of `esa_DampingHard` at the five-bit `AND` -/

/-- The `p`-biased Fourier coefficient of `and5` at `S` is `p⁵ ψ_p(1)^|S|`. -/
lemma coeff_and5 (p : ℝ) (S : Finset (Fin 5)) :
    ptn_coeff p (fun ω => if and5 ω then (1 : ℝ) else 0) S = p ^ 5 * ptn_psi p true ^ S.card := by
  have key : ∀ ω : ConfigSpace (Fin 5), (∀ i, ω i = true) →
      ptn_pchar p S ω = ptn_psi p true ^ S.card := by
    intro ω h; simp [ptn_pchar, h]
  simp [ptn_coeff, expect, weight, sum_cons, Fin.prod_univ_succ, bernoulliWeight, and5]
  rw [key _ (by intro i; fin_cases i <;> rfl)]
  ring

/-- `ψ_p(1)² = (1 - p)/p`. -/
lemma psi_true_sq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : ptn_psi p true ^ 2 = (1 - p) / p := by
  have : 0 < 1 - p := by linarith
  rw [ptn_psi, div_pow, ptn_sigma_sq hp0 hp1]
  simp
  field_simp

/-- The damped Fourier mass of `and5` is `p¹⁰ ((1 + r (1-p)/p)⁵ - 1)`. -/
lemma dampedMass_and5 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (r : ℝ) :
    pen_dampedMass p r (fun ω => if and5 ω then (1 : ℝ) else 0)
      = p ^ 10 * ((1 + (1 - p) / p * r) ^ 5 - 1) := by
  unfold pen_dampedMass
  simp_rw [coeff_and5]
  have hterm : ∀ S : Finset (Fin 5), (p ^ 5 * ptn_psi p true ^ S.card) ^ 2 * r ^ S.card
      = p ^ 10 * (((1 - p) / p * r) ^ S.card * 1 ^ (5 - S.card)) := by
    intro S
    rw [one_pow, mul_one, mul_pow, ← psi_true_sq hp0 hp1, ← pow_mul, ← pow_mul, mul_pow,
      ← pow_mul]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ _),
    Fin.sum_pow_mul_eq_add_pow]
  simp only [Finset.card_empty, pow_zero, one_pow, mul_one]
  ring

/-- `7 ≤ exp (200/99)`, from `exp 1 > 2.718`. -/
lemma seven_le_exp : (7 : ℝ) ≤ Real.exp (200 / 99) := by
  have he := Real.exp_one_gt_d9
  have h2 : Real.exp 2 ≤ Real.exp (200 / 99) := Real.exp_le_exp.mpr (by norm_num)
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add] at h2
  nlinarith

/-- The damping threshold at `p = 11/20` is at most `1/7`. -/
lemma threshold_le_seventh :
    Real.exp (-(1 / (2 * ((11 / 20 : ℝ) * (1 - 11 / 20))))) ≤ 1 / 7 := by
  rw [show -(1 / (2 * ((11 / 20 : ℝ) * (1 - 11 / 20)))) = -(200 / 99) by norm_num, Real.exp_neg,
    inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) seven_le_exp

/-- The conclusion of `esa_DampingHard` holds for `and5` at `p = 11/20`, with `r = 1/7`. -/
example :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      pen_dampedMass (11 / 20) r (fun ω => if and5 ω then (1 : ℝ) else 0)
        ≤ maxInfl (bernoulliWeight (11 / 20)) (fun ω => if and5 ω then (1 : ℝ) else 0)
          * var (bernoulliWeight (11 / 20)) (fun ω => if and5 ω then (1 : ℝ) else 0)
      ∧ 4 * ((11 / 20 : ℝ) * (1 - 11 / 20)) * Real.log (1 / r) ≤ 2 := by
  refine ⟨1 / 7, by norm_num, by norm_num, ?_, ?_⟩
  · rw [dampedMass_and5 (by norm_num) (by norm_num), maxInfl_and5, var_and5]
    norm_num
  · have h : Real.log 7 ≤ 200 / 99 := (Real.log_le_iff_le_exp (by norm_num)).mpr seven_le_exp
    rw [one_div_one_div]
    nlinarith

/-! ## The degenerate window `q = 1/2` -/

/-- `esa_DampingHard q` for `q ≤ 1/2` holds because `(1/2, q)` is empty. -/
lemma esa_dampingHard_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : esa_DampingHard q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : pen_DampingWitness (1 / 2) :=
  esa_dampingWitness_of_hard (esa_dampingHard_of_le_half le_rfl)

example : ptn_RhoOptimise (1 / 2) := esa_rhoOptimise_of_hard (esa_dampingHard_of_le_half le_rfl)

example : kpb_PBiasedHC (1 / 2) :=
  esa_PBiasedHC_of_hard (by norm_num) (esa_dampingHard_of_le_half le_rfl)

end StatMechTest.BooleanFunctions.EntropySubadditivity
