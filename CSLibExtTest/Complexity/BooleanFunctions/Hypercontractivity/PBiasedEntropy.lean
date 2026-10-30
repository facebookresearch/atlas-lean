/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.PBiasedEntropy
public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.CoupledTensorizeRefutations

/-!
# Tests for damped Fourier mass and the damping-witness route

Tests for `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.PBiasedEntropy`, mostly at the
dictator `ω ↦ ω 0` on `{0, 1}^{Fin 1}` (one-coordinate computations from `CoupledTensorizeRefutations`):

* `pen_dampedMass` of the dictator is `p(1-p) r`; `pen_dampedMass_nonneg`, `pen_dampedMass_pos`;
* `pen_degree_extraction` on a one-element sum (an equality) and on a two-element sum
  (`c = 1`, `d = 0, 1`, `r = 1/2`);
* `pen_logGain_assembly` at concrete numbers with `δ = 1/2`, giving `2 log 2 ≤ 4`;
* `pen_degreeWeight_eq` at the dictator, consistent with `Inf(dictator) = 1`;
* the body of `pen_DampingWitness` holds for the dictator at every `p ∈ (0, 1)` (witness
  `r = 1/2`), so the predicate is not vacuous on this function;
* `pen_dampingWitness_c0`.

Not tested non-degenerately: `pen_DampingWitness q` quantifies over all Boolean functions and all
`p ∈ (1/2, q)`; it is neither proved nor refuted for any `q > 1/2`. The conditional chain
(`pen_rhoOptimise_of_damping`, `pen_kklHC_of_damping`, `pen_PBiasedHC_of_damping`) is recorded at
the degenerate window `q = 1/2`, where the predicate holds because `(1/2, 1/2)` is empty.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.PBiasedEntropy

open StatMech StatMech.OSSS StatMech.Probability

/-- The dictator `ω ↦ ω 0` on `{0, 1}^{Fin 1}`. -/
def dict1 (ω : ConfigSpace (Fin 1)) : Bool := ω 0

/-- The damped mass of the dictator is `p(1-p) r`. -/
lemma dampedMass_dict1 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (r : ℝ) :
    pen_dampedMass p r (fun ω => if dict1 ω then (1 : ℝ) else 0) = p * (1 - p) * r := by
  rw [pen_dampedMass, show Finset.univ.erase (∅ : Finset (Fin 1)) = {{0}} by decide,
    Finset.sum_singleton]
  rw [show (fun ω => if dict1 ω then (1 : ℝ) else 0)
      = (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0) from rfl,
    ctc_coeff_single p hp0 hp1, ptn_sigma_sq hp0 hp1]
  simp

/-- The variance of the dictator under `μ_p` is `p(1-p)`. -/
lemma var_dict1 (p : ℝ) :
    var (bernoulliWeight p) (fun ω => if dict1 ω then (1 : ℝ) else 0) = p * (1 - p) := by
  simp only [var, cov, ctc_expect_fin1, dict1]
  simp
  ring

example : pen_dampedMass (1 / 2) (1 / 3) (fun ω => if dict1 ω then (1 : ℝ) else 0) = 1 / 12 := by
  rw [dampedMass_dict1 (by norm_num) (by norm_num)]; norm_num

example : 0 ≤ pen_dampedMass (1 / 2) (1 / 3) (fun ω => if dict1 ω then (1 : ℝ) else 0) :=
  pen_dampedMass_nonneg (by norm_num) _

example : 0 < pen_dampedMass (1 / 2) (1 / 3) (fun ω => if dict1 ω then (1 : ℝ) else 0) := by
  refine pen_dampedMass_pos (by norm_num) _ ?_
  rw [← ptn_var_eq_fourierWeight (by norm_num) (by norm_num), var_dict1]
  norm_num

/-- `pen_degree_extraction` on a single term (`c = 1`, `d = 1`, `r = 1/2`). -/
example :
    (∑ _k ∈ ({0} : Finset ℕ), (1 : ℝ))
        * Real.log ((∑ _k ∈ ({0} : Finset ℕ), (1 : ℝ))
          / (∑ _k ∈ ({0} : Finset ℕ), (1 : ℝ) * (1 / 2) ^ 1))
      ≤ Real.log (1 / (1 / 2)) * ∑ _k ∈ ({0} : Finset ℕ), ((1 : ℕ) : ℝ) * 1 :=
  pen_degree_extraction ({0} : Finset ℕ) (fun _ => (1 : ℝ)) (fun _ => 1) (1 / 2)
    (by norm_num) (by simp) (by norm_num)

/-- On a single term both sides of `pen_degree_extraction` equal `log 2`. -/
example :
    (∑ _k ∈ ({0} : Finset ℕ), (1 : ℝ))
        * Real.log ((∑ _k ∈ ({0} : Finset ℕ), (1 : ℝ))
          / (∑ _k ∈ ({0} : Finset ℕ), (1 : ℝ) * (1 / 2) ^ 1)) = Real.log 2
      ∧ Real.log (1 / (1 / 2)) * ∑ _k ∈ ({0} : Finset ℕ), ((1 : ℕ) : ℝ) * 1 = Real.log 2 := by
  norm_num

/-- `pen_degree_extraction` with `c = 1`, `d = 0, 1`, `r = 1/2`: `2 log (4/3) ≤ log 2`. -/
example : 2 * Real.log (4 / 3) ≤ Real.log 2 := by
  have h := pen_degree_extraction ({0, 1} : Finset ℕ) (fun _ => (1 : ℝ)) (fun k => k) (1 / 2)
    (by norm_num) (by simp) (by norm_num)
  norm_num at h
  exact h

example : 2 * 1 * Real.log (1 / (1 / 2 : ℝ)) ≤ 4 :=
  pen_logGain_assembly (V := 1) (D := 1 / 2) (T := 4) (δ := 1 / 2) (L := 2) (pp := 1 / 4) (M := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; linarith [Real.log_two_lt_d9]) (by norm_num) (by norm_num)

example : (∑ S ∈ Finset.univ.erase (∅ : Finset (Fin 1)),
      (S.card : ℝ) * (ptn_coeff (1 / 2) (fun ω => if dict1 ω then (1 : ℝ) else 0) S) ^ 2)
    = 1 / 4 := by
  rw [pen_degreeWeight_eq (by norm_num) (by norm_num),
    show (fun ω => if dict1 ω then (1 : ℝ) else 0)
      = (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0) from rfl,
    ctc_totalInfl]
  norm_num

/-- The body of `pen_DampingWitness` holds for the dictator at every `p ∈ (0, 1)`, with
`r = 1/2`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      pen_dampedMass p r (fun ω => if dict1 ω then (1 : ℝ) else 0)
        ≤ maxInfl (bernoulliWeight p) (fun ω => if dict1 ω then (1 : ℝ) else 0)
          * var (bernoulliWeight p) (fun ω => if dict1 ω then (1 : ℝ) else 0)
      ∧ 4 * (p * (1 - p)) * Real.log (1 / r) ≤ 2 := by
  have hmax : maxInfl (bernoulliWeight p) (fun ω => if dict1 ω then (1 : ℝ) else 0) = 1 :=
    ctc_maxInfl p
  have hpp : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  have hpp' : 4 * (p * (1 - p)) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
  have hlog : Real.log (1 / (1 / 2 : ℝ)) = Real.log 2 := by norm_num
  refine ⟨1 / 2, by norm_num, by norm_num, ?_, ?_⟩
  · rw [dampedMass_dict1 hp0 hp1, hmax, var_dict1]; nlinarith
  · rw [hlog]
    have h2 := Real.log_two_lt_d9
    have h0 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith

/-- `pen_DampingWitness q` for `q ≤ 1/2` holds because `(1/2, q)` is empty. -/
lemma pen_dampingWitness_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : pen_DampingWitness q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : ptn_RhoOptimise (1 / 2) :=
  pen_rhoOptimise_of_damping (pen_dampingWitness_of_le_half le_rfl)

example : kpb_PBiasedHC (1 / 2) :=
  pen_PBiasedHC_of_damping (by norm_num) (pen_dampingWitness_of_le_half le_rfl)

example :
    (0 : ℝ) * var (bernoulliWeight (3 / 4)) (fun ω => if dict1 ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight (3 / 4)) (fun ω => if dict1 ω then (1 : ℝ) else 0))
      ≤ totalInfl (bernoulliWeight (3 / 4)) (fun ω => if dict1 ω then (1 : ℝ) else 0) :=
  pen_dampingWitness_c0 (by norm_num) (by norm_num) dict1

end StatMechTest.BooleanFunctions.PBiasedEntropy
