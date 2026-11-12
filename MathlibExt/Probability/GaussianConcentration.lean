/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-! # Gaussian concentration for linear functions

For a standard Gaussian vector and a coefficient vector `a`, the
linear form satisfies the standard two-sided Gaussian tail bound
`P (|⟨a, X⟩| ≥ t) ≤ 2 exp (-t² / (2 ‖a‖²))`. This is the
linear-function case of roadmap package ML-11 of the Atlas TCS
canon roadmap; the general Lipschitz (Maurey-Pisier) statement
needs Gaussian log-Sobolev / isoperimetry infrastructure that is
not in Mathlib yet.

Source: Boucheron, Lugosi and Massart, Concentration
Inequalities (2013), Section 5.
-/

open Finset MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- The identity function is sub-Gaussian with parameter 1 under the standard
Gaussian, by the closed-form Gaussian mgf. -/
private lemma hasSubgaussianMGF_id_gaussianReal01 :
    HasSubgaussianMGF id 1 (gaussianReal 0 1) where
  integrable_exp_mul t := by
    simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp

/-- Each scaled coordinate `x ↦ a i * x i` is sub-Gaussian under the product
Gaussian, since the `i`-th coordinate has law `gaussianReal 0 1`. -/
private lemma hasSubgaussianMGF_coord {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    HasSubgaussianMGF (fun x : Fin n → ℝ => a i * x i)
      (NNReal.mk ((a i) ^ 2) (sq_nonneg (a i)) * 1)
      (Measure.pi fun _ => gaussianReal 0 1) := by
  have hmap : (Measure.pi fun _ => gaussianReal 0 1).map (fun x : Fin n → ℝ => x i)
      = gaussianReal 0 1 :=
    (measurePreserving_eval _ i).map_eq
  have hi : HasSubgaussianMGF (fun x : Fin n → ℝ => x i) 1
      (Measure.pi fun _ => gaussianReal 0 1) := by
    rw [← HasSubgaussianMGF.id_map_iff ((measurable_pi_apply i).aemeasurable)]
    rw [hmap]
    exact hasSubgaussianMGF_id_gaussianReal01
  exact hi.const_mul (a i)

/-- The scaled coordinates are independent under the product Gaussian. -/
private lemma iIndepFun_scaled_coord {n : ℕ} (a : Fin n → ℝ) :
    iIndepFun (fun (i : Fin n) (x : Fin n → ℝ) => a i * x i)
      (Measure.pi fun _ => gaussianReal 0 1) :=
  iIndepFun_pi (μ := fun _ => gaussianReal 0 1)
    (X := fun i (y : ℝ) => a i * y) (fun i => by measurability)

/-- The linear form `x ↦ ∑ i, a i * x i` is sub-Gaussian with parameter
`∑ i, (a i)^2` under the product Gaussian. -/
private lemma hasSubgaussianMGF_sum {n : ℕ} (a : Fin n → ℝ) :
    HasSubgaussianMGF (fun x : Fin n → ℝ => ∑ i ∈ Finset.univ, a i * x i)
      (∑ i ∈ Finset.univ, (NNReal.mk ((a i) ^ 2) (sq_nonneg (a i)) * 1))
      (Measure.pi fun _ => gaussianReal 0 1) :=
  HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ) (iIndepFun_scaled_coord a)
    (fun i _ => hasSubgaussianMGF_coord a i)

/-- Gaussian concentration for linear functions: if `X` is a
standard Gaussian vector in `Fin n → ℝ` (product of
`gaussianReal 0 1`) and `a` is a coefficient vector, then
`P (|⟨a, X⟩| ≥ t) ≤ 2 exp (-t² / (2 ‖a‖²))` for `t > 0`, with the
right side read as `0`-safe when `a = 0` (then the probability is
`0` since the linear form vanishes; the bound is stated through
`ENNReal.ofReal` of the real expression, and for `a = 0` we read
the inequality as the `∑ a^2 = 0` case handled separately below). -/
theorem gaussian_linear_tail {n : ℕ} (a : Fin n → ℝ) {t : ℝ} (ht : 0 < t)
    (ha : ∑ i, a i ^ 2 ≠ 0) :
    (Measure.pi fun _ => gaussianReal 0 1)
        {x | t ≤ |∑ i, a i * x i|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ∑ i, a i ^ 2))) := by
  have _ := ha
  have hS := hasSubgaussianMGF_sum a
  have hc : (((∑ i ∈ Finset.univ, (NNReal.mk ((a i) ^ 2) (sq_nonneg (a i)) * 1)) : NNReal) : ℝ)
      = ∑ i, a i ^ 2 := by
    rw [NNReal.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hup : (Measure.pi fun _ => gaussianReal 0 1).real
      {x : Fin n → ℝ | t ≤ ∑ i, a i * x i}
      ≤ Real.exp (-t ^ 2 / (2 * ∑ i, a i ^ 2)) := by
    have h := hS.measure_ge_le (le_of_lt ht)
    rwa [hc] at h
  have hlow : (Measure.pi fun _ => gaussianReal 0 1).real
      {x : Fin n → ℝ | t ≤ -∑ i, a i * x i}
      ≤ Real.exp (-t ^ 2 / (2 * ∑ i, a i ^ 2)) := by
    have h := hS.neg.measure_ge_le (le_of_lt ht)
    rwa [hc] at h
  have hset : {x : Fin n → ℝ | t ≤ |∑ i, a i * x i|}
      = {x : Fin n → ℝ | t ≤ ∑ i, a i * x i}
        ∪ {x : Fin n → ℝ | t ≤ -∑ i, a i * x i} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      by_cases h0 : 0 ≤ ∑ i, a i * x i
      · rw [abs_of_nonneg h0] at h
        exact Or.inl h
      · rw [abs_of_neg (not_le.mp h0)] at h
        exact Or.inr h
    · rintro (h | h)
      · exact h.trans (le_abs_self _)
      · exact h.trans (neg_le_abs _)
  have hfin : (Measure.pi fun _ => gaussianReal 0 1)
      {x : Fin n → ℝ | t ≤ |∑ i, a i * x i|} ≠ ⊤ :=
    measure_ne_top _ _
  have hpos : 0 ≤ 2 * Real.exp (-t ^ 2 / (2 * ∑ i, a i ^ 2)) := by positivity
  rw [← ENNReal.ofReal_toReal hfin, hset, ENNReal.ofReal_le_ofReal_iff hpos]
  have h2 : Real.exp (-t ^ 2 / (2 * ∑ i, a i ^ 2))
      + Real.exp (-t ^ 2 / (2 * ∑ i, a i ^ 2))
      = 2 * Real.exp (-t ^ 2 / (2 * ∑ i, a i ^ 2)) := by ring
  rw [← h2]
  refine (measureReal_union_le _ _).trans ?_
  exact add_le_add hup hlow

/-- The degenerate case: if the coefficient vector has
`∑ a_i^2 = 0` (so every `a i = 0`), the exceedance event is empty
for `t > 0`. -/
theorem gaussian_linear_tail_zero {n : ℕ} (a : Fin n → ℝ) {t : ℝ} (ht : 0 < t)
    (ha : ∑ i, a i ^ 2 = 0) :
    (Measure.pi fun _ => gaussianReal 0 1)
        {x | t ≤ |∑ i, a i * x i|} = 0 := by
  have hai : ∀ i, a i = 0 := by
    intro i
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (a i))).mp ha i
      (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp h
  have hsum : ∀ x : Fin n → ℝ, (∑ i, a i * x i) = 0 := by
    intro x
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [hai i]
  have hev : {x : Fin n → ℝ | t ≤ |∑ i, a i * x i|} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rw [hsum x, abs_zero]
    exact not_le_of_gt ht
  rw [hev, measure_empty]

end ProbabilityTheory

