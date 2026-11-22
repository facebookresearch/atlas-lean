/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.ItemResponse
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Product-law mass and coordinate moments

For the finite product law `localIndepPMF`, the real mass of one outcome is
the product of the selected coordinate probabilities, and coordinate
indicators have the product-law means and pairwise product means.
-/

open MeasureTheory

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

private theorem sum_pi_prod_bool {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommSemiring R]
    (f : ι → Bool → R) :
    ∑ x : ι → Bool, ∏ i, f i (x i) = ∏ i, ∑ b, f i b := by
  have h := Finset.sum_prod_piFinset (ι := ι) (κ := Bool) (s := Finset.univ)
    (fun i b => f i b)
  rw [Fintype.piFinset_univ] at h
  exact h

/-- (1) Real mass of one outcome: `toReal` of the product law is the product
of the selected coordinate probabilities. No strict positivity: `q i = 0`
and `q i = 1` are allowed. -/
theorem localIndepPMF_toReal_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (x : ι → Bool) :
    (localIndepPMF q hq0 hq1 x).toReal
      = ∏ i, (if x i then q i else 1 - q i) := by
  rw [localIndepPMF_apply, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  cases hx : x i
  · have e : (if false then ENNReal.ofReal (q i) else ENNReal.ofReal (1 - q i))
        = ENNReal.ofReal (1 - q i) := by simp
    have e' : (if false then q i else 1 - q i) = 1 - q i := by simp
    rw [e, e']
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (hq1 i))
  · have e : (if true then ENNReal.ofReal (q i) else ENNReal.ofReal (1 - q i))
        = ENNReal.ofReal (q i) := by simp
    have e' : (if true then q i else 1 - q i) = q i := by simp
    rw [e, e']
    exact ENNReal.toReal_ofReal (hq0 i)

private theorem localIndepPMF_m1_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (i j : ι) :
    (∑ b : Bool, ((if i = j then (if b then (1 : ℝ) else 0) else 1)
      * (if b then q j else 1 - q j)))
      = (if i = j then q i else 1) := by
  by_cases hj : i = j
  · subst hj
    simp
  · simp [hj]

private theorem localIndepPMF_m2_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (i j k : ι) :
    (∑ b : Bool, (((if i = k then (if b then (1 : ℝ) else 0) else 1)
      * (if j = k then (if b then (1 : ℝ) else 0) else 1))
      * (if b then q k else 1 - q k)))
      = (if i = k then q i else if j = k then q j else 1) := by
  by_cases hi : i = k
  · subst hi
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  · by_cases hj : j = k
    · subst hj
      simp [hi]
    · simp [hi, hj]

/-- (2)+(3) Coordinate moments under `PMF.toMeasure`: each coordinate has
mean `q i`, and two distinct coordinates have product-mean `q i * q j`.
The `i ≠ j` hypothesis is required only for the product identity. -/
theorem localIndepPMF_coordinate_moments {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (∀ i, ∫ x, (if x i then (1 : ℝ) else 0)
        ∂(localIndepPMF q hq0 hq1).toMeasure = q i)
    ∧ (∀ i j, i ≠ j →
        ∫ x, (if x i then (1 : ℝ) else 0) * (if x j then (1 : ℝ) else 0)
          ∂(localIndepPMF q hq0 hq1).toMeasure = q i * q j) := by
  have h1 : ∀ i : ι, (∫ x, (if x i then (1 : ℝ) else 0)
      ∂(localIndepPMF q hq0 hq1).toMeasure) = q i := by
    intro i
    rw [PMF.integral_eq_sum]
    simp only [smul_eq_mul]
    have habs1 : ∀ x : ι → Bool, (∏ j, (if x j then q j else 1 - q j))
        * (if x i then (1 : ℝ) else 0)
        = ∏ j, ((if i = j then (if x j then (1 : ℝ) else 0) else 1)
          * (if x j then q j else 1 - q j)) := by
      intro x
      rw [Finset.prod_mul_distrib]
      have hA : (∏ j, (if i = j then (if x j then (1 : ℝ) else 0) else 1))
          = (if x i then (1 : ℝ) else 0) := by
        simp [Finset.prod_ite_eq]
      rw [hA]
      ring
    have hterm1 : ∀ x : ι → Bool, (localIndepPMF q hq0 hq1 x).toReal
        * (if x i then (1 : ℝ) else 0)
        = ∏ j, ((if i = j then (if x j then (1 : ℝ) else 0) else 1)
          * (if x j then q j else 1 - q j)) := by
      intro x
      rw [localIndepPMF_toReal_apply]
      exact habs1 x
    calc ∑ a, (localIndepPMF q hq0 hq1 a).toReal * (if a i then (1 : ℝ) else 0)
        = ∑ x, ∏ j, ((if i = j then (if x j then (1 : ℝ) else 0) else 1)
            * (if x j then q j else 1 - q j)) :=
          Finset.sum_congr rfl (fun x _ => hterm1 x)
      _ = ∏ j, ∑ b : Bool, ((if i = j then (if b then (1 : ℝ) else 0) else 1)
            * (if b then q j else 1 - q j)) :=
          sum_pi_prod_bool (fun j b => (if i = j then (if b then (1 : ℝ) else 0) else 1)
            * (if b then q j else 1 - q j))
      _ = ∏ j, (if i = j then q i else 1) :=
          Finset.prod_congr rfl (fun j _ => localIndepPMF_m1_factor q i j)
      _ = q i := by simp [Finset.prod_ite_eq]
  have h2 : ∀ i j : ι, i ≠ j → (∫ x, (if x i then (1 : ℝ) else 0)
      * (if x j then (1 : ℝ) else 0)
      ∂(localIndepPMF q hq0 hq1).toMeasure) = q i * q j := by
    intro i j hij
    rw [PMF.integral_eq_sum]
    simp only [smul_eq_mul]
    have habs2 : ∀ x : ι → Bool, (∏ k, (if x k then q k else 1 - q k))
        * ((if x i then (1 : ℝ) else 0) * (if x j then (1 : ℝ) else 0))
        = ∏ k, (((if i = k then (if x k then (1 : ℝ) else 0) else 1)
          * (if j = k then (if x k then (1 : ℝ) else 0) else 1))
          * (if x k then q k else 1 - q k)) := by
      intro x
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      have hA : (∏ k, (if i = k then (if x k then (1 : ℝ) else 0) else 1))
          = (if x i then (1 : ℝ) else 0) := by
        simp [Finset.prod_ite_eq]
      have hB : (∏ k, (if j = k then (if x k then (1 : ℝ) else 0) else 1))
          = (if x j then (1 : ℝ) else 0) := by
        simp [Finset.prod_ite_eq]
      rw [hA, hB]
      ring
    have hterm2 : ∀ x : ι → Bool, (localIndepPMF q hq0 hq1 x).toReal
        * ((if x i then (1 : ℝ) else 0) * (if x j then (1 : ℝ) else 0))
        = ∏ k, (((if i = k then (if x k then (1 : ℝ) else 0) else 1)
          * (if j = k then (if x k then (1 : ℝ) else 0) else 1))
          * (if x k then q k else 1 - q k)) := by
      intro x
      rw [localIndepPMF_toReal_apply]
      exact habs2 x
    have h2fac : ∀ k : ι, (if i = k then q i else if j = k then q j else 1)
        = (if i = k then q i else 1) * (if j = k then q j else 1) := by
      intro k
      by_cases hi : i = k
      · by_cases hj : j = k
        · exact absurd (hi.trans hj.symm) hij
        · simp [hi, hj]
      · by_cases hj : j = k
        · simp [hi, hj]
        · simp [hi, hj]
    calc ∑ a, (localIndepPMF q hq0 hq1 a).toReal
          * ((if a i then (1 : ℝ) else 0) * (if a j then (1 : ℝ) else 0))
        = ∑ x, ∏ k, (((if i = k then (if x k then (1 : ℝ) else 0) else 1)
            * (if j = k then (if x k then (1 : ℝ) else 0) else 1))
            * (if x k then q k else 1 - q k)) :=
          Finset.sum_congr rfl (fun x _ => hterm2 x)
      _ = ∏ k, ∑ b : Bool, (((if i = k then (if b then (1 : ℝ) else 0) else 1)
            * (if j = k then (if b then (1 : ℝ) else 0) else 1))
            * (if b then q k else 1 - q k)) :=
          sum_pi_prod_bool (fun k b => ((if i = k then (if b then (1 : ℝ) else 0) else 1)
            * (if j = k then (if b then (1 : ℝ) else 0) else 1))
            * (if b then q k else 1 - q k))
      _ = ∏ k, (if i = k then q i else if j = k then q j else 1) :=
          Finset.prod_congr rfl (fun k _ => localIndepPMF_m2_factor q i j k)
      _ = ∏ k, ((if i = k then q i else 1) * (if j = k then q j else 1)) :=
          Finset.prod_congr rfl (fun k _ => h2fac k)
      _ = (∏ k, (if i = k then q i else 1)) * (∏ k, (if j = k then q j else 1)) := by
          rw [Finset.prod_mul_distrib]
      _ = q i * q j := by simp [Finset.prod_ite_eq]
  exact ⟨h1, h2⟩

end MathlibExt.Probability.Statistics.Measurement
