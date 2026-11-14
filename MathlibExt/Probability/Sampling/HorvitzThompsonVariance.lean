/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Sampling.HorvitzThompson

import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Erase
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Horvitz-Thompson variance and the Sen-Yates-Grundy form

Second-order inclusion probabilities, the general Horvitz-Thompson variance
identity (mean-squared error about the population total), its Yates-Grundy
form for fixed-size designs, and the expectation of the Sen-Yates-Grundy
variance estimator. The estimator's expectation is the Sen-Yates-Grundy form
whenever every pair has positive inclusion probability
(`integral_senYatesGrundyEstimate`), but that form is the variance only for
fixed-size designs, so the estimator is unbiased for the variance only there
(`integral_senYatesGrundyEstimate_eq_variance`).

## References

- Shalabh, *Sampling Theory*, Chapter 7 "Varying Probability Sampling",
  Department of Mathematics and Statistics, IIT Kanpur.
- D. G. Horvitz and D. J. Thompson, "A generalization of sampling without
  replacement from a finite universe", JASA 47(260) (1952), 663-685.
- F. Yates and P. M. Grundy, "Selection without replacement from within
  strata with probability proportional to size", JRSS B 15(2) (1953).
- C.-E. Särndal, B. Swensson, and J. Wretman, *Model Assisted Survey
  Sampling*, Springer (1992), Chapter 2.
-/

@[expose] public section

namespace MathlibExt.Probability.Sampling

open MeasureTheory

/-- Second-order (pair) inclusion probability: total mass of the samples
    containing both `i` and `j`. -/
noncomputable def pairInclusionProbability {α : Type*} [Fintype α]
    [DecidableEq α] (p : PMF (Finset α)) (i j : α) : ℝ :=
  ∑ s, if i ∈ s ∧ j ∈ s then (p s).toReal else 0

/-- Sen-Yates-Grundy variance form for fixed-size designs. It equals the
    variance of the Horvitz-Thompson total only for fixed-size designs
    (`variance_horvitzThompsonTotal_fixed`). -/
noncomputable def senYatesGrundyVariance {α : Type*} [Fintype α]
    [DecidableEq α] (p : PMF (Finset α)) (y : α → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
    (inclusionProbability p i * inclusionProbability p j
      - pairInclusionProbability p i j)
      * (y i / inclusionProbability p i - y j / inclusionProbability p j) ^ 2

/-- Sen-Yates-Grundy variance estimator at sample `s`. -/
noncomputable def senYatesGrundyEstimate {α : Type*} [Fintype α]
    [DecidableEq α] (p : PMF (Finset α)) (y : α → ℝ) (s : Finset α) : ℝ :=
  (1 / 2) * ∑ i ∈ s, ∑ j ∈ s.erase i,
    ((inclusionProbability p i * inclusionProbability p j
      - pairInclusionProbability p i j)
      / pairInclusionProbability p i j)
      * (y i / inclusionProbability p i - y j / inclusionProbability p j) ^ 2

/-- The design masses sum to one. -/
private theorem sum_toReal_eq_one {α : Type*} [Fintype α]
    (p : PMF (Finset α)) : ∑ s, (p s).toReal = 1 := by
  have hne : ∀ s ∈ (Finset.univ : Finset (Finset α)), p s ≠ ⊤ :=
    fun s _ => p.apply_ne_top s
  have h := ENNReal.toReal_sum hne
  have h1 : (∑ s, p s) = 1 := by
    rw [← tsum_fintype (L := SummationFilter.unconditional _)]
    exact p.tsum_coe
  rw [← h, h1, ENNReal.toReal_one]

/-- Mass-weighted inclusion indicators sum to the inclusion probability. -/
private theorem sum_mul_indicator_eq {α : Type*} [Fintype α] [DecidableEq α]
    (p : PMF (Finset α)) (i : α) :
    ∑ s, (p s).toReal * (if i ∈ s then (1 : ℝ) else 0)
      = inclusionProbability p i := by
  have hterm : ∀ s : Finset α, (p s).toReal * (if i ∈ s then (1 : ℝ) else 0)
      = (if i ∈ s then (p s).toReal else 0) := by
    intro s
    by_cases h : i ∈ s <;> simp [h]
  calc ∑ s, (p s).toReal * (if i ∈ s then (1 : ℝ) else 0)
      = ∑ s, (if i ∈ s then (p s).toReal else 0) :=
        Finset.sum_congr rfl (fun s _ => hterm s)
    _ = inclusionProbability p i := rfl

/-- Joint mass-weighted indicators give pair inclusion on the off-diagonal
    and single inclusion on the diagonal. -/
private theorem sum_mul_indicator_mul_eq {α : Type*} [Fintype α]
    [DecidableEq α] (p : PMF (Finset α)) (i j : α) :
    ∑ s, (p s).toReal * ((if i ∈ s then (1 : ℝ) else 0)
      * (if j ∈ s then (1 : ℝ) else 0))
      = (if i = j then inclusionProbability p i
        else pairInclusionProbability p i j) := by
  by_cases hij : i = j
  · rw [ite_eq_left hij]
    have hterm : ∀ s : Finset α, (p s).toReal
        * ((if i ∈ s then (1 : ℝ) else 0) * (if j ∈ s then (1 : ℝ) else 0))
        = (if i ∈ s then (p s).toReal else 0) := by
      intro s
      rw [hij]
      by_cases h : j ∈ s <;> simp [h]
    calc ∑ s, (p s).toReal
          * ((if i ∈ s then (1 : ℝ) else 0) * (if j ∈ s then (1 : ℝ) else 0))
        = ∑ s, (if i ∈ s then (p s).toReal else 0) :=
          Finset.sum_congr rfl (fun s _ => hterm s)
      _ = inclusionProbability p i := rfl
  · rw [ite_eq_right hij]
    have hterm : ∀ s : Finset α, (p s).toReal
        * ((if i ∈ s then (1 : ℝ) else 0) * (if j ∈ s then (1 : ℝ) else 0))
        = (if i ∈ s ∧ j ∈ s then (p s).toReal else 0) := by
      intro s
      by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [hi, hj]
    calc ∑ s, (p s).toReal
          * ((if i ∈ s then (1 : ℝ) else 0) * (if j ∈ s then (1 : ℝ) else 0))
        = ∑ s, (if i ∈ s ∧ j ∈ s then (p s).toReal else 0) :=
          Finset.sum_congr rfl (fun s _ => hterm s)
      _ = pairInclusionProbability p i j := rfl

/-- Covariance of two inclusion indicators: joint inclusion on the diagonal
    is single inclusion, off the diagonal it is pair inclusion, minus the
    product of single inclusions. -/
private theorem indicator_cov {α : Type*} [Fintype α] [DecidableEq α]
    (p : PMF (Finset α)) (i j : α) :
    (∑ s, (p s).toReal * (((if i ∈ s then (1 : ℝ) else 0)
      - inclusionProbability p i)
      * ((if j ∈ s then (1 : ℝ) else 0) - inclusionProbability p j)))
      = (if i = j then inclusionProbability p i
        else pairInclusionProbability p i j)
        - inclusionProbability p i * inclusionProbability p j := by
  have hexpand : ∀ s : Finset α, (p s).toReal
      * (((if i ∈ s then (1 : ℝ) else 0) - inclusionProbability p i)
        * ((if j ∈ s then (1 : ℝ) else 0) - inclusionProbability p j))
      = (p s).toReal * ((if i ∈ s then (1 : ℝ) else 0)
          * (if j ∈ s then (1 : ℝ) else 0))
        - inclusionProbability p i
          * ((p s).toReal * (if j ∈ s then (1 : ℝ) else 0))
        - inclusionProbability p j
          * ((p s).toReal * (if i ∈ s then (1 : ℝ) else 0))
        + inclusionProbability p i * inclusionProbability p j
          * (p s).toReal := by
    intro s
    ring
  have hE : (∑ s, (p s).toReal * ((if i ∈ s then (1 : ℝ) else 0)
      * (if j ∈ s then (1 : ℝ) else 0)))
      = (if i = j then inclusionProbability p i
        else pairInclusionProbability p i j) :=
    sum_mul_indicator_mul_eq p i j
  simp only [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hE, ← Finset.mul_sum, sum_mul_indicator_eq, sum_toReal_eq_one,
    mul_one]
  ring

/-- Fixed-size row-sum identity (Shalabh, Ch. 7): under `hfix`, the
    off-diagonal entries of each row of the inclusion-indicator covariance
    matrix sum to `-π i (1 - π i)`, so each full row sums to zero. -/
private theorem row_sum_fixed {α : Type*} [Fintype α] [DecidableEq α]
    (p : PMF (Finset α)) (n : ℕ)
    (hfix : ∀ s, p s ≠ 0 → s.card = n) (i : α) :
    ∑ j ∈ Finset.univ.erase i,
      (pairInclusionProbability p i j
        - inclusionProbability p i * inclusionProbability p j)
      = -(inclusionProbability p i * (1 - inclusionProbability p i)) := by
  have hcard : ∀ s : Finset α,
      (∑ j, (if j ∈ s then (1 : ℝ) else 0)) = (s.card : ℝ) := by
    intro s
    have hsub : (∑ j, (if j ∈ s then (1 : ℝ) else 0)) = ∑ j ∈ s, (1 : ℝ) := by
      have hcongr : ∀ j ∈ s, (if j ∈ s then (1 : ℝ) else 0) = (1 : ℝ) := by
        intro j hj
        simp [hj]
      calc (∑ j, (if j ∈ s then (1 : ℝ) else 0))
          = ∑ j ∈ s, (if j ∈ s then (1 : ℝ) else 0) := by
            symm
            apply Finset.sum_subset (Finset.subset_univ s)
            intro j _ hjs
            simp [hjs]
        _ = ∑ j ∈ s, (1 : ℝ) := Finset.sum_congr rfl hcongr
    rw [hsub, Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp
  have hae : ∀ s : Finset α, (p s).toReal
      * (((if i ∈ s then (1 : ℝ) else 0) - inclusionProbability p i)
        * ((s.card : ℝ) - (n : ℝ))) = 0 := by
    intro s
    by_cases h : p s = 0
    · rw [h, ENNReal.toReal_zero, zero_mul]
    · have hcn : (s.card : ℝ) = (n : ℝ) := by rw [hfix s h]
      rw [hcn, sub_self, mul_zero, mul_zero]
  have h0 : (∑ s, (p s).toReal * ((((if i ∈ s then (1 : ℝ) else 0)
      - inclusionProbability p i) * ((s.card : ℝ) - (n : ℝ)))))
      = 0 :=
    Finset.sum_eq_zero (fun s _ => hae s)
  have step1 : (∑ s, (p s).toReal * ((((if i ∈ s then (1 : ℝ) else 0)
      - inclusionProbability p i) * ((s.card : ℝ) - (n : ℝ)))))
      = (∑ j, ∑ s, (p s).toReal * ((((if i ∈ s then (1 : ℝ) else 0)
        - inclusionProbability p i) * (if j ∈ s then (1 : ℝ) else 0))))
        - (n : ℝ) * ∑ s, (p s).toReal * (((if i ∈ s then (1 : ℝ) else 0)
        - inclusionProbability p i)) := by
    have hpt : ∀ s : Finset α, (p s).toReal
        * ((((if i ∈ s then (1 : ℝ) else 0) - inclusionProbability p i)
        * ((s.card : ℝ) - (n : ℝ))))
        = (∑ j, (p s).toReal * ((((if i ∈ s then (1 : ℝ) else 0)
          - inclusionProbability p i) * (if j ∈ s then (1 : ℝ) else 0))))
          - (n : ℝ) * ((p s).toReal * (((if i ∈ s then (1 : ℝ) else 0)
          - inclusionProbability p i))) := by
      intro s
      rw [← hcard s]
      simp only [mul_sub, Finset.mul_sum]
      ring
    simp only [hpt, Finset.sum_sub_distrib]
    rw [Finset.sum_comm, ← Finset.mul_sum]
  have hcenter : (∑ s, (p s).toReal * (((if i ∈ s then (1 : ℝ) else 0)
      - inclusionProbability p i))) = 0 := by
    have hpt2 : ∀ s : Finset α, (p s).toReal
        * (((if i ∈ s then (1 : ℝ) else 0) - inclusionProbability p i))
        = (p s).toReal * (if i ∈ s then (1 : ℝ) else 0)
          - inclusionProbability p i * (p s).toReal := by
      intro s
      ring
    simp only [hpt2, Finset.sum_sub_distrib, sum_mul_indicator_eq,
      ← Finset.mul_sum, sum_toReal_eq_one, mul_one, sub_self]
  have hC1 : ∀ j, (∑ s, (p s).toReal * ((((if i ∈ s then (1 : ℝ) else 0)
      - inclusionProbability p i) * (if j ∈ s then (1 : ℝ) else 0))))
      = (if i = j then inclusionProbability p i
        else pairInclusionProbability p i j)
        - inclusionProbability p i * inclusionProbability p j := by
    intro j
    have hpt3 : ∀ s : Finset α, (p s).toReal
        * ((((if i ∈ s then (1 : ℝ) else 0) - inclusionProbability p i)
        * (if j ∈ s then (1 : ℝ) else 0)))
        = (p s).toReal * ((if i ∈ s then (1 : ℝ) else 0)
          * (if j ∈ s then (1 : ℝ) else 0))
          - inclusionProbability p i
          * ((p s).toReal * (if j ∈ s then (1 : ℝ) else 0)) := by
      intro s
      ring
    simp only [hpt3, Finset.sum_sub_distrib, sum_mul_indicator_mul_eq,
      sum_mul_indicator_eq, ← Finset.mul_sum]
  rw [step1, hcenter, mul_zero, sub_zero] at h0
  simp only [hC1] at h0
  have hsplit : (∑ j, ((if i = j then inclusionProbability p i
      else pairInclusionProbability p i j)
      - inclusionProbability p i * inclusionProbability p j))
      = (inclusionProbability p i - inclusionProbability p i
        * inclusionProbability p i)
        + ∑ j ∈ Finset.univ.erase i,
          (pairInclusionProbability p i j
          - inclusionProbability p i * inclusionProbability p j) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp only [ite_true]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_erase] at hj
      have hnij : i ≠ j := fun h => hj.1 h.symm
      rw [ite_eq_right hnij]
  rw [hsplit] at h0
  have hrew : (inclusionProbability p i - inclusionProbability p i
      * inclusionProbability p i)
      = inclusionProbability p i * (1 - inclusionProbability p i) := by
    ring
  rw [hrew, add_comm] at h0
  exact eq_neg_of_add_eq_zero_left h0

/-- Swapping a double sum over off-diagonal pairs. -/
private theorem sum_erase_swap {α : Type*} [Fintype α] [DecidableEq α]
    (F : α → α → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, F i j)
      = ∑ j, ∑ i ∈ Finset.univ.erase j, F i j := by
  have h1 : ∀ i, (∑ j ∈ Finset.univ.erase i, F i j)
      = ∑ j, (if j ≠ i then F i j else 0) := by
    intro i
    calc (∑ j ∈ Finset.univ.erase i, F i j)
        = ∑ j ∈ Finset.univ.erase i, (if j ≠ i then F i j else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_erase] at hj
          exact (ite_eq_left hj.1).symm
      _ = ∑ j, (if j ≠ i then F i j else 0) := by
          apply Finset.sum_subset (Finset.erase_subset i Finset.univ)
          intro x _ hx
          have hxi : ¬ x ≠ i := fun hne =>
            hx (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ x⟩)
          simp [hxi]
  have h2 : ∀ j, (∑ i, (if j ≠ i then F i j else 0))
      = ∑ i ∈ Finset.univ.erase j, F i j := by
    intro j
    calc (∑ i, (if j ≠ i then F i j else 0))
        = ∑ i ∈ Finset.univ.erase j, (if j ≠ i then F i j else 0) := by
            symm
            apply Finset.sum_subset (Finset.erase_subset j Finset.univ)
            intro x _ hx
            have hxj : ¬ j ≠ x := fun h =>
              hx (Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ x⟩)
            simp [hxj]
      _ = ∑ i ∈ Finset.univ.erase j, F i j := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mem_erase] at hk
            exact ite_eq_left (Ne.symm hk.1)
  simp only [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact h2 j

/-- General Horvitz-Thompson variance identity (Shalabh, Ch. 7, total form):
    the mean-squared error about the population total splits into a diagonal
    term and an off-diagonal term weighted by second-order inclusion. -/
theorem variance_horvitzThompsonTotal {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace (Finset α)] [MeasurableSingletonClass (Finset α)]
    (p : PMF (Finset α)) (y : α → ℝ)
    (hpos : ∀ i, 0 < inclusionProbability p i) :
    ∫ s, (horvitzThompsonTotal p y s - ∑ i, y i) ^ 2 ∂p.toMeasure
      = (∑ i, (1 - inclusionProbability p i) / inclusionProbability p i
          * y i ^ 2)
        + ∑ i, ∑ j ∈ Finset.univ.erase i,
          (pairInclusionProbability p i j
            - inclusionProbability p i * inclusionProbability p j)
            / (inclusionProbability p i * inclusionProbability p j)
            * (y i * y j) := by
  have hne : ∀ i, inclusionProbability p i ≠ 0 :=
    fun i => ne_of_gt (hpos i)
  have hdecomp : ∀ s : Finset α, horvitzThompsonTotal p y s - ∑ i, y i
      = ∑ i, (y i / inclusionProbability p i)
        * ((if i ∈ s then (1 : ℝ) else 0) - inclusionProbability p i) := by
    intro s
    have e1 : (∑ i ∈ s, y i / inclusionProbability p i)
        = ∑ i, (y i / inclusionProbability p i)
          * (if i ∈ s then (1 : ℝ) else 0) := by
      have hcongr : ∀ i ∈ s, y i / inclusionProbability p i
          = (y i / inclusionProbability p i)
            * (if i ∈ s then (1 : ℝ) else 0) := by
        intro i hi
        simp [hi]
      have hsub := Finset.sum_subset (Finset.subset_univ s)
        (f := fun i => (y i / inclusionProbability p i)
          * (if i ∈ s then (1 : ℝ) else 0))
        (by
          intro i _ his
          simp [his])
      rw [Finset.sum_congr rfl hcongr]
      exact hsub
    have e2 : (∑ i, y i)
        = ∑ i, (y i / inclusionProbability p i)
          * inclusionProbability p i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (div_mul_cancel₀ _ (hne i)).symm
    unfold horvitzThompsonTotal
    rw [e1, e2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsq : ∀ s : Finset α, (horvitzThompsonTotal p y s - ∑ i, y i) ^ 2
      = ∑ i, ∑ j, (((y i / inclusionProbability p i)
        * ((if i ∈ s then (1 : ℝ) else 0) - inclusionProbability p i))
        * ((y j / inclusionProbability p j)
        * ((if j ∈ s then (1 : ℝ) else 0) - inclusionProbability p j))) := by
    intro s
    rw [hdecomp s, pow_two, Finset.sum_mul_sum]
  have hfac : ∀ i j,
      (∑ s, (p s).toReal * ((((y i / inclusionProbability p i)
        * ((if i ∈ s then (1 : ℝ) else 0) - inclusionProbability p i))
        * ((y j / inclusionProbability p j)
        * ((if j ∈ s then (1 : ℝ) else 0) - inclusionProbability p j)))))
      = ((y i / inclusionProbability p i)
          * (y j / inclusionProbability p j))
        * ((if i = j then inclusionProbability p i
          else pairInclusionProbability p i j)
          - inclusionProbability p i * inclusionProbability p j) := by
    intro i j
    have hpt : ∀ s : Finset α, (p s).toReal
        * ((((y i / inclusionProbability p i)
        * ((if i ∈ s then (1 : ℝ) else 0) - inclusionProbability p i))
        * ((y j / inclusionProbability p j)
        * ((if j ∈ s then (1 : ℝ) else 0) - inclusionProbability p j))))
        = ((y i / inclusionProbability p i)
          * (y j / inclusionProbability p j))
          * ((p s).toReal * ((((if i ∈ s then (1 : ℝ) else 0)
          - inclusionProbability p i))
          * (((if j ∈ s then (1 : ℝ) else 0)
          - inclusionProbability p j)))) := by
      intro s
      ring
    rw [Finset.sum_congr rfl (fun s _ => hpt s), ← Finset.mul_sum,
      indicator_cov p i j]
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, hsq, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp only [hfac]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · have hni := hne i
    simp only [ite_true]
    field_simp
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_erase] at hj
    have hnij : i ≠ j := fun h => hj.1 h.symm
    have hni := hne i
    have hnj := hne j
    have hnijm : inclusionProbability p i * inclusionProbability p j ≠ 0 :=
      mul_ne_zero hni hnj
    rw [ite_eq_right hnij]
    field_simp

/-- Yates-Grundy form for fixed-size designs (Yates and Grundy (1953);
    Shalabh, Ch. 7): the variance equals half the weighted sum of squared
    pairwise contrasts. -/
theorem variance_horvitzThompsonTotal_fixed {α : Type*} [Fintype α]
    [DecidableEq α] [MeasurableSpace (Finset α)]
    [MeasurableSingletonClass (Finset α)] (p : PMF (Finset α)) (y : α → ℝ)
    (n : ℕ) (hpos : ∀ i, 0 < inclusionProbability p i)
    (hfix : ∀ s, p s ≠ 0 → s.card = n) :
    ∫ s, (horvitzThompsonTotal p y s - ∑ i, y i) ^ 2 ∂p.toMeasure
      = senYatesGrundyVariance p y := by
  have hne : ∀ i, inclusionProbability p i ≠ 0 :=
    fun i => ne_of_gt (hpos i)
  have hR : ∀ i, (∑ j ∈ Finset.univ.erase i,
      (inclusionProbability p i * inclusionProbability p j
        - pairInclusionProbability p i j))
      = inclusionProbability p i * (1 - inclusionProbability p i) := by
    intro i
    have h := row_sum_fixed p n hfix i
    have hneg : ∀ j ∈ Finset.univ.erase i,
        (inclusionProbability p i * inclusionProbability p j
          - pairInclusionProbability p i j)
        = -((pairInclusionProbability p i j)
          - inclusionProbability p i * inclusionProbability p j) := by
      intro j _
      ring
    rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib, h, neg_neg]
  have hsym : ∀ i j, pairInclusionProbability p i j
      = pairInclusionProbability p j i := by
    intro i j
    apply Finset.sum_congr rfl
    intro s _
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [hi, hj]
  have hexp : ∀ i j, (inclusionProbability p i * inclusionProbability p j
      - pairInclusionProbability p i j)
      * (y i / inclusionProbability p i
        - y j / inclusionProbability p j) ^ 2
      = ((inclusionProbability p i * inclusionProbability p j
        - pairInclusionProbability p i j)
        * (y i / inclusionProbability p i) ^ 2
        + (inclusionProbability p i * inclusionProbability p j
        - pairInclusionProbability p i j)
        * (y j / inclusionProbability p j) ^ 2)
        - 2 * ((inclusionProbability p i * inclusionProbability p j
        - pairInclusionProbability p i j)
        * ((y i / inclusionProbability p i)
        * (y j / inclusionProbability p j))) := by
    intro i j
    ring
  have hexp_all : (∑ i, ∑ j ∈ Finset.univ.erase i,
      (inclusionProbability p i * inclusionProbability p j
        - pairInclusionProbability p i j)
        * (y i / inclusionProbability p i
        - y j / inclusionProbability p j) ^ 2)
      = (∑ i, ∑ j ∈ Finset.univ.erase i,
          (inclusionProbability p i * inclusionProbability p j
            - pairInclusionProbability p i j)
            * (y i / inclusionProbability p i) ^ 2)
        + (∑ i, ∑ j ∈ Finset.univ.erase i,
          (inclusionProbability p i * inclusionProbability p j
            - pairInclusionProbability p i j)
            * (y j / inclusionProbability p j) ^ 2)
        - (∑ i, ∑ j ∈ Finset.univ.erase i,
          2 * ((inclusionProbability p i * inclusionProbability p j
            - pairInclusionProbability p i j)
            * ((y i / inclusionProbability p i)
            * (y j / inclusionProbability p j)))) := by
    simp only [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hT1 : (∑ i, ∑ j ∈ Finset.univ.erase i,
      (inclusionProbability p i * inclusionProbability p j
        - pairInclusionProbability p i j)
        * (y i / inclusionProbability p i) ^ 2)
      = ∑ i, (inclusionProbability p i * (1 - inclusionProbability p i))
        * (y i / inclusionProbability p i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, hR i]
  have hmid : (∑ i, ∑ j ∈ Finset.univ.erase i,
      (inclusionProbability p i * inclusionProbability p j
        - pairInclusionProbability p i j)
        * (y j / inclusionProbability p j) ^ 2)
      = ∑ i, (inclusionProbability p i * (1 - inclusionProbability p i))
        * (y i / inclusionProbability p i) ^ 2 := by
    rw [sum_erase_swap]
    apply Finset.sum_congr rfl
    intro j _
    have hsymm : ∀ i ∈ Finset.univ.erase j,
        (inclusionProbability p i * inclusionProbability p j
          - pairInclusionProbability p i j)
          * (y j / inclusionProbability p j) ^ 2
        = (inclusionProbability p j * inclusionProbability p i
          - pairInclusionProbability p j i)
          * (y j / inclusionProbability p j) ^ 2 := by
      intro k _
      rw [hsym k j, mul_comm (inclusionProbability p k)
        (inclusionProbability p j)]
    rw [Finset.sum_congr rfl hsymm, ← Finset.sum_mul, hR j]
  have hhalf : ∀ A B : ℝ, (1 / 2) * (A + A - B)
      = A + (-((1 / 2) * B)) := by
    intro A B
    ring
  have hD : (∑ i, (1 - inclusionProbability p i) / inclusionProbability p i
      * y i ^ 2)
      = ∑ i, (inclusionProbability p i * (1 - inclusionProbability p i))
        * (y i / inclusionProbability p i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    have hni := hne i
    field_simp
  have hOT : (∑ i, ∑ j ∈ Finset.univ.erase i,
      (pairInclusionProbability p i j
        - inclusionProbability p i * inclusionProbability p j)
        / (inclusionProbability p i * inclusionProbability p j)
        * (y i * y j))
      + (1 / 2) * (∑ i, ∑ j ∈ Finset.univ.erase i,
        2 * ((inclusionProbability p i * inclusionProbability p j
          - pairInclusionProbability p i j)
          * ((y i / inclusionProbability p i)
          * (y j / inclusionProbability p j)))) = 0 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hni := hne i
    have hnj := hne j
    have hnijm : inclusionProbability p i * inclusionProbability p j ≠ 0 :=
      mul_ne_zero hni hnj
    field_simp
    ring
  have hOeq : (∑ i, ∑ j ∈ Finset.univ.erase i,
      (pairInclusionProbability p i j
        - inclusionProbability p i * inclusionProbability p j)
        / (inclusionProbability p i * inclusionProbability p j)
        * (y i * y j))
      = -((1 / 2) * (∑ i, ∑ j ∈ Finset.univ.erase i,
        2 * ((inclusionProbability p i * inclusionProbability p j
          - pairInclusionProbability p i j)
          * ((y i / inclusionProbability p i)
          * (y j / inclusionProbability p j))))) :=
    eq_neg_of_add_eq_zero_left hOT
  rw [variance_horvitzThompsonTotal p y hpos]
  unfold senYatesGrundyVariance
  rw [hexp_all, hT1, hmid, hhalf, hD, hOeq]

/-- Expectation of the Sen-Yates-Grundy variance estimator: whenever every
    pair has positive inclusion probability, its expectation is the
    Sen-Yates-Grundy form `senYatesGrundyVariance`. This identity needs no
    fixed-size hypothesis, but the form is the variance of the
    Horvitz-Thompson total only for fixed-size designs; unbiasedness for the
    variance is `integral_senYatesGrundyEstimate_eq_variance`. -/
theorem integral_senYatesGrundyEstimate {α : Type*} [Fintype α]
    [DecidableEq α] [MeasurableSpace (Finset α)]
    [MeasurableSingletonClass (Finset α)] (p : PMF (Finset α)) (y : α → ℝ)
    (hpij : ∀ i j, i ≠ j → 0 < pairInclusionProbability p i j) :
    ∫ s, senYatesGrundyEstimate p y s ∂p.toMeasure
      = senYatesGrundyVariance p y := by
  have hinner : ∀ (F : α → α → ℝ) (s : Finset α) (i : α), i ∈ s →
      (∑ j ∈ s.erase i, F i j)
      = ∑ j ∈ Finset.univ.erase i,
        (if i ∈ s ∧ j ∈ s then F i j else 0) := by
    intro F s i hi
    calc (∑ j ∈ s.erase i, F i j)
        = ∑ j ∈ s.erase i, (if i ∈ s ∧ j ∈ s then F i j else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_erase] at hj
          simp [hi, hj.2]
      _ = ∑ j ∈ Finset.univ.erase i,
          (if i ∈ s ∧ j ∈ s then F i j else 0) := by
          apply Finset.sum_subset
            (Finset.erase_subset_erase i (Finset.subset_univ s))
          intro j hj hjn
          rw [Finset.mem_erase] at hj hjn
          by_cases hjs : j ∈ s
          · exfalso
            exact hjn ⟨hj.1, hjs⟩
          · simp [hjs]
  have houter : ∀ (G : α → ℝ) (s : Finset α),
      (∑ i ∈ s, G i) = ∑ i, (if i ∈ s then G i else 0) := by
    intro G s
    calc (∑ i ∈ s, G i) = ∑ i ∈ s, (if i ∈ s then G i else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [hi]
      _ = ∑ i, (if i ∈ s then G i else 0) :=
          Finset.sum_subset (Finset.subset_univ s) (by
            intro i _ his
            simp [his])
  have hconv1 : ∀ (F : α → α → ℝ) (s : Finset α),
      (∑ i ∈ s, ∑ j ∈ s.erase i, F i j)
      = ∑ i, ∑ j ∈ Finset.univ.erase i,
        (if i ∈ s ∧ j ∈ s then F i j else 0) := by
    intro F s
    rw [houter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ s
    · rw [ite_eq_left hi]
      exact hinner F s i hi
    · rw [ite_eq_right hi]
      symm
      apply Finset.sum_eq_zero
      intro j _
      simp [hi]
  have hper : ∀ i j, i ≠ j →
      (∑ s, (p s).toReal * (if i ∈ s ∧ j ∈ s
        then (((inclusionProbability p i * inclusionProbability p j
          - pairInclusionProbability p i j)
          / pairInclusionProbability p i j)
          * ((y i / inclusionProbability p i
          - y j / inclusionProbability p j) ^ 2)) else 0))
      = (inclusionProbability p i * inclusionProbability p j
        - pairInclusionProbability p i j)
        * ((y i / inclusionProbability p i
        - y j / inclusionProbability p j) ^ 2) := by
    intro i j hij
    have hρ : pairInclusionProbability p i j ≠ 0 :=
      ne_of_gt (hpij i j hij)
    have hsplit : ∀ s : Finset α, (p s).toReal
        * (if i ∈ s ∧ j ∈ s
          then (((inclusionProbability p i * inclusionProbability p j
          - pairInclusionProbability p i j)
          / pairInclusionProbability p i j)
          * ((y i / inclusionProbability p i
          - y j / inclusionProbability p j) ^ 2)) else 0)
        = ((if i ∈ s ∧ j ∈ s then (p s).toReal else 0))
          * ((((inclusionProbability p i * inclusionProbability p j
          - pairInclusionProbability p i j)
          / pairInclusionProbability p i j))
          * ((y i / inclusionProbability p i
          - y j / inclusionProbability p j) ^ 2)) := by
      intro s
      by_cases h : i ∈ s ∧ j ∈ s <;> simp [h]
    have hE0 : (∑ s, (if i ∈ s ∧ j ∈ s then (p s).toReal else 0))
        = pairInclusionProbability p i j := rfl
    rw [Finset.sum_congr rfl (fun s _ => hsplit s), ← Finset.sum_mul,
      hE0]
    field_simp
  have hstep : (∑ s, (p s).toReal * (∑ i ∈ s, ∑ j ∈ s.erase i,
      (((inclusionProbability p i * inclusionProbability p j
        - pairInclusionProbability p i j)
        / pairInclusionProbability p i j))
        * ((y i / inclusionProbability p i
        - y j / inclusionProbability p j) ^ 2)))
      = (∑ s, (p s).toReal * (∑ i, ∑ j ∈ Finset.univ.erase i,
        (if i ∈ s ∧ j ∈ s
          then (((inclusionProbability p i * inclusionProbability p j
          - pairInclusionProbability p i j)
          / pairInclusionProbability p i j))
          * ((y i / inclusionProbability p i
          - y j / inclusionProbability p j) ^ 2) else 0))) := by
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    exact hconv1 _ s
  have hfactor : ∀ s : Finset α, (p s).toReal
      * ((1 / 2) * ∑ i ∈ s, ∑ j ∈ s.erase i,
        (((inclusionProbability p i * inclusionProbability p j
          - pairInclusionProbability p i j)
          / pairInclusionProbability p i j))
          * ((y i / inclusionProbability p i
          - y j / inclusionProbability p j) ^ 2))
      = (1 / 2) * ((p s).toReal * (∑ i ∈ s, ∑ j ∈ s.erase i,
        (((inclusionProbability p i * inclusionProbability p j
          - pairInclusionProbability p i j)
          / pairInclusionProbability p i j))
          * ((y i / inclusionProbability p i
          - y j / inclusionProbability p j) ^ 2))) := by
    intro s
    ring
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  unfold senYatesGrundyEstimate senYatesGrundyVariance
  simp only [hfactor, ← Finset.mul_sum]
  congr 1
  rw [hstep]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_erase] at hj
  exact hper i j (fun h => hj.1 h.symm)

/-- For fixed-size designs with positive pair inclusion probabilities, the
    Sen-Yates-Grundy estimator is unbiased for the mean-squared error
    (Shalabh, Ch. 7): its expectation equals the variance integral. -/
theorem integral_senYatesGrundyEstimate_eq_variance {α : Type*} [Fintype α]
    [DecidableEq α] [MeasurableSpace (Finset α)]
    [MeasurableSingletonClass (Finset α)] (p : PMF (Finset α)) (y : α → ℝ)
    (n : ℕ) (hpos : ∀ i, 0 < inclusionProbability p i)
    (hfix : ∀ s, p s ≠ 0 → s.card = n)
    (hpij : ∀ i j, i ≠ j → 0 < pairInclusionProbability p i j) :
    ∫ s, senYatesGrundyEstimate p y s ∂p.toMeasure
      = ∫ s, (horvitzThompsonTotal p y s - ∑ i, y i) ^ 2 ∂p.toMeasure := by
  rw [integral_senYatesGrundyEstimate p y hpij,
    variance_horvitzThompsonTotal_fixed p y n hpos hfix]

end MathlibExt.Probability.Sampling
