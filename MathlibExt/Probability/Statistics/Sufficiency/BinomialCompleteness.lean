/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Binomial
public import Mathlib.Probability.Distributions.Binomial
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Module
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Probability.Statistics.Sufficiency.Complete

/-!
# Binomial-count completeness on an interior interval

For fixed `n ≥ 1`, the family `{Binomial(n,p) : p ∈ Set.Ioo a b}` with `0 < a < b < 1`
is complete in the count statistic: the Bernstein-polynomial identity on a nontrivial
interval forces every zero-mean function to vanish almost everywhere under each law.

The a.e.-zero support lemma `binomial_ae_eq_zero_of_eq_zero_on_Iic` is public (not
private) because the test module's boundary fixture uses it directly.

References: completeness was introduced in Lehmann, E. L. and Scheffé, H. (1950),
"Completeness, similar regions, and unbiased estimation. I.", Sankhyā 10(4): 305–340
(JSTOR 25048038). The binomial case follows from the general result that a full-rank
exponential family has a complete sufficient statistic; see Lehmann, E. L. and
Casella, G., Theory of Point Estimation, 2nd edition (Springer Texts in Statistics,
Springer, 1998), Chapter 1.

Source: this formalization proves the Bernstein-polynomial identity on the nontrivial
interval directly — a zero-mean function yields a polynomial with infinitely many roots
(`Polynomial.eq_zero_of_infinite_isRoot` over the injective reparameterization
`p ↦ p / (1 - p)`), forcing every coefficient, hence every value on `{k | k ≤ n}`, to
vanish — rather than routing through the exponential-family theorem.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Sufficiency

open MeasureTheory

/-- Coefficient polynomial `∑ k ≤ n, C(n,k) * u k * X^k`. -/
private noncomputable def binomPoly (n : ℕ) (u : ℕ → ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.Iic n, Polynomial.monomial k ((n.choose k : ℝ) * u k)

/-- Evaluating `binomPoly` at `p / (1 - p)` recovers the Bernstein sum scaled by `(1 - p)^n`. -/
private theorem binomPoly_eval_mul (n : ℕ) (u : ℕ → ℝ) (p : ℝ) (hp1 : p < 1) :
    (binomPoly n u).eval (p / (1 - p)) * (1 - p) ^ n
      = ∑ k ∈ Finset.Iic n, ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) * u k := by
  have h1p : (0:ℝ) < 1 - p := sub_pos.mpr hp1
  have hq : (1:ℝ) - p ≠ 0 := ne_of_gt h1p
  unfold binomPoly
  rw [Polynomial.eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Polynomial.eval_monomial]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Finset.mem_Iic.mp hk)
  have hnk : k + j - k = j := by rw [add_comm k j, Nat.add_sub_cancel]
  rw [hnk, pow_add]
  have key : (p / (1 - p)) ^ k * (1 - p) ^ k = p ^ k := by
    rw [← mul_pow, div_mul_cancel₀ _ hq]
  have hLHS : (((k + j).choose k : ℝ) * u k) * (p / (1 - p)) ^ k *
      ((1 - p) ^ k * (1 - p) ^ j)
      = (((k + j).choose k : ℝ) * u k) *
        ((p / (1 - p)) ^ k * (1 - p) ^ k) * (1 - p) ^ j := by ring
  rw [hLHS, key]
  ring

/-- Coefficients of `binomPoly` on its support. -/
private theorem binomPoly_coeff (n : ℕ) (u : ℕ → ℝ) (k : ℕ) (hk : k ∈ Finset.Iic n) :
    (binomPoly n u).coeff k = (n.choose k : ℝ) * u k := by
  unfold binomPoly
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k
    (fun b _ hb => by rw [Polynomial.coeff_monomial]; exact ite_eq_right hb)
    (fun h => absurd hk h)]
  rw [Polynomial.coeff_monomial]
  exact ite_eq_left rfl

/-- The reparameterization `p ↦ p / (1 - p)` is injective on the interior interval. -/
private theorem div_one_sub_injective_on_Ioo {a b : ℝ} (hb : b < 1) :
    Function.Injective (fun p : Set.Ioo a b => (p.val : ℝ) / (1 - p.val)) := by
  intro x y h
  have hx1 : (1:ℝ) - x.val ≠ 0 :=
    ne_of_gt (sub_pos.mpr (lt_trans x.property.2 hb))
  have hy1 : (1:ℝ) - y.val ≠ 0 :=
    ne_of_gt (sub_pos.mpr (lt_trans y.property.2 hb))
  simp only at h
  field_simp at h
  apply Subtype.ext
  linear_combination h

/-- A function vanishing on `{k | k ≤ n}` is a.e. zero under every `Bin(n, p)` law. -/
theorem binomial_ae_eq_zero_of_eq_zero_on_Iic (n : ℕ) (p : ↥unitInterval)
    (u : ℕ → ℝ) (hu : ∀ k, k ≤ n → u k = 0) :
    u =ᵐ[ProbabilityTheory.binomial n p] 0 := by
  have hnull : ProbabilityTheory.binomial n p (Set.Ioi n) = 0 := by
    rw [ProbabilityTheory.binomial_eq_sum_dirac, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Measure.smul_apply]
    have hk' : k ∉ Set.Ioi n :=
      fun h => not_le_of_gt (Set.mem_Ioi.mp h) (Finset.mem_Iic.mp hk)
    rw [Measure.dirac_apply, Set.indicator_of_notMem hk']
    exact smul_zero _
  have hsub : {k | u k = 0}ᶜ ⊆ Set.Ioi n := by
    intro k hk
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hk
    rw [Set.mem_Ioi]
    by_contra hle
    exact hk (hu k (le_of_not_gt hle))
  exact mem_ae_iff.mpr (measure_mono_null hsub hnull)

set_option linter.unusedVariables false in
/-- **Binomial-count completeness on an interior interval.** For fixed `n ≥ 1`, the family
`{Binomial(n,p) : p ∈ Set.Ioo a b}` with `0 < a < b < 1` is complete in the count
statistic: the Bernstein-polynomial identity on a nontrivial interval forces every
zero-mean `u` to vanish almost everywhere under each law. The hypothesis `hn` is not
needed by this proof; it records the finite-sample regime of the pinned statement. -/
theorem isCompleteStatistic_binomial_count (n : ℕ) (hn : 1 ≤ n)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    IsCompleteStatistic
      (fun p : Set.Ioo a b =>
        ⟨ProbabilityTheory.binomial n ⟨p.val, by
          constructor
          · exact le_trans ha.le p.property.1.le
          · exact le_trans p.property.2.le hb.le⟩,
        by infer_instance⟩)
      (id : ℕ → ℕ) := by
  constructor
  · exact measurable_id
  · intro u hu hint hzero p₀
    have hsum : ∀ p : Set.Ioo a b,
        ∑ k ∈ Finset.Iic n, ((n.choose k : ℝ) * p.val ^ k * (1 - p.val) ^ (n - k)) * u k = 0 := by
      intro p
      have h0 := hzero p
      change ∫ ω, u (id ω) ∂(ProbabilityTheory.binomial n ⟨p.val, _⟩) = 0 at h0
      rw [ProbabilityTheory.integral_binomial] at h0
      exact h0
    have hvan : ∀ p : Set.Ioo a b, (binomPoly n u).eval (p.val / (1 - p.val)) = 0 := by
      intro p
      have hp1 : p.val < 1 := lt_trans p.property.2 hb
      have h1p : (0:ℝ) < 1 - p.val := sub_pos.mpr hp1
      have hpow : (1 - p.val) ^ n ≠ 0 := pow_ne_zero n (ne_of_gt h1p)
      have hmul := binomPoly_eval_mul n u p.val hp1
      rw [hsum p] at hmul
      exact (mul_eq_zero.mp hmul).resolve_right hpow
    have hpoly : binomPoly n u = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      have hIoo := Set.Ioo.infinite hab
      refine Set.infinite_of_injective_forall_mem
        (div_one_sub_injective_on_Ioo (a := a) hb) (fun p => ?_)
      show (fun p : Set.Ioo a b => p.val / (1 - p.val)) p ∈ {x | (binomPoly n u).IsRoot x}
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def]
      exact hvan p
    have hcoeff : ∀ k, k ≤ n → u k = 0 := by
      intro k hk
      have hk' : k ∈ Finset.Iic n := Finset.mem_Iic.mpr hk
      have h0 : (binomPoly n u).coeff k = 0 := by
        rw [hpoly]
        exact Polynomial.coeff_zero k
      rw [binomPoly_coeff n u k hk'] at h0
      have hne : (n.choose k : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
      exact (mul_eq_zero.mp h0).resolve_left hne
    exact binomial_ae_eq_zero_of_eq_zero_on_Iic n ⟨p₀.val, by
      constructor
      · exact le_trans ha.le p₀.property.1.le
      · exact le_trans p₀.property.2.le hb.le⟩ u hcoeff

end MathlibExt.Probability.Statistics.Sufficiency
