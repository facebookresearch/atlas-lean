/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Adapted from `eth/proof/rates/ClauseBound/Group/Sample.lean` and
`eth/proof/rates/ClauseBound/Rec/Tail.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
extract the finite sampling bound over `Finset.powersetCard`, keep proof-only lemmas private,
and derive the two-point estimate from Mathlib's canonical sub-Gaussian interval bound.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Probability.Moments.SubGaussian

/-!
# Hoeffding bound for sampling without replacement

Among the `n`-element subsets of a nonempty finite population with weights in `[0, R]`, the
number whose total weight exceeds the expected total by at least `t * n * R` is at most
`exp (-2 * n * t ^ 2)` times the number of all `n`-element subsets.

The proof bounds elementary symmetric sums by a power of the arithmetic mean, then applies a
Chernoff estimate. The two-point exponential-moment estimate is obtained from Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`.
-/

@[expose] public section

namespace Finset

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- Hoeffding's two-point exponential-moment bound, specialized from Mathlib's interval bound. -/
private theorem two_point_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    p * Real.exp (θ * (1 - p)) + (1 - p) * Real.exp (θ * (0 - p)) ≤
      Real.exp (θ ^ 2 / 8) := by
  open MeasureTheory ProbabilityTheory in
  let μ : Measure ℝ :=
    ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac 0
  have hq0 : 0 ≤ 1 - p := by linarith
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp0 hq0]
    simp
  have hint (f : ℝ → ℝ) : ∫ y, f y ∂μ = p * f 1 + (1 - p) * f 0 := by
    have h1 : Integrable f (ENNReal.ofReal p • Measure.dirac (1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    have h0 : Integrable f (ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    rw [integral_add_measure h1 h0, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal hq0]
    simp
  have hb : ∀ᵐ y ∂μ, id y ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [μ]
    rw [ae_add_measure_iff]
    constructor
    · refine Measure.ae_smul_measure ?_ _
      rw [ae_dirac_eq]
      simp
    · refine Measure.ae_smul_measure ?_ _
      rw [ae_dirac_eq]
      simp
  have h :=
    (hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := id) aemeasurable_id hb).mgf_le θ
  have hmean : ∫ y, id y ∂μ = p := by
    rw [hint]
    simp
  rw [hmean, mgf, hint] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  simp
  ring

/-- The tangent inequality used in the elementary-symmetric-sum induction. -/
private theorem tangent_le (u w : ℝ) (hu : 0 ≤ u) (hw : 0 ≤ w) (k : ℕ) :
    ((k : ℝ) + 1) * w * u ^ k ≤ w ^ (k + 1) + k * u ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have key : 0 ≤ (w ^ (k + 1) - u ^ (k + 1)) * (w - u) := by
      rcases le_total u w with h | h
      · exact
          mul_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hu h _)) (sub_nonneg.2 h)
      · exact
          mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (pow_le_pow_left₀ hw h _))
            (sub_nonpos.2 h)
    have h2 := mul_le_mul_of_nonneg_right ih hu
    push_cast
    simp only [pow_succ] at key h2 ⊢
    generalize u ^ k = A at *
    generalize w ^ k = W at *
    nlinarith

/-- The subset-product sum after adjoining one element. -/
private theorem sum_powersetCard_insert {a : ι} {s : Finset ι} (ha : a ∉ s)
    (x : ι → ℝ) (k : ℕ) :
    ∑ S ∈ powersetCard (k + 1) (insert a s), ∏ i ∈ S, x i =
      ∑ S ∈ powersetCard (k + 1) s, ∏ i ∈ S, x i +
        x a * ∑ S ∈ powersetCard k s, ∏ i ∈ S, x i := by
  have hnot : ∀ {m : ℕ} {S : Finset ι}, S ∈ powersetCard m s → a ∉ S :=
    fun hS h => ha ((mem_powersetCard.1 hS).1 h)
  rw [powersetCard_succ_insert ha, sum_union, sum_image, mul_sum]
  · congr 1
    refine sum_congr rfl fun S hS => ?_
    rw [prod_insert (hnot hS)]
  · intro S hS U hU h
    have h' := congrArg (fun V => V.erase a) h
    simpa [erase_insert (hnot hS), erase_insert (hnot hU)] using h'
  · rw [disjoint_left]
    intro S hS hS'
    obtain ⟨U, _, rfl⟩ := mem_image.1 hS'
    exact hnot hS (mem_insert_self a U)

/-- A Maclaurin bound for elementary symmetric sums of nonnegative weights. -/
private theorem esymm_le (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∀ n : ℕ,
      ∑ S ∈ powersetCard n s, ∏ i ∈ S, x i ≤
        ((#s).choose n : ℝ) * ((∑ i ∈ s, x i) / #s) ^ n := by
  induction s using Finset.induction_on with
  | empty =>
    intro n
    rcases n with _ | n
    · simp
    · have h : powersetCard (n + 1) (∅ : Finset ι) = ∅ :=
        powersetCard_eq_empty.2 (by simp)
      simp [h]
  | insert a s ha ih =>
    intro n
    rcases n with _ | k
    · simp
    have hxa : 0 ≤ x a := hx a (mem_insert_self a s)
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (mem_insert_of_mem hi)
    have ih1 := ih hxs (k + 1)
    have ih0 := ih hxs k
    have hS0 : 0 ≤ ∑ i ∈ s, x i := sum_nonneg hxs
    rw [sum_powersetCard_insert ha, card_insert_of_notMem ha, sum_insert ha]
    have hNu : (#s : ℝ) * ((∑ i ∈ s, x i) / #s) = ∑ i ∈ s, x i := by
      by_cases h0 : #s = 0
      · rw [card_eq_zero.1 h0]
        simp
      · have : (#s : ℝ) ≠ 0 := by exact_mod_cast h0
        field_simp
    have hNw :
        ((#s : ℝ) + 1) * ((x a + ∑ i ∈ s, x i) / ((#s : ℝ) + 1)) =
          x a + ∑ i ∈ s, x i := by
      have : (#s : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    have hu : 0 ≤ (∑ i ∈ s, x i) / #s := by positivity
    have hw : 0 ≤ (x a + ∑ i ∈ s, x i) / ((#s : ℝ) + 1) := by positivity
    have h1 :
        ((#s : ℝ) + 1) * ((#s).choose k : ℝ) =
          ((#s + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (#s) k
    have h2 :
        ((#s + 1).choose (k + 1) : ℝ) =
          ((#s).choose k : ℝ) + ((#s).choose (k + 1) : ℝ) := by
      exact_mod_cast Nat.choose_succ_succ (#s) k
    push_cast
    generalize (∑ i ∈ s, x i) / #s = u at *
    generalize (x a + ∑ i ∈ s, x i) / ((#s : ℝ) + 1) = w at *
    have hv : x a = ((#s : ℝ) + 1) * w - #s * u := by linarith
    have ht := tangent_le u w hu hw k
    calc
      ∑ S ∈ powersetCard (k + 1) s, ∏ i ∈ S, x i +
          x a * ∑ S ∈ powersetCard k s, ∏ i ∈ S, x i ≤
          ((#s).choose (k + 1) : ℝ) * u ^ (k + 1) +
            x a * (((#s).choose k : ℝ) * u ^ k) :=
        add_le_add ih1 (mul_le_mul_of_nonneg_left ih0 hxa)
      _ = ((#s + 1).choose (k + 1) : ℝ) *
          (((k : ℝ) + 1) * w * u ^ k - k * u ^ (k + 1)) := by
        rw [hv]
        linear_combination
          (w * u ^ k - u ^ (k + 1)) * h1 - u ^ (k + 1) * h2
      _ ≤ ((#s + 1).choose (k + 1) : ℝ) * w ^ (k + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

omit [DecidableEq ι] in
/-- The exponential average bound used by the Chernoff argument. -/
private theorem avg_exp_le (s : Finset ι) (c : ι → ℝ) {R : ℝ} (hR : 0 < R)
    (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ R) (hs : s.Nonempty) (θ : ℝ) :
    (∑ i ∈ s, Real.exp (θ * c i)) / #s ≤
      Real.exp (θ * ((∑ i ∈ s, c i) / #s) + (θ * R) ^ 2 / 8) := by
  have hN : (0 : ℝ) < #s := by exact_mod_cast card_pos.2 hs
  have h1 :
      ∀ i ∈ s,
        Real.exp (θ * c i) ≤ (1 - c i / R) + c i / R * Real.exp (θ * R) := by
    intro i hi
    obtain ⟨h0, hle⟩ := hc i hi
    have hb : 0 ≤ c i / R := by positivity
    have ha : 0 ≤ 1 - c i / R := by
      rw [sub_nonneg, div_le_one hR]
      exact hle
    have h :=
      convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (θ * R)) ha hb (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
    rwa [show c i / R * (θ * R) = θ * c i by field_simp] at h
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (∑ i ∈ s, c i) / #s / R := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i ∈ s, c i := sum_nonneg fun i hi => (hc i hi).1
  have hsumR : ∑ i ∈ s, c i ≤ #s * R := by
    calc
      ∑ i ∈ s, c i ≤ ∑ _i ∈ s, R := sum_le_sum fun i hi => (hc i hi).2
      _ = #s * R := by rw [sum_const, nsmul_eq_mul]
  have hp0 : 0 ≤ p := by
    rw [hp]
    positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_div, div_le_one (by positivity)]
    exact hsumR
  have h2 :
      (∑ i ∈ s, Real.exp (θ * c i)) / #s ≤ (1 - p) + p * Real.exp (θ * R) := by
    rw [div_le_iff₀ hN]
    calc
      ∑ i ∈ s, Real.exp (θ * c i) ≤
          ∑ i ∈ s, ((1 - c i / R) + c i / R * Real.exp (θ * R)) :=
        sum_le_sum h1
      _ = #s - (∑ i ∈ s, c i) / R +
          (∑ i ∈ s, c i) / R * Real.exp (θ * R) := by
        rw [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one,
          ← sum_div, ← sum_mul, ← sum_div]
      _ = ((1 - p) + p * Real.exp (θ * R)) * #s := by
        rw [hp]
        field_simp
  have h3 := two_point_le hp0 hp1 (θ * R)
  have h4 :
      (1 - p) + p * Real.exp (θ * R) =
        (p * Real.exp (θ * R * (1 - p)) +
          (1 - p) * Real.exp (θ * R * (0 - p))) * Real.exp (θ * R * p) := by
    have e1 :
        Real.exp (θ * R * (1 - p)) * Real.exp (θ * R * p) = Real.exp (θ * R) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 :
        Real.exp (θ * R * (0 - p)) * Real.exp (θ * R * p) = 1 := by
      rw [← Real.exp_add, show θ * R * (0 - p) + θ * R * p = 0 by ring,
        Real.exp_zero]
    linear_combination (-p) * e1 - (1 - p) * e2
  have h5 : θ * ((∑ i ∈ s, c i) / #s) = θ * R * p := by
    rw [hp]
    field_simp
  rw [h5, add_comm, Real.exp_add]
  refine h2.trans ?_
  rw [h4]
  exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le

/--
Hoeffding's upper-tail bound for sampling without replacement, stated as a count.

Among the `n`-element subsets `S` of `s`, at most
`exp (-2 * n * t ^ 2) * choose (#s) n` satisfy
`n * mean(c) + t * n * R ≤ ∑ i ∈ S, c i`. The event is non-strict; `n = 0` and
`#s < n` are included without separate assumptions.
-/
theorem card_sample_tail_le (s : Finset ι) (c : ι → ℝ) {R t : ℝ} (hR : 0 < R)
    (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ R) (hs : s.Nonempty) (n : ℕ) (ht : 0 ≤ t) :
    (#{S ∈ powersetCard n s |
        n * ((∑ i ∈ s, c i) / #s) + t * n * R ≤ ∑ i ∈ S, c i} : ℝ) ≤
      Real.exp (-(2 * n * t ^ 2)) * ((#s).choose n : ℝ) := by
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 4 * t / R := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by
    rw [hθ]
    positivity
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = (∑ i ∈ s, c i) / #s := ⟨_, rfl⟩
  rw [← hμ]
  have h1 :
      (#{S ∈ powersetCard n s |
          n * μ + t * n * R ≤ ∑ i ∈ S, c i} : ℝ) *
          Real.exp (θ * (n * μ + t * n * R)) ≤
        ∑ S ∈ powersetCard n s, ∏ i ∈ S, Real.exp (θ * c i) := by
    calc
      (#{S ∈ powersetCard n s |
          n * μ + t * n * R ≤ ∑ i ∈ S, c i} : ℝ) *
          Real.exp (θ * (n * μ + t * n * R)) =
          ∑ _S ∈ powersetCard n s with n * μ + t * n * R ≤ ∑ i ∈ _S, c i,
            Real.exp (θ * (n * μ + t * n * R)) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ S ∈ powersetCard n s with n * μ + t * n * R ≤ ∑ i ∈ S, c i,
          ∏ i ∈ S, Real.exp (θ * c i) := by
        refine sum_le_sum fun S hS => ?_
        rw [← Real.exp_sum, ← mul_sum]
        exact
          Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left (mem_filter.1 hS).2 hθ0)
      _ ≤ ∑ S ∈ powersetCard n s, ∏ i ∈ S, Real.exp (θ * c i) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun S _ _ => prod_nonneg fun i _ => (Real.exp_pos _).le
  have h2 :=
    esymm_le s (fun i => Real.exp (θ * c i)) (fun i _ => (Real.exp_pos _).le) n
  have h3 :
      ((∑ i ∈ s, Real.exp (θ * c i)) / #s) ^ n ≤
        Real.exp (n * (θ * μ + (θ * R) ^ 2 / 8)) := by
    rw [Real.exp_nat_mul, hμ]
    exact pow_le_pow_left₀ (by positivity) (avg_exp_le s c hR hc hs θ) n
  have h4 :
      (#{S ∈ powersetCard n s |
          n * μ + t * n * R ≤ ∑ i ∈ S, c i} : ℝ) *
          Real.exp (θ * (n * μ + t * n * R)) ≤
        ((#s).choose n : ℝ) * Real.exp (n * (θ * μ + (θ * R) ^ 2 / 8)) :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
  have h5 :
      Real.exp (n * (θ * μ + (θ * R) ^ 2 / 8)) =
        Real.exp (-(2 * n * t ^ 2)) * Real.exp (θ * (n * μ + t * n * R)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hθ]
    field_simp
    ring
  rw [h5, ← mul_assoc] at h4
  have h6 := le_of_mul_le_mul_right h4 (Real.exp_pos _)
  linarith

end Finset
