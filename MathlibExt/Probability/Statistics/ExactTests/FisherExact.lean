/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Hypergeometric
public import MathlibExt.Probability.Statistics.ExactTests.TailPValue
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Independence.Basic

import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Fisher's exact test: the conditional law of a 2×2 table given its margins

Let `X ~ Bin(n₁, p)` and `Y ~ Bin(n₂, p)` be independent counts of successes in two groups of
sizes `n₁` and `n₂` with a common success probability `p` (the null hypothesis of Fisher's exact
test for a 2×2 table). Then `X + Y ~ Bin(n₁ + n₂, p)`, and, given the margin `X + Y = t`, the
cell `X` has the hypergeometric law

`P(X = k | X + Y = t) = C(n₁, k) C(n₂, t - k) / C(n₁ + n₂, t)`,

which does not depend on the nuisance parameter `p`. This is the null distribution of Fisher's
exact test.

## Main results

* `measureReal_add_eq_binomial`: the sum of independent `Bin(n₁, p)` and `Bin(n₂, p)` counts is
  `Bin(n₁ + n₂, p)`.
* `cond_measureReal_eq_hypergeometricReal`: for `0 < p < 1` and `t ≤ n₁ + n₂`,
  `P(X = k | X + Y = t) = hypergeometricReal (n₁ + n₂) n₁ t k`.
* `hasLaw_cond_hypergeometric`: given `X + Y = t`, `X` has the law
  `hypergeometric (n₁ + n₂) n₁ t`.
* `isValidPValue_fisherUpper_cond`: the one-sided (upper) Fisher exact p-value
  `fisherUpperPValue` is valid conditionally on the margin, for every nuisance `p ∈ (0, 1)`.
* `fisherUpperPValue_eq_sum`: the p-value is the hypergeometric tail sum over `[X ω, t]`.

## References

* R. A. Fisher, *Statistical Methods for Research Workers*, 5th ed., Oliver and Boyd (1934),
  §21.02.
* R. A. Fisher, *The logic of inductive inference*, J. R. Statist. Soc. 98 (1935), 39–82.
* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  §4.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped unitInterval

namespace MathlibExt.Probability.Statistics.ExactTests

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℕ} {n₁ n₂ : ℕ} {p : I}

/-- The joint mass of two independent binomial counts with `X + Y = t`, at `X = k ≤ t`. -/
private lemma measureReal_eq_and_eq (hX : HasLaw X Bin(n₁, p) μ) (hY : HasLaw Y Bin(n₂, p) μ)
    (hXY : IndepFun X Y μ) {k t : ℕ} (hk : k ≤ t) :
    μ.real {ω | X ω = k ∧ Y ω = t - k} =
      n₁.choose k * n₂.choose (t - k) * ((p : ℝ) ^ t * (1 - p) ^ (n₁ + n₂ - t)) := by
  have hX' : μ.real {ω | X ω = k} = Bin(n₁, p).real {k} :=
    hX.measureReal_eq (p := (· = k)) (measurableSet_singleton k)
  have hY' : μ.real {ω | Y ω = t - k} = Bin(n₂, p).real {t - k} :=
    hY.measureReal_eq (p := (· = t - k)) (measurableSet_singleton (t - k))
  have hind : μ.real {ω | X ω = k ∧ Y ω = t - k} =
      μ.real {ω | X ω = k} * μ.real {ω | Y ω = t - k} := by
    have := hXY.measure_inter_preimage_eq_mul {k} {t - k} (measurableSet_singleton k)
      (measurableSet_singleton (t - k))
    simp only [measureReal_def]
    rw [← ENNReal.toReal_mul]
    exact congrArg ENNReal.toReal this
  rw [hind, hX', hY', binomial_real_singleton, binomial_real_singleton]
  by_cases h : k ≤ n₁ ∧ t - k ≤ n₂
  · have hp : (p : ℝ) ^ t = (p : ℝ) ^ k * (p : ℝ) ^ (t - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hk]
    have hq : (1 - (p : ℝ)) ^ (n₁ + n₂ - t) =
        (1 - (p : ℝ)) ^ (n₁ - k) * (1 - (p : ℝ)) ^ (n₂ - (t - k)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp, hq]
    ring
  · rcases not_and_or.1 h with h | h <;>
      simp [Nat.choose_eq_zero_of_lt (not_le.1 h)]

omit [MeasurableSpace Ω] in
/-- The event `X + Y = t` is the disjoint union over `k ≤ t` of the events
`X = k, Y = t - k`. -/
private lemma setOf_add_eq (t : ℕ) :
    {ω | X ω + Y ω = t} = ⋃ k ∈ range (t + 1), {ω | X ω = k ∧ Y ω = t - k} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_range, exists_prop]
  constructor
  · intro h
    exact ⟨X ω, by omega, rfl, by omega⟩
  · rintro ⟨k, hk, rfl, h⟩
    omega

/-- **Sum of independent binomials.** If `X ~ Bin(n₁, p)` and `Y ~ Bin(n₂, p)` are independent,
then `X + Y ~ Bin(n₁ + n₂, p)`: `P(X + Y = t) = C(n₁ + n₂, t) p^t (1 - p)^(n₁ + n₂ - t)`. -/
theorem measureReal_add_eq_binomial (hXm : Measurable X) (hYm : Measurable Y)
    (hX : HasLaw X Bin(n₁, p) μ) (hY : HasLaw Y Bin(n₂, p) μ) (hXY : IndepFun X Y μ) (t : ℕ) :
    μ.real {ω | X ω + Y ω = t} = Bin(n₁ + n₂, p).real {t} := by
  have hfin : IsFiniteMeasure μ := hX.isFiniteMeasure
  rw [setOf_add_eq, measureReal_biUnion_finset, binomial_real_singleton]
  · rw [Finset.sum_congr rfl fun k hk =>
      measureReal_eq_and_eq hX hY hXY (Nat.lt_succ_iff.1 (mem_range.1 hk)), ← Finset.sum_mul,
      mul_assoc]
    congr 1
    have h := Nat.add_choose_eq n₁ n₂ t
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => n₁.choose i * n₂.choose j)] at h
    exact_mod_cast h.symm
  · intro i _ j _ hij
    exact Set.disjoint_left.2 fun ω hi hj => hij (hi.1.symm.trans hj.1)
  · intro k _
    exact (hXm (measurableSet_singleton k)).inter (hYm (measurableSet_singleton (t - k)))

/-- **Fisher's exact conditional law.** Let `X ~ Bin(n₁, p)` and `Y ~ Bin(n₂, p)` be independent
with a common `p ∈ (0, 1)`. Given the margin `X + Y = t` with `t ≤ n₁ + n₂`, the cell `X` is
hypergeometric: `P(X = k | X + Y = t) = C(n₁, k) C(n₂, t - k) / C(n₁ + n₂, t)`, whatever `p`.

Source: Fisher (1934, §21.02; 1935); Lehmann–Romano (2005), §4.5. -/
theorem cond_measureReal_eq_hypergeometricReal (hp₀ : 0 < p) (hp₁ : p < 1)
    (hXm : Measurable X) (hYm : Measurable Y) (hX : HasLaw X Bin(n₁, p) μ)
    (hY : HasLaw Y Bin(n₂, p) μ) (hXY : IndepFun X Y μ) {t : ℕ} (ht : t ≤ n₁ + n₂) (k : ℕ) :
    (μ[|{ω | X ω + Y ω = t}]).real {ω | X ω = k} = hypergeometricReal (n₁ + n₂) n₁ t k := by
  have hS : MeasurableSet {ω | X ω + Y ω = t} := (hXm.add hYm) (measurableSet_singleton t)
  have hcond : (μ[|{ω | X ω + Y ω = t}]).real {ω | X ω = k} =
      (μ.real {ω | X ω + Y ω = t})⁻¹ * μ.real ({ω | X ω + Y ω = t} ∩ {ω | X ω = k}) := by
    simp only [measureReal_def, cond_apply hS, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hp0 : (0 : ℝ) < p := hp₀
  have hp1 : (p : ℝ) < 1 := hp₁
  have hw : (0 : ℝ) < (p : ℝ) ^ t * (1 - p) ^ (n₁ + n₂ - t) :=
    mul_pos (pow_pos hp0 _) (pow_pos (by linarith) _)
  have hc : (0 : ℝ) < (n₁ + n₂).choose t := by exact_mod_cast Nat.choose_pos ht
  rw [hcond, measureReal_add_eq_binomial hXm hYm hX hY hXY, binomial_real_singleton]
  rcases le_or_gt k t with hk | hk
  · have hset : {ω | X ω + Y ω = t} ∩ {ω | X ω = k} = {ω | X ω = k ∧ Y ω = t - k} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      omega
    rw [hset, measureReal_eq_and_eq hX hY hXY hk, hypergeometricReal, ite_eq_left hk,
      Nat.add_sub_cancel_left]
    field_simp
  · have hset : {ω | X ω + Y ω = t} ∩ {ω | X ω = k} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      omega
    rw [hset, measureReal_empty, mul_zero, hypergeometricReal_of_lt hk]

/-- The margin `X + Y = t` has positive probability under the null, for `0 < p < 1`. -/
private lemma measure_add_eq_ne_zero (hp₀ : 0 < p) (hp₁ : p < 1) (hXm : Measurable X)
    (hYm : Measurable Y) (hX : HasLaw X Bin(n₁, p) μ) (hY : HasLaw Y Bin(n₂, p) μ)
    (hXY : IndepFun X Y μ) {t : ℕ} (ht : t ≤ n₁ + n₂) : μ {ω | X ω + Y ω = t} ≠ 0 := by
  have hp0 : (0 : ℝ) < p := hp₀
  have hp1 : (p : ℝ) < 1 := hp₁
  have hpos : 0 < μ.real {ω | X ω + Y ω = t} := by
    rw [measureReal_add_eq_binomial hXm hYm hX hY hXY, binomial_real_singleton]
    have hc : (0 : ℝ) < (n₁ + n₂).choose t := by exact_mod_cast Nat.choose_pos ht
    exact mul_pos (mul_pos hc (pow_pos hp0 _)) (pow_pos (by linarith) _)
  exact fun h => hpos.ne' (by simp [measureReal_def, h])

/-- **Fisher's conditional law, as a law.** Under the hypotheses of
`cond_measureReal_eq_hypergeometricReal`, given the margin `X + Y = t` the cell `X` has the
hypergeometric law `H(n₁ + n₂, n₁, t)`, whatever `p ∈ (0, 1)`. -/
theorem hasLaw_cond_hypergeometric (hp₀ : 0 < p) (hp₁ : p < 1) (hXm : Measurable X)
    (hYm : Measurable Y) (hX : HasLaw X Bin(n₁, p) μ) (hY : HasLaw Y Bin(n₂, p) μ)
    (hXY : IndepFun X Y μ) {t : ℕ} (ht : t ≤ n₁ + n₂) :
    HasLaw X (hypergeometric (n₁ + n₂) n₁ t (Nat.le_add_right n₁ n₂) ht).toMeasure
      (μ[|{ω | X ω + Y ω = t}]) where
  aemeasurable := hXm.aemeasurable
  map_eq := by
    have := hX.isFiniteMeasure
    have := cond_isProbabilityMeasure (measure_add_eq_ne_zero hp₀ hp₁ hXm hYm hX hY hXY ht)
    refine Measure.ext_of_measureReal_singleton fun k => ?_
    rw [map_measureReal_apply hXm (measurableSet_singleton k)]
    change (μ[|{ω | X ω + Y ω = t}]).real {ω | X ω = k} = _
    rw [cond_measureReal_eq_hypergeometricReal hp₀ hp₁ hXm hYm hX hY hXY ht k, measureReal_def,
      PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k), hypergeometric_apply,
      ENNReal.toReal_ofReal (hypergeometricReal_nonneg _ _ _ _)]

/-- The one-sided (upper) Fisher exact p-value of the cell `X` of a 2×2 table with group sizes
`n₁`, `n₂` and success margin `t`: the hypergeometric `H(n₁ + n₂, n₁, t)` probability of a cell
count at least as large as the observed `X ω`. -/
noncomputable def fisherUpperPValue (n₁ n₂ t : ℕ) (ht : t ≤ n₁ + n₂) (X : Ω → ℕ) : Ω → ℝ :=
  upperTailPValue (hypergeometric (n₁ + n₂) n₁ t (Nat.le_add_right n₁ n₂) ht).toMeasure X

/-- **Validity of the one-sided Fisher exact test.** Let `X ~ Bin(n₁, p)` and `Y ~ Bin(n₂, p)`
be independent with a common `p ∈ (0, 1)`. Conditionally on the margin `X + Y = t`, the upper
Fisher exact p-value is valid: `P(fisherUpperPValue ≤ s | X + Y = t) ≤ s` for `s ∈ [0, 1]`.
The bound holds for every nuisance `p`, because the conditional law of `X` does not depend on
it. This is the one-sided (upper) test only.

Source: Lehmann–Romano (2005), §4.5 and Lemma 3.3.1. -/
theorem isValidPValue_fisherUpper_cond (hp₀ : 0 < p) (hp₁ : p < 1) (hXm : Measurable X)
    (hYm : Measurable Y) (hX : HasLaw X Bin(n₁, p) μ) (hY : HasLaw Y Bin(n₂, p) μ)
    (hXY : IndepFun X Y μ) {t : ℕ} (ht : t ≤ n₁ + n₂) :
    MultipleTesting.IsValidPValue (μ[|{ω | X ω + Y ω = t}]) (fisherUpperPValue n₁ n₂ t ht X) :=
  isValidPValue_upperTailPValue (hasLaw_cond_hypergeometric hp₀ hp₁ hXm hYm hX hY hXY ht)

omit [MeasurableSpace Ω] in
/-- The upper Fisher exact p-value is the finite hypergeometric tail sum
`∑_{X ω ≤ j ≤ t} C(n₁, j) C(n₂, t - j) / C(n₁ + n₂, t)`. -/
theorem fisherUpperPValue_eq_sum {t : ℕ} (ht : t ≤ n₁ + n₂) (X : Ω → ℕ) (ω : Ω) :
    fisherUpperPValue n₁ n₂ t ht X ω =
      ∑ j ∈ Icc (X ω) t, hypergeometricReal (n₁ + n₂) n₁ t j := by
  have hsupp : {j | X ω ≤ j} ∩ (hypergeometric (n₁ + n₂) n₁ t (Nat.le_add_right n₁ n₂) ht).support
      = ↑(Icc (X ω) t) ∩
        (hypergeometric (n₁ + n₂) n₁ t (Nat.le_add_right n₁ n₂) ht).support := by
    ext j
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, coe_Icc, Set.mem_Icc, PMF.mem_support_iff,
      and_congr_left_iff]
    intro hj
    have hjt : j ≤ t := by
      by_contra h
      exact hj (by rw [hypergeometric_apply, hypergeometricReal_of_lt (not_le.1 h),
        ENNReal.ofReal_zero])
    exact ⟨fun h => ⟨h, hjt⟩, And.left⟩
  rw [fisherUpperPValue, upperTailPValue, upperTail, measureReal_def,
    PMF.toMeasure_apply_eq_of_inter_support_eq _ (s := {j | X ω ≤ j}) .of_discrete .of_discrete
      hsupp, PMF.toMeasure_apply_finset, ENNReal.toReal_sum fun j _ => PMF.apply_ne_top _ j]
  refine sum_congr rfl fun j _ => ?_
  rw [hypergeometric_apply, ENNReal.toReal_ofReal (hypergeometricReal_nonneg _ _ _ _)]

end MathlibExt.Probability.Statistics.ExactTests
