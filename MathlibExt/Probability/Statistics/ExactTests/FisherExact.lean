/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Hypergeometric
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

end MathlibExt.Probability.Statistics.ExactTests
