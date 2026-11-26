/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Consistency of the Li–Mantel estimator for the segregation ratio

Sibships of size `s` are ascertained through at least one affected child (complete
ascertainment), and each child is affected independently with probability `p` (the segregation
ratio). The number of affected children in an ascertained sibship then follows the zero-truncated
binomial law `truncBinom`. From the affected counts `x` of the first `n` sibships, `affectedCount`
counts affected children, `singletonCount` counts sibships with exactly one affected child, and
`liMantel` is the estimator `(R - J) / (T - J)`. This file proves its almost-sure consistency
(`liMantel_tendsto_ae`): for independent ascertained sibships of a common size `s ≥ 2` with
segregation ratio `0 < p < 1`, the estimator computed from the first `n` sibships converges
almost surely to `p`, by applying the strong law of large numbers to the affected counts and the
singleton indicators.

Sources: C. C. Li and N. Mantel, "A simple method of estimating the segregation ratio under
complete ascertainment", Am. J. Hum. Genet. 20 (1968) 61–81; R. A. Fisher, "The effect of
methods of ascertainment upon the estimation of frequencies", Ann. Eugen. 6 (1934) 13–25.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.LiMantelSegregationWanted

open MeasureTheory ProbabilityTheory Filter Topology Finset Function

/-- The **zero-truncated binomial law**: the probability that an ascertained sibship of size `s`
has exactly `k` affected children, when each child is affected independently with probability
`p` and the sibship is ascertained if and only if `k ≥ 1`. It vanishes for `k = 0` and `k > s`.
For `1 ≤ k ≤ s` it is `C(s, k) p^k (1 - p)^(s - k) / (1 - (1 - p)^s)`. The intended domain is
`s ≥ 1` and `0 < p < 1`, where the denominator `1 - (1 - p)^s` is positive. Outside it the
denominator can vanish (e.g. `p = 0`), and then the value is `0`, since Lean's division is total
(`x / 0 = 0`). -/
noncomputable def truncBinom (s : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  if 1 ≤ k ∧ k ≤ s then
    (s.choose k : ℝ) * p ^ k * (1 - p) ^ (s - k) / (1 - (1 - p) ^ s)
  else 0

/-- Number `R` of affected children in the first `n` sibships, given the affected counts `x`. -/
def affectedCount (x : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, x i

/-- Number `J` of sibships with exactly one affected child among the first `n`. -/
def singletonCount (x : ℕ → ℕ) (n : ℕ) : ℕ := #{i ∈ range n | x i = 1}

/-- The **Li–Mantel estimator** `(R - J) / (T - J)` of the segregation ratio from the first `n`
ascertained sibships of size `s`, where `T = n s` is the number of children. Since `J ≤ n`, the
denominator satisfies `T - J ≥ n (s - 1) > 0` whenever `n ≥ 1` and `s ≥ 2`, the intended domain.
Otherwise it can vanish (for `n = 0`, or for `s = 1`, where every sibship is a singleton), and
then the value is `0` because Lean's division is total (`x / 0 = 0`). -/
noncomputable def liMantel (s : ℕ) (x : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((affectedCount x n : ℝ) - singletonCount x n) / ((n * s : ℕ) - (singletonCount x n : ℝ))

private def indOne : ℕ → ℝ := fun k => if k = 1 then 1 else 0

private theorem denom_pos (s : ℕ) (hs : 1 ≤ s) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    0 < 1 - (1 - p) ^ s := by
  have hq : (1 - p) ^ s < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  linarith

private theorem binom_mean (s : ℕ) (hs : 1 ≤ s) (p : ℝ) :
    ∑ k ∈ range (s + 1), (k : ℝ) * ((s.choose k : ℝ) * p ^ k * (1 - p) ^ (s - k)) =
      s * p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show s ≠ 0 by omega)
  simp only [Nat.succ_eq_add_one]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have hexp : ∀ k : ℕ, m + 1 - (k + 1) = m - k := fun k => by omega
  have hcast : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * (((m + 1).choose (k + 1) : ℕ) : ℝ) =
      ((m + 1 : ℕ) : ℝ) * ((m.choose k : ℕ) : ℝ) := by
    intro k
    have h := Nat.add_one_mul_choose_eq m k
    have h' : ((m + 1 : ℕ) : ℝ) * ((m.choose k : ℕ) : ℝ) =
        (((m + 1).choose (k + 1) : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by exact_mod_cast h
    exact Eq.trans (mul_comm _ _) h'.symm
  have hadd : ∑ k ∈ range (m + 1), ((m.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (m - k) =
      1 := by
    have h1 : p + (1 - p) = (1 : ℝ) := by ring
    have h := add_pow p (1 - p) m
    rw [h1, one_pow] at h
    calc ∑ k ∈ range (m + 1), ((m.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (m - k)
        = ∑ j ∈ range (m + 1), p ^ j * (1 - p) ^ (m - j) * ((m.choose j : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 1 := h.symm
  calc ∑ k ∈ range (m + 1), ((k + 1 : ℕ) : ℝ) *
        ((((m + 1).choose (k + 1) : ℕ) : ℝ) * p ^ (k + 1) * (1 - p) ^ (m + 1 - (k + 1)))
      = ∑ k ∈ range (m + 1), ((m + 1 : ℕ) : ℝ) * p *
        (((m.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (m - k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hfac : ((k + 1 : ℕ) : ℝ) *
            ((((m + 1).choose (k + 1) : ℕ) : ℝ) * (p ^ k * p) * (1 - p) ^ (m - k)) =
            (p ^ k * p * (1 - p) ^ (m - k)) * (((k + 1 : ℕ) : ℝ) *
              (((m + 1).choose (k + 1) : ℕ) : ℝ)) := by ring
        rw [hexp k, pow_succ, hfac, hcast k]
        ring
    _ = ((m + 1 : ℕ) : ℝ) * p * ∑ k ∈ range (m + 1),
        (((m.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (m - k)) := by rw [← Finset.mul_sum]
    _ = ((m + 1 : ℕ) : ℝ) * p := by rw [hadd, mul_one]

private theorem truncBinom_mean (s : ℕ) (hs : 1 ≤ s) (p : ℝ) :
    ∑ k ∈ range (s + 1), (k : ℝ) * truncBinom s p k = s * p / (1 - (1 - p) ^ s) := by
  have hterm : ∀ k ∈ range (s + 1),
      (k : ℝ) * truncBinom s p k =
        ((k : ℝ) * ((s.choose k : ℝ) * p ^ k * (1 - p) ^ (s - k))) /
          (1 - (1 - p) ^ s) := by
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases h1 : 1 ≤ k
    · have hcond : 1 ≤ k ∧ k ≤ s := ⟨h1, by omega⟩
      simp only [truncBinom]
      rw [ite_eq_left hcond]
      ring
    · have hk0 : k = 0 := by omega
      simp [hk0]
  calc ∑ k ∈ range (s + 1), (k : ℝ) * truncBinom s p k
      = ∑ k ∈ range (s + 1), ((k : ℝ) * ((s.choose k : ℝ) * p ^ k * (1 - p) ^ (s - k))) /
        (1 - (1 - p) ^ s) := Finset.sum_congr rfl hterm
    _ = (∑ k ∈ range (s + 1), (k : ℝ) * ((s.choose k : ℝ) * p ^ k * (1 - p) ^ (s - k))) /
        (1 - (1 - p) ^ s) := (Finset.sum_div _ _ _).symm
    _ = s * p / (1 - (1 - p) ^ s) := by rw [binom_mean s hs p]

private theorem truncBinom_one (s : ℕ) (hs : 2 ≤ s) (p : ℝ) :
    truncBinom s p 1 = s * p * (1 - p) ^ (s - 1) / (1 - (1 - p) ^ s) := by
  have hcond : 1 ≤ 1 ∧ 1 ≤ s := ⟨le_rfl, by omega⟩
  simp only [truncBinom]
  rw [ite_eq_left hcond]
  simp [Nat.choose_one_right, pow_one]

private theorem ae_le_of_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : ℕ) (p : ℝ) (X : ℕ → Ω → ℕ)
    (hlaw : ∀ i k, μ.real (X i ⁻¹' {k}) = truncBinom s p k) (i : ℕ) :
    ∀ᵐ ω ∂μ, X i ω ≤ s := by
  have hnull : ∀ k : ℕ, s < k → μ (X i ⁻¹' {k}) = 0 := by
    intro k hk
    have htk : truncBinom s p k = 0 := by
      simp only [truncBinom]
      rw [ite_eq_right (by omega)]
    have h := hlaw i k
    rw [htk] at h
    exact (measureReal_eq_zero_iff (measure_lt_top μ _).ne).mp h
  have hset : {ω : Ω | s < X i ω} = ⋃ k ∈ {k : ℕ | s < k}, X i ⁻¹' {k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨X i ω, h, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact hk
  have hμ : μ {ω : Ω | s < X i ω} = 0 := by
    rw [hset, measure_biUnion_null_iff (Set.to_countable _)]
    intro k hk
    exact hnull k hk
  have hcompl : {ω : Ω | X i ω ≤ s}ᶜ = {ω : Ω | s < X i ω} := by
    ext ω
    simp
  have hmem : {ω : Ω | X i ω ≤ s} ∈ ae μ := by
    rw [mem_ae_iff, hcompl]
    exact hμ
  exact hmem

private theorem identDistrib_of_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : ℕ) (p : ℝ) (X : ℕ → Ω → ℕ)
    (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i k, μ.real (X i ⁻¹' {k}) = truncBinom s p k) (i : ℕ) :
    IdentDistrib (X i) (X 0) μ μ := by
  refine ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (hmeas i) (measurableSet_singleton k),
    Measure.map_apply (hmeas 0) (measurableSet_singleton k)]
  have hfin1 : μ (X i ⁻¹' {k}) ≠ ⊤ := (measure_lt_top μ _).ne
  have hfin0 : μ (X 0 ⁻¹' {k}) ≠ ⊤ := (measure_lt_top μ _).ne
  have e1 : μ (X i ⁻¹' {k}) = ENNReal.ofReal (truncBinom s p k) := by
    rw [← hlaw i k, ofReal_measureReal hfin1]
  have e0 : μ (X 0 ⁻¹' {k}) = ENNReal.ofReal (truncBinom s p k) := by
    rw [← hlaw 0 k, ofReal_measureReal hfin0]
  rw [e1, e0]

private theorem integral_cast_of_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : ℕ) (hs : 2 ≤ s) (p : ℝ) (X : ℕ → Ω → ℕ)
    (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i k, μ.real (X i ⁻¹' {k}) = truncBinom s p k) :
    μ[(fun k : ℕ => (k : ℝ)) ∘ X 0] = s * p / (1 - (1 - p) ^ s) := by
  have hae : ∀ᵐ ω ∂μ, X 0 ω ≤ s := ae_le_of_law μ s p X hlaw 0
  have hrep : (fun k : ℕ => (k : ℝ)) ∘ X 0 =ᵐ[μ] fun ω =>
      ∑ k ∈ range (s + 1), (X 0 ⁻¹' {k}).indicator (fun _ => (k : ℝ)) ω := by
    filter_upwards [hae] with ω hω
    simp only [Function.comp_apply]
    have hmem : X 0 ω ∈ range (s + 1) := Finset.mem_range.mpr (by omega)
    have hmain : (X 0 ⁻¹' {X 0 ω}).indicator (fun _ => ((X 0 ω : ℕ) : ℝ)) ω =
        ((X 0 ω : ℕ) : ℝ) := Set.indicator_of_mem (by simp) _
    have hsingle : ∀ b ∈ range (s + 1), b ≠ X 0 ω →
        (X 0 ⁻¹' {b}).indicator (fun _ => (b : ℝ)) ω = 0 := by
      intro k _ hkne
      have hnin : ω ∉ X 0 ⁻¹' {k} := by simpa using hkne.symm
      exact Set.indicator_of_notMem hnin _
    rw [← hmain]
    exact (Finset.sum_eq_single_of_mem (X 0 ω) hmem hsingle).symm
  have hint : ∀ k ∈ range (s + 1),
      Integrable (fun ω => (X 0 ⁻¹' {k}).indicator (fun _ => (k : ℝ)) ω) μ := by
    intro k _
    exact Integrable.indicator (integrable_const _) (hmeas 0 (measurableSet_singleton k))
  calc μ[(fun k : ℕ => (k : ℝ)) ∘ X 0]
      = ∫ ω, ∑ k ∈ range (s + 1), (X 0 ⁻¹' {k}).indicator (fun _ => (k : ℝ)) ω ∂μ :=
        integral_congr_ae hrep
    _ = ∑ k ∈ range (s + 1), ∫ ω, (X 0 ⁻¹' {k}).indicator (fun _ => (k : ℝ)) ω ∂μ :=
        integral_finsetSum _ hint
    _ = ∑ k ∈ range (s + 1), (k : ℝ) * μ.real (X 0 ⁻¹' {k}) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_indicator_const _ (hmeas 0 (measurableSet_singleton k)), smul_eq_mul]
        exact mul_comm _ _
    _ = ∑ k ∈ range (s + 1), (k : ℝ) * truncBinom s p k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hlaw]
    _ = s * p / (1 - (1 - p) ^ s) := truncBinom_mean s (by omega) p

private theorem integral_indOne_of_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : ℕ) (p : ℝ) (X : ℕ → Ω → ℕ)
    (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i k, μ.real (X i ⁻¹' {k}) = truncBinom s p k) :
    μ[indOne ∘ X 0] = truncBinom s p 1 := by
  have heq : indOne ∘ X 0 = (X 0 ⁻¹' {1}).indicator 1 := by
    ext ω
    simp only [Function.comp_apply, indOne]
    by_cases h : X 0 ω = 1
    · have hm : ω ∈ X 0 ⁻¹' {1} := by simpa using h
      rw [Set.indicator_of_mem hm]
      simp [h]
    · have hm : ω ∉ X 0 ⁻¹' {1} := by simpa using h
      rw [Set.indicator_of_notMem hm]
      simp [h]
  calc μ[indOne ∘ X 0] = μ[(X 0 ⁻¹' {1}).indicator 1] := by rw [heq]
    _ = truncBinom s p 1 := by
      have h1 : ∫ ω, (X 0 ⁻¹' {1}).indicator 1 ω ∂μ = μ.real (X 0 ⁻¹' {1}) :=
        integral_indicator_one (hmeas 0 (measurableSet_singleton 1))
      rw [hlaw] at h1
      exact h1

private theorem sum_cast_eq_affectedCount (x : ℕ → ℕ) (n : ℕ) :
    (∑ i ∈ range n, ((x i : ℕ) : ℝ)) = ((affectedCount x n : ℕ) : ℝ) := by
  simp only [affectedCount, Nat.cast_sum]

private theorem sum_indOne_eq_singletonCount (x : ℕ → ℕ) (n : ℕ) :
    (∑ i ∈ range n, indOne (x i)) = ((singletonCount x n : ℕ) : ℝ) := by
  simp only [singletonCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [indOne]
  by_cases h : x i = 1 <;> simp [h]

private theorem sub_truncBinom_one_pos (s : ℕ) (hs : 2 ≤ s) (p : ℝ) (hp₀ : 0 < p)
    (hp₁ : p < 1) : 0 < (s : ℝ) - truncBinom s p 1 := by
  have hD : 0 < 1 - (1 - p) ^ s := denom_pos s (by omega) p hp₀ hp₁
  rw [truncBinom_one s hs p]
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hq1 : (1 - p) ^ (s - 1) < 1 :=
    pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have hqs : (1 - p) ^ s = (1 - p) ^ (s - 1) * (1 - p) := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ s by omega)]
    rw [pow_succ]
  have hpos : 0 < (s : ℝ) * (1 - (1 - p) ^ s) - s * p * (1 - p) ^ (s - 1) := by
    have heq : (s : ℝ) * (1 - (1 - p) ^ s) - s * p * (1 - p) ^ (s - 1) =
        s * (1 - (1 - p) ^ (s - 1)) := by
      rw [hqs]
      ring
    rw [heq]
    exact mul_pos hs0 (by linarith)
  rw [sub_pos, div_lt_iff₀ hD]
  linarith [hpos]

private theorem liMantel_limit_value (s : ℕ) (hs : 2 ≤ s) (p : ℝ) (hp₀ : 0 < p)
    (hp₁ : p < 1) :
    (s * p / (1 - (1 - p) ^ s) - truncBinom s p 1) / ((s : ℝ) - truncBinom s p 1) =
      p := by
  have hD : 0 < 1 - (1 - p) ^ s := denom_pos s (by omega) p hp₀ hp₁
  have hDne : (1 : ℝ) - (1 - p) ^ s ≠ 0 := ne_of_gt hD
  have hden : 0 < (s : ℝ) - truncBinom s p 1 := sub_truncBinom_one_pos s hs p hp₀ hp₁
  rw [truncBinom_one s hs p] at hden ⊢
  rw [div_eq_iff (ne_of_gt hden)]
  have hqs : (1 - p) ^ s = (1 - p) ^ (s - 1) * (1 - p) := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ s by omega)]
    rw [pow_succ]
  have hmul : ((s : ℝ) - s * p * (1 - p) ^ (s - 1) / (1 - (1 - p) ^ s)) *
      (1 - (1 - p) ^ s) =
      (s : ℝ) * (1 - (1 - p) ^ s) - s * p * (1 - p) ^ (s - 1) := by
    rw [sub_mul, div_mul_cancel₀ _ hDne]
  rw [← sub_div, div_eq_iff hDne, mul_assoc p _ _, hmul, hqs]
  ring

/-- **Consistency of the Li–Mantel estimator** (Li and Mantel 1968): let the affected counts
`X i` of ascertained sibships of a common size `s ≥ 2` be independent random variables, each with
the zero-truncated binomial law for a segregation ratio `0 < p < 1`. Then, almost surely, the
estimator `(R - J) / (T - J)` computed from the first `n` sibships converges to `p` as
`n → ∞`.

Source: Li and Mantel (1968). -/
public theorem liMantel_tendsto_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : ℕ) (hs : 2 ≤ s) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (X : ℕ → Ω → ℕ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hlaw : ∀ i k, μ.real (X i ⁻¹' {k}) = truncBinom s p k) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => liMantel s (fun i => X i ω) n) atTop (𝓝 p) := by
  have hφ : Measurable (fun k : ℕ => (k : ℝ)) := measurable_of_countable _
  have hψ : Measurable indOne := measurable_of_countable _
  have hYint : Integrable ((fun k : ℕ => (k : ℝ)) ∘ X 0) μ := by
    refine Integrable.of_bound ((hφ.comp (hmeas 0)).aestronglyMeasurable) (s : ℝ) ?_
    filter_upwards [ae_le_of_law μ s p X hlaw 0] with ω hω
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hω
  have hZint : Integrable (indOne ∘ X 0) μ := by
    refine Integrable.of_bound ((hψ.comp (hmeas 0)).aestronglyMeasurable) (1 : ℝ) ?_
    refine Eventually.of_forall fun ω => ?_
    simp only [Function.comp_apply, indOne]
    by_cases h : X 0 ω = 1 <;> simp [h]
  have hYindep : Pairwise ((· ⟂ᵢ[μ] ·) on fun i => (fun k : ℕ => (k : ℝ)) ∘ X i) :=
    fun i j hij => (hindep.indepFun hij).comp hφ hφ
  have hZindep : Pairwise ((· ⟂ᵢ[μ] ·) on fun i => indOne ∘ X i) :=
    fun i j hij => (hindep.indepFun hij).comp hψ hψ
  have hYident : ∀ i, IdentDistrib ((fun k : ℕ => (k : ℝ)) ∘ X i)
      ((fun k : ℕ => (k : ℝ)) ∘ X 0) μ μ :=
    fun i => (identDistrib_of_law μ s p X hmeas hlaw i).comp hφ
  have hZident : ∀ i, IdentDistrib (indOne ∘ X i) (indOne ∘ X 0) μ μ :=
    fun i => (identDistrib_of_law μ s p X hmeas hlaw i).comp hψ
  have hY := strong_law_ae_real (fun i => (fun k : ℕ => (k : ℝ)) ∘ X i) hYint hYindep hYident
  have hZ := strong_law_ae_real (fun i => indOne ∘ X i) hZint hZindep hZident
  have hμY : ∫ x, ((X 0 x : ℕ) : ℝ) ∂μ = s * p / (1 - (1 - p) ^ s) :=
    integral_cast_of_law μ s hs p X hmeas hlaw
  have hμZ : ∫ x, indOne (X 0 x) ∂μ = truncBinom s p 1 :=
    integral_indOne_of_law μ s p X hmeas hlaw
  have hden : 0 < (s : ℝ) - truncBinom s p 1 := sub_truncBinom_one_pos s hs p hp₀ hp₁
  filter_upwards [hY, hZ] with ω hYω hZω
  simp only [Function.comp_apply] at hYω hZω
  rw [hμY] at hYω
  rw [hμZ] at hZω
  have hlim : Tendsto (fun n : ℕ => (((∑ i ∈ range n, ((X i ω : ℕ) : ℝ)) / n) -
      ((∑ i ∈ range n, indOne (X i ω)) / n)) /
      ((s : ℝ) - ((∑ i ∈ range n, indOne (X i ω)) / n))) atTop
      (𝓝 (((s * p / (1 - (1 - p) ^ s)) - truncBinom s p 1) /
        ((s : ℝ) - truncBinom s p 1))) :=
    (hYω.sub hZω).div (tendsto_const_nhds.sub hZω) (ne_of_gt hden)
  rw [liMantel_limit_value s hs p hp₀ hp₁] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [liMantel, sum_cast_eq_affectedCount, sum_indOne_eq_singletonCount]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hT : ((n * s : ℕ) : ℝ) = (n : ℝ) * s := Nat.cast_mul _ _
  have e1 : (((affectedCount (fun i => X i ω) n : ℕ) : ℝ) / n) -
      (((singletonCount (fun i => X i ω) n : ℕ) : ℝ) / n) =
      (((affectedCount (fun i => X i ω) n : ℕ) : ℝ) -
        ((singletonCount (fun i => X i ω) n : ℕ) : ℝ)) / n := (sub_div _ _ _).symm
  have e2 : (s : ℝ) - (((singletonCount (fun i => X i ω) n : ℕ) : ℝ) / n) =
      ((((n * s : ℕ) : ℝ) - ((singletonCount (fun i => X i ω) n : ℕ) : ℝ))) / n := by
    rw [hT, eq_div_iff hn0, sub_mul, div_mul_cancel₀ _ hn0]
    ring
  rw [e1, e2, div_div_div_cancel_right₀ hn0]

end WantedExt.Biology.StatisticalGenetics.LiMantelSegregationWanted
