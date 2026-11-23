/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic

/-!
# The Bonferroni procedure controls the family-wise error rate

Given `m` p-values, the Bonferroni procedure at level `α` rejects every hypothesis whose
p-value is at most `α / m`. By the union bound, if every true-null p-value is valid
(`μ {p i ≤ t} ≤ t`), the probability of rejecting at least one true null is at most
`α |H0| / m ≤ α`. No assumption is made on the dependence between the p-values or on the
false-null p-values.

## Main results

* `measure_exists_mem_le_le`: the union bound `μ (∃ i ∈ H0, p i ≤ c) ≤ |H0| c`.
* `measure_exists_le_div_le`: `μ (∃ i ∈ H0, p i ≤ α / m) ≤ α |H0| / m`.
* `measure_bonferroni_familywiseError_le`: the Bonferroni procedure has FWER at most `α`.

## References

* C. E. Bonferroni, *Teoria statistica delle classi e calcolo delle probabilità*,
  Pubblicazioni del R. Istituto Superiore di Scienze Economiche e Commerciali di Firenze 8
  (1936), 3–62.
* O. J. Dunn, *Multiple comparisons among means*, J. Amer. Statist. Assoc. 56 (1961), 52–64.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- The hypotheses rejected by the Bonferroni procedure at level `α`: those whose p-value is
at most `α / m`. -/
noncomputable def bonferroniRejections (α : ℝ) (p : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => p i ≤ α / m

/-- **Union bound for valid p-values.** If every true-null p-value is valid and
`c ∈ [0, 1]`, the probability that some true null has p-value at most `c` is at most
`|H0| c`. No independence is assumed. -/
theorem measure_exists_mem_le_le (μ : Measure Ω) (p : Fin m → Ω → ℝ) (H0 : Finset (Fin m))
    (hnull : ∀ i ∈ H0, IsValidPValue μ (p i)) {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    μ {ω | ∃ i ∈ H0, p i ω ≤ c} ≤ ENNReal.ofReal (H0.card * c) := by
  have hset : {ω | ∃ i ∈ H0, p i ω ≤ c} = ⋃ i ∈ H0, {ω | p i ω ≤ c} := by
    ext ω
    simp
  calc μ {ω | ∃ i ∈ H0, p i ω ≤ c}
      ≤ ∑ i ∈ H0, μ {ω | p i ω ≤ c} := hset ▸ measure_biUnion_finset_le H0 _
    _ ≤ ∑ _i ∈ H0, ENNReal.ofReal c := Finset.sum_le_sum fun i hi => hnull i hi c hc
    _ = ENNReal.ofReal (H0.card * c) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]

/-- **Bonferroni inequality.** If every true-null p-value is valid, the probability that some
true null has p-value at most `α / m` is at most `α |H0| / m`, for `α ∈ [0, 1]`. No
independence is assumed. (For `m = 0` there is no hypothesis and both sides are `0`.)

Source: Bonferroni (1936); Dunn (1961). -/
theorem measure_exists_le_div_le (μ : Measure Ω) (p : Fin m → Ω → ℝ) (H0 : Finset (Fin m))
    (hnull : ∀ i ∈ H0, IsValidPValue μ (p i)) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    μ {ω | ∃ i ∈ H0, p i ω ≤ α / m} ≤ ENNReal.ofReal (α * H0.card / m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : H0 = ∅ := Finset.eq_empty_of_isEmpty H0
    simp [this]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hαm : α / m ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hα₀ (by positivity), (div_le_one (by positivity)).2 (hα₁.trans hm')⟩
  refine (measure_exists_mem_le_le μ p H0 hnull hαm).trans_eq ?_
  congr 1
  ring

/-- **The Bonferroni procedure controls the FWER.** If every true-null p-value is valid, the
probability that the Bonferroni procedure at level `α ∈ [0, 1]` rejects at least one true null
is at most `α`. -/
theorem measure_bonferroni_familywiseError_le (μ : Measure Ω) (p : Fin m → Ω → ℝ)
    (H0 : Finset (Fin m)) (hnull : ∀ i ∈ H0, IsValidPValue μ (p i)) {α : ℝ} (hα₀ : 0 ≤ α)
    (hα₁ : α ≤ 1) :
    μ {ω | (bonferroniRejections α (fun i => p i ω) ∩ H0).Nonempty} ≤ ENNReal.ofReal α := by
  have hset : {ω | (bonferroniRejections α (fun i => p i ω) ∩ H0).Nonempty} =
      {ω | ∃ i ∈ H0, p i ω ≤ α / m} := by
    ext ω
    simp [bonferroniRejections, Finset.Nonempty, and_comm]
  rw [hset]
  refine (measure_exists_le_div_le μ p H0 hnull hα₀ hα₁).trans (ENNReal.ofReal_le_ofReal ?_)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hα₀]
  rw [mul_div_assoc]
  refine mul_le_of_le_one_right hα₀ ((div_le_one (by positivity)).2 ?_)
  exact_mod_cast (Finset.card_le_univ H0).trans_eq (Fintype.card_fin m)

end MathlibExt.Probability.Statistics.MultipleTesting
