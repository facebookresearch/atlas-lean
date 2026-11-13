/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Learning.Symmetrization

/-! Tests for the finite-class ghost-sample symmetrization setup. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Statistics.Learning.Symmetrization

/-- Singleton class: the uniform deviation is the single loss's deviation. -/
example {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) {n : ℕ} (f : Fin 1 → Z → ℝ)
    (S : Fin n → Z) :
    supDeviation μ f S = |(n : ℝ)⁻¹ * ∑ i : Fin n, f 0 (S i) - ∫ z, f 0 z ∂μ| := by
  rw [supDeviation, ciSup_unique]
  rfl

/-- Singleton class: the ghost deviation is the single loss's two-sample gap. -/
example {Z : Type*} {n : ℕ} (f : Fin 1 → Z → ℝ) (S S' : Fin n → Z) :
    ghostSupDeviation f S S' =
      |(n : ℝ)⁻¹ * ∑ i : Fin n, f 0 (S i) - (n : ℝ)⁻¹ * ∑ i : Fin n, f 0 (S' i)| := by
  rw [ghostSupDeviation, ciSup_unique]
  rfl

/-- Empty class: the uniform deviation is `0`. -/
example {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) {n : ℕ} (f : Fin 0 → Z → ℝ)
    (S : Fin n → Z) :
    supDeviation μ f S = 0 := by
  rw [supDeviation]
  exact Real.iSup_of_isEmpty _

/-- Constant loss, `n > 0`: no deviation. -/
example {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ] {M n : ℕ}
    (hn : 0 < n) (c : ℝ) (S : Fin n → Z) :
    supDeviation μ (fun (_ : Fin M) (_ : Z) => c) S = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  simp [supDeviation, Finset.sum_const, Finset.card_univ, hn']

/-- Boundary `n = 0`: the empty sample has empirical mean `0`, so the constant loss `1` has
deviation `1`; the previous test needs `0 < n`. -/
example {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (S : Fin 0 → Z) :
    supDeviation μ (fun (_ : Fin 1) (_ : Z) => (1 : ℝ)) S = 1 := by
  simp [supDeviation]

/-- Constant loss: the ghost deviation vanishes for every sample size. -/
example {Z : Type*} {M n : ℕ} (c : ℝ) (S S' : Fin n → Z) :
    ghostSupDeviation (fun (_ : Fin M) (_ : Z) => c) S S' = 0 := by
  simp [ghostSupDeviation]

/-- Two hypotheses: the supremum picks the separating loss, not the first one. -/
example :
    ghostSupDeviation (fun (j : Fin 2) (z : Bool) => if j = 1 ∧ z = true then (1 : ℝ) else 0)
      ![true] ![false] = 1 := by
  apply le_antisymm
  · rw [ghostSupDeviation]
    refine Real.iSup_le ?_ zero_le_one
    intro j
    fin_cases j <;> simp
  · have h1 := abs_sub_le_ghostSupDeviation
      (fun (j : Fin 2) (z : Bool) => if j = 1 ∧ z = true then (1 : ℝ) else 0)
      ![true] ![false] (1 : Fin 2)
    simp at h1
    exact h1

/-- Constant classifier `true`: the error indicator is the indicator of the label `false`. -/
example {α : Type*} (a : α) :
    binaryErrorIndicator (fun (_ : Fin 1) (_ : α) => true) 0 (a, false) = 1 ∧
      binaryErrorIndicator (fun (_ : Fin 1) (_ : α) => true) 0 (a, true) = 0 := by
  simp [binaryErrorIndicator]

/-- The error indicator has the loss shape assumed by the agnostic finite-class bound. -/
example {α : Type*} {M : ℕ} (h : Fin M → α → Bool) :
    ∀ j p, binaryErrorIndicator h j p = if h j p.1 ≠ p.2 then (1 : ℝ) else (0 : ℝ) := by
  intro j p
  rfl

/-- Ghost marginal: an event of the ghost sample has the sample-law probability. -/
example {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    {A : Set (Fin n → Z)} (hA : MeasurableSet A) :
    ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)).real
        {p | p.2 ∈ A} =
      (Measure.pi fun _ : Fin n => μ).real A := by
  unfold Measure.real
  have hset : {p : (Fin n → Z) × (Fin n → Z) | p.2 ∈ A} = Prod.snd ⁻¹' A := rfl
  rw [hset, ← Measure.map_apply measurable_snd hA, ghostSample_map_snd]

end MathlibExtTest.Probability.Statistics.Learning.Symmetrization
