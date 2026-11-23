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

/-- Singleton class: the inequality for one loss, with both suprema collapsed. -/
theorem symmetrization_singleton {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {n : ℕ} (g : Z → ℝ) (hg : Measurable g)
    (hbd : ∀ᵐ z ∂μ, g z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε)
    (hnε : 2 ≤ (n : ℝ) * ε ^ 2) :
    (Measure.pi fun _ : Fin n => μ).real
        {S | ε < |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - ∫ z, g z ∂μ|} ≤
      2 * ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)).real
        {p | ε / 2 <
          |(n : ℝ)⁻¹ * ∑ i : Fin n, g (p.1 i) - (n : ℝ)⁻¹ * ∑ i : Fin n, g (p.2 i)|} := by
  have h := measureReal_supDeviation_gt_le_two_mul_ghost μ (fun (_ : Fin 1) => g)
    (fun _ => hg) (fun _ => hbd) hε hnε
  unfold supDeviation ghostSupDeviation at h
  simpa only [ciSup_unique] using h

/-- Binary class: the inequality for the error indicators of a finite binary class. -/
theorem symmetrization_binaryClass {α : Type*} [MeasurableSpace α] (μ : Measure (α × Bool))
    [IsProbabilityMeasure μ] {M n : ℕ} (h : Fin M → α → Bool)
    (herr : ∀ j, MeasurableSet {p : α × Bool | h j p.1 ≠ p.2}) {ε : ℝ} (hε : 0 < ε)
    (hnε : 2 ≤ (n : ℝ) * ε ^ 2) :
    (Measure.pi fun _ : Fin n => μ).real {S | ε < supDeviation μ (binaryErrorIndicator h) S} ≤
      2 * ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)).real
        {p | ε / 2 < ghostSupDeviation (binaryErrorIndicator h) p.1 p.2} := by
  exact measureReal_supDeviation_gt_le_two_mul_ghost μ (binaryErrorIndicator h)
    (fun j => measurable_binaryErrorIndicator h j (herr j))
    (fun j => Filter.Eventually.of_forall fun p => binaryErrorIndicator_mem_Icc h j p)
    hε hnε

/-- Threshold class with two hypotheses on `ℝ`: losses `1{z ≤ t j}`, `j : Fin 2`. -/
theorem symmetrization_thresholdClass (μ : Measure ℝ) [IsProbabilityMeasure μ] {n : ℕ}
    (t : Fin 2 → ℝ) {ε : ℝ} (hε : 0 < ε) (hnε : 2 ≤ (n : ℝ) * ε ^ 2) :
    (Measure.pi fun _ : Fin n => μ).real
        {S | ε < supDeviation μ (fun j => (Set.Iic (t j)).indicator 1) S} ≤
      2 * ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)).real
        {p | ε / 2 < ghostSupDeviation (fun j => (Set.Iic (t j)).indicator 1) p.1 p.2} := by
  refine measureReal_supDeviation_gt_le_two_mul_ghost μ _ ?_ ?_ hε hnε
  · intro j
    exact measurable_const.indicator measurableSet_Iic
  · intro j
    filter_upwards with z
    by_cases hz : z ∈ Set.Iic (t j)
    · rw [Set.indicator_of_mem hz]
      exact ⟨zero_le_one, le_rfl⟩
    · rw [Set.indicator_of_notMem hz]
      exact ⟨le_rfl, zero_le_one⟩

/-- Empty class: both sides vanish. -/
theorem symmetrization_emptyClass {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {n : ℕ} (f : Fin 0 → Z → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi fun _ : Fin n => μ).real {S | ε < supDeviation μ f S} = 0 ∧
      ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)).real
        {p | ε / 2 < ghostSupDeviation f p.1 p.2} = 0 := by
  have hB : {S : Fin n → Z | ε < supDeviation μ f S} = ∅ := by
    ext S
    simp [lt_supDeviation_iff μ f S hε.le]
  have hG : {p : (Fin n → Z) × (Fin n → Z) | ε / 2 < ghostSupDeviation f p.1 p.2} = ∅ := by
    ext p
    simp [lt_ghostSupDeviation_iff f p.1 p.2 (half_pos hε).le]
  rw [hB, hG]
  simp

/-- Dependent ghost (negative): with the ghost sample equal to the sample, the ghost event has
probability `0`, so the inequality fails for a dependent ghost whenever its left side is positive;
the product law is necessary. -/
theorem symmetrization_diagonalGhost_eq_zero {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {M n : ℕ} (f : Fin M → Z → ℝ) (hf : ∀ j, Measurable (f j))
    {ε : ℝ} (hε : 0 ≤ ε) :
    ((Measure.pi fun _ : Fin n => μ).map fun S => (S, S)).real
        {p | ε / 2 < ghostSupDeviation f p.1 p.2} = 0 := by
  have hdiag : Measurable fun S : Fin n → Z => (S, S) :=
    measurable_id.prodMk measurable_id
  rw [measureReal_def, Measure.map_apply hdiag (measurableSet_lt_ghostSupDeviation f hf _)]
  have hpre : (fun S : Fin n → Z => (S, S)) ⁻¹' {p | ε / 2 < ghostSupDeviation f p.1 p.2} = ∅ := by
    ext S
    simp [ghostSupDeviation_self, not_lt.mpr (div_nonneg hε zero_le_two)]
  rw [hpre]
  simp

end MathlibExtTest.Probability.Statistics.Learning.Symmetrization
