/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Finite-class ghost-sample setup (frozen definitions for the symmetrization lemma)

Coordinator freeze (L5-15 gate, discharged as this definitions file). Conventions are those of
`MathlibExt.Probability.Statistics.Learning.FiniteRisk`: hypothesis index `Fin M`, losses
`f : Fin M → Z → ℝ` with `∀ j, Measurable (f j)` and `∀ j, ∀ᵐ z ∂μ, f j z ∈ Set.Icc 0 1`,
empirical mean `(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i)`, population mean `∫ z, f j z ∂μ`, sample law
`Measure.pi fun _ : Fin n => μ`, probabilities as `Measure.real`.

* The supremum over the finite class is the indexed `⨆ j : Fin M` in `ℝ` (the dual of the
  `⨅ j` used by `erm_populationRisk_le_best_plus_two`). For a nonempty class (`0 < M`) every
  such supremum is attained by some index. For the empty class (`M = 0`) both deviations are `0`,
  the value `ℝ` assigns to an empty indexed supremum; no index attains it. In both cases every
  event below is measurable and probabilities are ordinary (not outer).
* The ghost sample is an independent copy with the same law: the pair `(S, S')` has law
  `(Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)`.
* A binary class `h : Fin M → α → Bool` enters through `binaryErrorIndicator h`, the `{0, 1}`
  loss on labeled points `α × Bool`; its measurability regime is
  `∀ j, MeasurableSet {p : α × Bool | h j p.1 ≠ p.2}`, as in the agnostic finite-class bound.

Reserved for the follow-up slice (stated here as the freeze, not proved in this file): the
standard symmetrization lemma (Devroye, Györfi and Lugosi, *A Probabilistic Theory of Pattern
Recognition*, Lemma 12.1), for `0 < ε` and `2 ≤ n * ε ^ 2`,
`P {S | ε < supDeviation μ f S} ≤ 2 * (P ⊗ P) {(S, S') | ε / 2 < ghostSupDeviation f S S'}`
with `P = Measure.pi fun _ : Fin n => μ`, strict thresholds `ε` and `ε / 2`, constant `2`, and
the L5-06 hypotheses on `f` unchanged.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- Uniform deviation over the finite class: the largest absolute gap between the empirical mean
on `S` and the population mean under `μ`. -/
noncomputable def supDeviation {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) {M n : ℕ}
    (f : Fin M → Z → ℝ) (S : Fin n → Z) : ℝ :=
  ⨆ j : Fin M, |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - ∫ z, f j z ∂μ|

/-- Ghost-sample deviation over the finite class: the largest absolute gap between the empirical
means on the sample `S` and on the ghost sample `S'`. -/
noncomputable def ghostSupDeviation {Z : Type*} {M n : ℕ} (f : Fin M → Z → ℝ)
    (S S' : Fin n → Z) : ℝ :=
  ⨆ j : Fin M, |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - (n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i)|

/-- Error indicator of a finite binary class on a labeled point: `1` on a misclassification,
`0` otherwise. -/
noncomputable def binaryErrorIndicator {α : Type*} {M : ℕ} (h : Fin M → α → Bool) (j : Fin M)
    (p : α × Bool) : ℝ :=
  if h j p.1 ≠ p.2 then 1 else 0

theorem abs_deviation_le_supDeviation {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    {M n : ℕ} (f : Fin M → Z → ℝ) (S : Fin n → Z) (j : Fin M) :
    |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - ∫ z, f j z ∂μ| ≤ supDeviation μ f S := by
  unfold supDeviation
  exact le_ciSup (f := fun j : Fin M => |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - ∫ z, f j z ∂μ|)
      (Finite.bddAbove_range _) j

theorem supDeviation_nonneg {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    {M n : ℕ} (f : Fin M → Z → ℝ) (S : Fin n → Z) :
    0 ≤ supDeviation μ f S := by
  unfold supDeviation
  exact Real.iSup_nonneg fun _ => abs_nonneg _

theorem supDeviation_le_iff {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    {M n : ℕ} (f : Fin M → Z → ℝ) (S : Fin n → Z) {c : ℝ} (hc : 0 ≤ c) :
    supDeviation μ f S ≤ c ↔
      ∀ j : Fin M, |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - ∫ z, f j z ∂μ| ≤ c := by
  constructor
  · intro h j
    exact (abs_deviation_le_supDeviation μ f S j).trans h
  · intro h
    unfold supDeviation
    exact Real.iSup_le h hc

theorem lt_supDeviation_iff {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    {M n : ℕ} (f : Fin M → Z → ℝ) (S : Fin n → Z) {c : ℝ} (hc : 0 ≤ c) :
    c < supDeviation μ f S ↔
      ∃ j : Fin M, c < |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - ∫ z, f j z ∂μ| := by
  rcases isEmpty_or_nonempty (Fin M) with hM | hM
  · rw [show supDeviation μ f S = 0 from @Real.iSup_of_isEmpty _ hM _]
    rw [@IsEmpty.exists_iff _ hM (fun j : Fin M => c < |(n : ℝ)⁻¹ * ∑ i : Fin n, f j
        (S i) - ∫ z, f j z ∂μ|)]
    rw [iff_false, not_lt]
    exact hc
  · exact @lt_ciSup_iff _ _ _ _ hM (fun j : Fin M => |(n : ℝ)⁻¹ * ∑ i : Fin n, f j
      (S i) - ∫ z, f j z ∂μ|) (Finite.bddAbove_range _)

/-- The strict uniform-deviation event lies inside the bad set of
`measure_exists_abs_empirical_sub_integral_ge_le`. -/
theorem setOf_lt_supDeviation_subset {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    {M n : ℕ} (f : Fin M → Z → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    {S : Fin n → Z | ε < supDeviation μ f S} ⊆
      {S : Fin n → Z | ∃ j : Fin M,
        ε ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - ∫ z, f j z ∂μ|} := by
  intro S hS
  simp only [Set.mem_ofPred_eq] at hS ⊢
  rw [lt_supDeviation_iff μ f S hε] at hS
  obtain ⟨j, hj⟩ := hS
  exact ⟨j, le_of_lt hj⟩

theorem measurable_supDeviation {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    {M n : ℕ} (f : Fin M → Z → ℝ) (hf : ∀ j, Measurable (f j)) :
    Measurable (fun S : Fin n → Z => supDeviation μ f S) := by
  unfold supDeviation
  apply Measurable.iSup
  intro j
  refine Measurable.comp continuous_abs.measurable ?_
  refine Measurable.sub_const ?_ _
  refine Measurable.const_mul ?_ _
  apply Finset.measurable_sum
  intro i _
  exact (hf j).comp (measurable_pi_apply i)

theorem measurableSet_lt_supDeviation {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    {M n : ℕ} (f : Fin M → Z → ℝ) (hf : ∀ j, Measurable (f j)) (c : ℝ) :
    MeasurableSet {S : Fin n → Z | c < supDeviation μ f S} := by
  exact measurableSet_lt measurable_const (measurable_supDeviation μ f hf)

theorem abs_sub_le_ghostSupDeviation {Z : Type*} {M n : ℕ} (f : Fin M → Z → ℝ)
    (S S' : Fin n → Z) (j : Fin M) :
    |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - (n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i)| ≤
      ghostSupDeviation f S S' := by
  unfold ghostSupDeviation
  exact le_ciSup (f := fun j : Fin M => |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) -
      (n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i)|) (Finite.bddAbove_range _) j

theorem ghostSupDeviation_nonneg {Z : Type*} {M n : ℕ} (f : Fin M → Z → ℝ)
    (S S' : Fin n → Z) :
    0 ≤ ghostSupDeviation f S S' := by
  unfold ghostSupDeviation
  exact Real.iSup_nonneg fun _ => abs_nonneg _

theorem ghostSupDeviation_le_iff {Z : Type*} {M n : ℕ} (f : Fin M → Z → ℝ)
    (S S' : Fin n → Z) {c : ℝ} (hc : 0 ≤ c) :
    ghostSupDeviation f S S' ≤ c ↔
      ∀ j : Fin M,
        |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - (n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i)| ≤ c := by
  constructor
  · intro h j
    exact (abs_sub_le_ghostSupDeviation f S S' j).trans h
  · intro h
    unfold ghostSupDeviation
    exact Real.iSup_le h hc

theorem lt_ghostSupDeviation_iff {Z : Type*} {M n : ℕ} (f : Fin M → Z → ℝ)
    (S S' : Fin n → Z) {c : ℝ} (hc : 0 ≤ c) :
    c < ghostSupDeviation f S S' ↔
      ∃ j : Fin M,
        c < |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) - (n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i)| := by
  rcases isEmpty_or_nonempty (Fin M) with hM | hM
  · rw [show ghostSupDeviation f S S' = 0 from @Real.iSup_of_isEmpty _ hM _]
    rw [@IsEmpty.exists_iff _ hM (fun j : Fin M => c < |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) -
        (n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i)|)]
    rw [iff_false, not_lt]
    exact hc
  · exact @lt_ciSup_iff _ _ _ _ hM (fun j : Fin M => |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i) -
      (n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i)|) (Finite.bddAbove_range _)

theorem ghostSupDeviation_comm {Z : Type*} {M n : ℕ} (f : Fin M → Z → ℝ)
    (S S' : Fin n → Z) :
    ghostSupDeviation f S S' = ghostSupDeviation f S' S := by
  simp only [ghostSupDeviation, abs_sub_comm]

theorem ghostSupDeviation_self {Z : Type*} {M n : ℕ} (f : Fin M → Z → ℝ) (S : Fin n → Z) :
    ghostSupDeviation f S S = 0 := by
  simp [ghostSupDeviation]

theorem measurable_ghostSupDeviation {Z : Type*} [MeasurableSpace Z] {M n : ℕ}
    (f : Fin M → Z → ℝ) (hf : ∀ j, Measurable (f j)) :
    Measurable (fun p : (Fin n → Z) × (Fin n → Z) => ghostSupDeviation f p.1 p.2) := by
  unfold ghostSupDeviation
  apply Measurable.iSup
  intro j
  refine Measurable.comp continuous_abs.measurable ?_
  refine Measurable.sub ?_ ?_
  · refine Measurable.const_mul ?_ _
    apply Finset.measurable_sum
    intro i _
    exact (hf j).comp ((measurable_pi_apply i).comp measurable_fst)
  · refine Measurable.const_mul ?_ _
    apply Finset.measurable_sum
    intro i _
    exact (hf j).comp ((measurable_pi_apply i).comp measurable_snd)

theorem measurableSet_lt_ghostSupDeviation {Z : Type*} [MeasurableSpace Z] {M n : ℕ}
    (f : Fin M → Z → ℝ) (hf : ∀ j, Measurable (f j)) (c : ℝ) :
    MeasurableSet {p : (Fin n → Z) × (Fin n → Z) | c < ghostSupDeviation f p.1 p.2} := by
  exact measurableSet_lt measurable_const (measurable_ghostSupDeviation f hf)

theorem ghostSample_map_fst {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (n : ℕ) :
    ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)).map Prod.fst =
      Measure.pi fun _ : Fin n => μ := by
  simp [Measure.map_fst_prod]

theorem ghostSample_map_snd {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (n : ℕ) :
    ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)).map Prod.snd =
      Measure.pi fun _ : Fin n => μ := by
  simp [Measure.map_snd_prod]

theorem indepFun_ghostSample {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (n : ℕ) :
    IndepFun (fun p : (Fin n → Z) × (Fin n → Z) => p.1)
      (fun p : (Fin n → Z) × (Fin n → Z) => p.2)
      ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)) := by
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

theorem binaryErrorIndicator_mem_Icc {α : Type*} {M : ℕ} (h : Fin M → α → Bool) (j : Fin M)
    (p : α × Bool) :
    binaryErrorIndicator h j p ∈ Set.Icc (0 : ℝ) 1 := by
  unfold binaryErrorIndicator
  split_ifs <;> simp

theorem measurable_binaryErrorIndicator {α : Type*} [MeasurableSpace α] {M : ℕ}
    (h : Fin M → α → Bool) (j : Fin M)
    (herr : MeasurableSet {p : α × Bool | h j p.1 ≠ p.2}) :
    Measurable (binaryErrorIndicator h j) := by
  have hfun : binaryErrorIndicator h j = {p : α × Bool | h j p.1 ≠ p.2}.indicator 1 := by
    funext p
    simp only [binaryErrorIndicator, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
  rw [hfun]
  exact measurable_const.indicator herr

end ProbabilityTheory
