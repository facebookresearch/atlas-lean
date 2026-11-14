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
public import Mathlib.Probability.Moments.Variance

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

The main result, `ProbabilityTheory.measureReal_supDeviation_gt_le_two_mul_ghost`, is the
standard symmetrization lemma (Devroye, Györfi and Lugosi, *A Probabilistic Theory of Pattern
Recognition*, Lemma 12.1): for `0 < ε` and `2 ≤ n * ε ^ 2`,
`P {S | ε < supDeviation μ f S} ≤ 2 * (P ⊗ P) {(S, S') | ε / 2 < ghostSupDeviation f S S'}`
with `P = Measure.pi fun _ : Fin n => μ`, strict thresholds `ε` and `ε / 2`, constant `2`, and
the L5-06 hypotheses on `f`. The proof applies Chebyshev's inequality to the ghost empirical mean
of a loss that deviates on `S`, so the ghost event has section probability at least `1 / 2` at
each such `S`, then integrates over the product law (Fubini); the deviating loss is chosen
separately for each `S`, so no measurable choice is needed.
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

/-- Variance of the empirical mean of one `[0, 1]`-valued loss under the sample law. -/
private theorem variance_empiricalMean_le {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {n : ℕ} (g : Z → ℝ) (hg : Measurable g)
    (hbd : ∀ᵐ z ∂μ, g z ∈ Set.Icc (0 : ℝ) 1) :
    variance (fun S : Fin n → Z => (n : ℝ)⁻¹ * ∑ i : Fin n, g (S i))
        (Measure.pi fun _ : Fin n => μ) ≤ (4 * (n : ℝ))⁻¹ := by
  have hmem : MemLp g 2 μ := memLp_of_bounded hbd hg.aestronglyMeasurable 2
  have hfun : (fun S : Fin n → Z => (n : ℝ)⁻¹ * ∑ i : Fin n, g (S i))
      = fun S => (n : ℝ)⁻¹ * ((∑ i : Fin n, fun ω : Fin n → Z => g (ω i)) S) := by
    funext S
    simp [Finset.sum_apply]
  rw [hfun, variance_const_mul]
  have hvar_sum : variance (∑ i : Fin n, fun ω : Fin n → Z => g (ω i))
      (Measure.pi fun _ : Fin n => μ) = ∑ i : Fin n, variance g μ :=
    variance_sum_pi (μ := fun _ : Fin n => μ) (X := fun _ : Fin n => g)
      (fun _ => hmem)
  rw [hvar_sum]
  have hV : variance g μ ≤ 1 / 4 := by
    calc variance g μ ≤ ((1 - 0 : ℝ) / 2) ^ 2 :=
          variance_le_sq_of_bounded hbd hg.aemeasurable
      _ = 1 / 4 := by norm_num
  have hVnn : 0 ≤ variance g μ := variance_nonneg g μ
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    simp
  · have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
    have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have h4n : (4 : ℝ) * (n : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hnR
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    nlinarith [hV, hVnn, hnpos]

/-- Mean of the empirical mean under the sample law, `n > 0`. -/
private theorem integral_empiricalMean {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n) (g : Z → ℝ) (hg : Measurable g)
    (hbd : ∀ᵐ z ∂μ, g z ∈ Set.Icc (0 : ℝ) 1) :
    ∫ S, (n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) ∂(Measure.pi fun _ : Fin n => μ) =
      ∫ z, g z ∂μ := by
  have hgi : Integrable g μ :=
    (memLp_of_bounded hbd hg.aestronglyMeasurable 1).integrable le_rfl
  have hmp : ∀ i : Fin n, MeasurePreserving (Function.eval i)
      (Measure.pi fun _ : Fin n => μ) μ :=
    fun i => measurePreserving_eval (fun _ : Fin n => μ) i
  have hcoord : ∀ i : Fin n,
      ∫ S, g (S i) ∂(Measure.pi fun _ : Fin n => μ) = ∫ z, g z ∂μ := by
    intro i
    have h := integral_map (μ := Measure.pi fun _ : Fin n => μ)
      (φ := Function.eval i) (measurable_pi_apply i).aemeasurable
      hg.aestronglyMeasurable
    rw [(hmp i).map_eq] at h
    exact h.symm
  rw [integral_const_mul,
    integral_finsetSum (f := fun (i : Fin n) (S : Fin n → Z) => g (S i)) Finset.univ
      (fun i _ => (hmp i).integrable_comp_of_integrable hgi)]
  simp_rw [hcoord]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  field_simp

/-- Chebyshev step: under `2 ≤ n ε ^ 2`, one loss's empirical mean leaves the `ε / 2`
neighborhood of its population mean with probability at most `1 / 2`. -/
private theorem measure_abs_empiricalMean_sub_integral_gt_half_le {Z : Type*}
    [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ} (g : Z → ℝ)
    (hg : Measurable g) (hbd : ∀ᵐ z ∂μ, g z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε)
    (hnε : 2 ≤ (n : ℝ) * ε ^ 2) :
    (Measure.pi fun _ : Fin n => μ)
        {S : Fin n → Z | ε / 2 < |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - ∫ z, g z ∂μ|} ≤
      (2 : ENNReal)⁻¹ := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      simp only [Nat.cast_zero, zero_mul] at hnε
      linarith
    · exact hn0
  have hmem : MemLp g 2 μ := memLp_of_bounded hbd hg.aestronglyMeasurable 2
  have hXmem : MemLp (fun S : Fin n → Z => (n : ℝ)⁻¹ * ∑ i : Fin n, g (S i)) 2
      (Measure.pi fun _ : Fin n => μ) := by
    have hsum : MemLp (∑ i : Fin n, fun ω : Fin n → Z => g (ω i)) 2
        (Measure.pi fun _ : Fin n => μ) :=
      memLp_finsetSum' Finset.univ (fun i _ =>
        hmem.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i))
    have hfun : (fun S : Fin n → Z => (n : ℝ)⁻¹ * ∑ i : Fin n, g (S i))
        = fun S => (n : ℝ)⁻¹ * ((∑ i : Fin n, fun ω : Fin n → Z => g (ω i)) S) := by
      funext S
      simp [Finset.sum_apply]
    rw [hfun]
    exact hsum.const_mul _
  have hmean : (Measure.pi fun _ : Fin n => μ)[fun S : Fin n → Z =>
      (n : ℝ)⁻¹ * ∑ i : Fin n, g (S i)] = ∫ z, g z ∂μ :=
    integral_empiricalMean μ hn g hg hbd
  have hcheb : (Measure.pi fun _ : Fin n => μ)
        {S : Fin n → Z | ε / 2 ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - ∫ z, g z ∂μ|} ≤
      ENNReal.ofReal (variance (fun S : Fin n → Z =>
        (n : ℝ)⁻¹ * ∑ i : Fin n, g (S i)) (Measure.pi fun _ : Fin n => μ) /
        (ε / 2) ^ 2) := by
    have h := meas_ge_le_variance_div_sq hXmem (half_pos hε)
    rw [hmean] at h
    exact h
  have hV : variance (fun S : Fin n → Z => (n : ℝ)⁻¹ * ∑ i : Fin n, g (S i))
      (Measure.pi fun _ : Fin n => μ) ≤ (4 * (n : ℝ))⁻¹ :=
    variance_empiricalMean_le μ g hg hbd
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h4n : (0 : ℝ) < 4 * (n : ℝ) := mul_pos (by norm_num) hnpos
  have hreal : variance (fun S : Fin n → Z => (n : ℝ)⁻¹ * ∑ i : Fin n, g (S i))
      (Measure.pi fun _ : Fin n => μ) / (ε / 2) ^ 2 ≤ (2 : ℝ)⁻¹ := by
    rw [div_le_iff₀ (sq_pos_of_ne_zero (ne_of_gt (half_pos hε)))]
    have hbound : (4 * (n : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ * (ε / 2) ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ h4n]
      nlinarith [hnε]
    linarith [hV, hbound]
  have hsub : {S : Fin n → Z | ε / 2 < |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - ∫ z, g z ∂μ|}
      ⊆ {S : Fin n → Z | ε / 2 ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - ∫ z, g z ∂μ|} := by
    intro S hS
    simp only [Set.mem_ofPred_eq] at hS ⊢
    exact hS.le
  calc (Measure.pi fun _ : Fin n => μ)
          {S : Fin n → Z | ε / 2 < |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - ∫ z, g z ∂μ|}
        ≤ (Measure.pi fun _ : Fin n => μ)
          {S : Fin n → Z | ε / 2 ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, g (S i) - ∫ z, g z ∂μ|} :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal (variance (fun S : Fin n → Z =>
            (n : ℝ)⁻¹ * ∑ i : Fin n, g (S i)) (Measure.pi fun _ : Fin n => μ) /
            (ε / 2) ^ 2) := hcheb
      _ ≤ ENNReal.ofReal ((2 : ℝ)⁻¹) := ENNReal.ofReal_le_ofReal hreal
      _ = (2 : ENNReal)⁻¹ := by
          rw [ENNReal.ofReal_inv_of_pos (x := (2 : ℝ)) two_pos, ENNReal.ofReal_ofNat]

/-- Section bound: on the strict uniform-deviation event, the ghost event has section
probability at least `1 / 2`. -/
private theorem inv_two_le_measure_ghost_section {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] {M n : ℕ} (f : Fin M → Z → ℝ)
    (hf : ∀ j, Measurable (f j)) (hbd : ∀ j, ∀ᵐ z ∂μ, f j z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ}
    (hε : 0 < ε) (hnε : 2 ≤ (n : ℝ) * ε ^ 2) {S : Fin n → Z}
    (hS : ε < supDeviation μ f S) :
    (2 : ENNReal)⁻¹ ≤
      (Measure.pi fun _ : Fin n => μ) {S' : Fin n → Z | ε / 2 < ghostSupDeviation f S S'} := by
  obtain ⟨j, hj⟩ := (lt_supDeviation_iff μ f S hε.le).mp hS
  have hmeas : Measurable fun S' : Fin n → Z =>
      (n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i) - ∫ z, f j z ∂μ :=
    ((Finset.measurable_sum Finset.univ
      (fun i _ => (hf j).comp (measurable_pi_apply i))).const_mul _).sub_const _
  have hAm : MeasurableSet {S' : Fin n → Z |
      ε / 2 < |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i) - ∫ z, f j z ∂μ|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hmeas)
  have hsub : {S' : Fin n → Z |
        ε / 2 < |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i) - ∫ z, f j z ∂μ|}ᶜ
      ⊆ {S' : Fin n → Z | ε / 2 < ghostSupDeviation f S S'} := by
    intro S' hS'
    have h2 : |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i) - ∫ z, f j z ∂μ| ≤ ε / 2 := by
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hS'
      exact not_lt.mp hS'
    change ε / 2 < ghostSupDeviation f S S'
    rw [lt_ghostSupDeviation_iff f S S' (half_pos hε).le]
    refine ⟨j, ?_⟩
    have htri := abs_sub_le ((n : ℝ)⁻¹ * ∑ i : Fin n, f j (S i))
      ((n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i)) (∫ z, f j z ∂μ)
    linarith
  have hA_le := measure_abs_empiricalMean_sub_integral_gt_half_le μ (f j) (hf j) (hbd j)
    hε hnε
  have h1 : (Measure.pi fun _ : Fin n => μ)
        {S' : Fin n → Z | ε / 2 < |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i) - ∫ z, f j z ∂μ|}
        + (2 : ENNReal)⁻¹ ≤ 1 :=
    calc _ ≤ (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ := add_le_add hA_le le_rfl
      _ = 1 := ENNReal.inv_two_add_inv_two
  have h2 : (2 : ENNReal)⁻¹ ≤ 1 - (Measure.pi fun _ : Fin n => μ)
      {S' : Fin n → Z | ε / 2 < |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i) - ∫ z, f j z ∂μ|} :=
    ENNReal.le_sub_of_add_le_left
      (measure_ne_top (Measure.pi fun _ : Fin n => μ) _) h1
  calc (2 : ENNReal)⁻¹
        ≤ 1 - (Measure.pi fun _ : Fin n => μ)
          {S' : Fin n → Z | ε / 2 < |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i) - ∫ z, f j z ∂μ|} :=
          h2
      _ = (Measure.pi fun _ : Fin n => μ)
          {S' : Fin n → Z | ε / 2 < |(n : ℝ)⁻¹ * ∑ i : Fin n, f j (S' i) - ∫ z, f j z ∂μ|}ᶜ :=
          (prob_compl_eq_one_sub hAm).symm
      _ ≤ (Measure.pi fun _ : Fin n => μ)
          {S' : Fin n → Z | ε / 2 < ghostSupDeviation f S S'} := measure_mono hsub

/-- **Symmetrization lemma** (Devroye, Györfi and Lugosi, Lemma 12.1) for a finite class of
measurable `[0, 1]`-valued losses: for `0 < ε` and `2 ≤ n ε ^ 2`, the probability that the
uniform deviation exceeds `ε` is at most twice the probability, under the law of an independent
ghost sample, that the ghost deviation exceeds `ε / 2`. -/
theorem measureReal_supDeviation_gt_le_two_mul_ghost {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] {M n : ℕ} (f : Fin M → Z → ℝ)
    (hf : ∀ j, Measurable (f j)) (hbd : ∀ j, ∀ᵐ z ∂μ, f j z ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ}
    (hε : 0 < ε) (hnε : 2 ≤ (n : ℝ) * ε ^ 2) :
    (Measure.pi fun _ : Fin n => μ).real {S | ε < supDeviation μ f S} ≤
      2 * ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)).real
        {p | ε / 2 < ghostSupDeviation f p.1 p.2} := by
  have hG : MeasurableSet {p : (Fin n → Z) × (Fin n → Z) |
      ε / 2 < ghostSupDeviation f p.1 p.2} :=
    measurableSet_lt_ghostSupDeviation (n := n) f hf (ε / 2)
  have hB : MeasurableSet {S : Fin n → Z | ε < supDeviation μ f S} :=
    measurableSet_lt_supDeviation μ (n := n) f hf ε
  have hcore : (2 : ENNReal)⁻¹ * (Measure.pi fun _ : Fin n => μ)
      {S : Fin n → Z | ε < supDeviation μ f S} ≤
      ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
        {p : (Fin n → Z) × (Fin n → Z) | ε / 2 < ghostSupDeviation f p.1 p.2} := by
    rw [Measure.prod_apply hG, ← lintegral_indicator_const hB]
    apply lintegral_mono
    intro S
    by_cases hSB : S ∈ {S : Fin n → Z | ε < supDeviation μ f S}
    · rw [Set.indicator_of_mem hSB]
      have hS : ε < supDeviation μ f S := hSB
      exact inv_two_le_measure_ghost_section μ f hf hbd hε hnε hS
    · rw [Set.indicator_of_notMem hSB]
      exact zero_le
  have h2 : (Measure.pi fun _ : Fin n => μ) {S : Fin n → Z | ε < supDeviation μ f S} ≤
      2 * (((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
        {p : (Fin n → Z) × (Fin n → Z) | ε / 2 < ghostSupDeviation f p.1 p.2}) := by
    have hcancel : (2 : ENNReal) * 2⁻¹ = 1 :=
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
    calc (Measure.pi fun _ : Fin n => μ) {S : Fin n → Z | ε < supDeviation μ f S}
          = 2 * ((2 : ENNReal)⁻¹ * (Measure.pi fun _ : Fin n => μ)
            {S : Fin n → Z | ε < supDeviation μ f S}) := by
            rw [← mul_assoc, hcancel, one_mul]
        _ ≤ 2 * (((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
            {p : (Fin n → Z) × (Fin n → Z) | ε / 2 < ghostSupDeviation f p.1 p.2}) := by
            gcongr
  rw [measureReal_def, measureReal_def]
  calc ((Measure.pi fun _ : Fin n => μ) {S : Fin n → Z | ε < supDeviation μ f S}).toReal
        ≤ (2 * (((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
          {p : (Fin n → Z) × (Fin n → Z) | ε / 2 < ghostSupDeviation f p.1 p.2})).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top _ _)) h2
      _ = 2 * ((((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
          {p : (Fin n → Z) × (Fin n → Z) | ε / 2 < ghostSupDeviation f p.1 p.2})).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat]

end ProbabilityTheory
