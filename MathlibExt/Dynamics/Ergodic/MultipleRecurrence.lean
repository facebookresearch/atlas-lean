/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import MathlibExt.Combinatorics.Additive.Szemeredi

/-!
# Furstenberg multiple recurrence

This file proves Furstenberg's multiple recurrence theorem for a measure-preserving
transformation of a probability space.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Dynamics.Ergodic.MultipleRecurrenceWanted

private noncomputable def furstVisitCount {α : Type*} (T : α → α) (A : Set α)
    (N : ℕ) (x : α) : ℕ := by
  classical
  exact ((Finset.range N).filter fun m => T^[m] x ∈ A).card

private theorem furst_visitCount_eq_sum_indicator {α : Type*} (T : α → α) (A : Set α)
    (N : ℕ) (x : α) :
    (furstVisitCount T A N x : ℝ≥0∞) =
      ∑ m ∈ Finset.range N, (T^[m] ⁻¹' A).indicator 1 x := by
  classical
  simp only [furstVisitCount, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Set.indicator_apply, Set.mem_preimage, Pi.one_apply, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]

private theorem furst_visitCount_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} (hT : MeasurePreserving T μ μ)
    {A : Set α} (hA : MeasurableSet A) (N : ℕ) :
    (∫⁻ x, (furstVisitCount T A N x : ℝ≥0∞) ∂μ) = (N : ℝ≥0∞) * μ A := by
  classical
  simp_rw [furst_visitCount_eq_sum_indicator]
  rw [lintegral_finsetSum]
  · simp only [lintegral_indicator_one, hA.preimage (hT.iterate _).measurable,
      (hT.iterate _).measure_preimage hA.nullMeasurableSet, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  · intro m _hm
    exact measurable_one.indicator (hA.preimage (hT.iterate m).measurable)

private theorem furst_goodSet_pos {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) {A : Set α} (hA : MeasurableSet A)
    (hApos : 0 < μ A) {N : ℕ} (hN : 0 < N) :
    0 < μ {x | (μ A).toReal / 2 * (N : ℝ) ≤ (furstVisitCount T A N x : ℝ)} := by
  rw [pos_iff_ne_zero]
  intro hzero
  have houtside :
      ∀ᵐ x ∂μ, x ∉ {x | (μ A).toReal / 2 * (N : ℝ) ≤ (furstVisitCount T A N x : ℝ)} := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hzero
  have hthreshold_nonneg : 0 ≤ (μ A).toReal / 2 * (N : ℝ) := by positivity
  have hpointwise : ∀ᵐ x ∂μ, (furstVisitCount T A N x : ℝ≥0∞) ≤
      ENNReal.ofReal ((μ A).toReal / 2 * (N : ℝ)) := by
    filter_upwards [houtside] with x hx
    apply (ENNReal.toReal_le_toReal (by simp) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hthreshold_nonneg]
    exact (lt_of_not_ge hx).le
  have hint : (N : ℝ≥0∞) * μ A ≤
      ENNReal.ofReal ((μ A).toReal / 2 * (N : ℝ)) := by
    rw [← furst_visitCount_lintegral hT hA N]
    calc
      (∫⁻ x, (furstVisitCount T A N x : ℝ≥0∞) ∂μ) ≤
          ∫⁻ _x, ENNReal.ofReal ((μ A).toReal / 2 * (N : ℝ)) ∂μ :=
        lintegral_mono_ae hpointwise
      _ = ENNReal.ofReal ((μ A).toReal / 2 * (N : ℝ)) := by simp
  have hreal :=
    (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mpr hint
  have hAreal : 0 < (μ A).toReal :=
    ENNReal.toReal_pos (ne_of_gt hApos) (measure_ne_top μ A)
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hthreshold_nonneg] at hreal
  nlinarith

private def furstProgressionSet {α : Type*} (T : α → α) (A : Set α)
    (k a d : ℕ) : Set α :=
  ⋂ i ∈ Finset.range k, T^[a + i * d] ⁻¹' A

private theorem furst_szemeredi_at_good {α : Type*} {T : α → α} {A : Set α}
    {k N : ℕ} {δ : ℝ} (hk : 2 ≤ k)
    (hSz : ∀ B : Finset ℕ, B ⊆ Finset.range N →
      δ * (N : ℝ) ≤ (B.card : ℝ) →
        ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ B)
    {x : α} (hx : δ * (N : ℝ) ≤ (furstVisitCount T A N x : ℝ)) :
    ∃ a ∈ Finset.range N, ∃ d ∈ (Finset.range N).filter (0 < ·),
      x ∈ furstProgressionSet T A k a d := by
  classical
  let S := (Finset.range N).filter fun m => T^[m] x ∈ A
  have hSsub : S ⊆ Finset.range N := Finset.filter_subset _ _
  have hScard : δ * (N : ℝ) ≤ (S.card : ℝ) := by
    simpa [S, furstVisitCount] using hx
  obtain ⟨a, d, hd, hap⟩ := hSz S hSsub hScard
  have haS : a ∈ S := by simpa using hap 0 (by omega)
  have hadS := hap 1 (by omega)
  have haN : a < N := Finset.mem_range.mp (hSsub haS)
  have hadN : a + d < N := by
    apply Finset.mem_range.mp (hSsub ?_)
    simpa using hadS
  have hdN : d < N := by omega
  refine ⟨a, Finset.mem_range.mpr haN, d, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hdN, hd⟩
  · rw [furstProgressionSet]
    simp only [Set.mem_iInter, Set.mem_preimage]
    intro i hi
    exact (Finset.mem_filter.mp (hap i (Finset.mem_range.mp hi))).2

private theorem furst_exists_positive_progression {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} {A : Set α} {k N : ℕ} {δ : ℝ}
    (hk : 2 ≤ k)
    (hSz : ∀ B : Finset ℕ, B ⊆ Finset.range N →
      δ * (N : ℝ) ≤ (B.card : ℝ) →
        ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ B)
    (hgood : 0 < μ {x | δ * (N : ℝ) ≤ (furstVisitCount T A N x : ℝ)}) :
    ∃ a ∈ Finset.range N, ∃ d ∈ (Finset.range N).filter (0 < ·),
      0 < μ (furstProgressionSet T A k a d) := by
  classical
  by_contra hnone
  have hnull : ∀ a ∈ Finset.range N, ∀ d ∈ (Finset.range N).filter (0 < ·),
      μ (furstProgressionSet T A k a d) = 0 := by
    intro a ha d hd
    apply nonpos_iff_eq_zero.mp
    apply not_lt.mp
    intro hpos
    exact hnone ⟨a, ha, d, hd, hpos⟩
  have hcover : {x | δ * (N : ℝ) ≤ (furstVisitCount T A N x : ℝ)} ⊆
      ⋃ a ∈ Finset.range N, ⋃ d ∈ (Finset.range N).filter (0 < ·),
        furstProgressionSet T A k a d := by
    intro x hx
    obtain ⟨a, ha, d, hd, hxd⟩ := furst_szemeredi_at_good hk hSz hx
    simp only [Set.mem_iUnion]
    exact ⟨a, ha, d, hd, hxd⟩
  have hunion :
      μ (⋃ a ∈ Finset.range N, ⋃ d ∈ (Finset.range N).filter (0 < ·),
        furstProgressionSet T A k a d) = 0 := by
    apply nonpos_iff_eq_zero.mp
    calc
      μ (⋃ a ∈ Finset.range N, ⋃ d ∈ (Finset.range N).filter (0 < ·),
          furstProgressionSet T A k a d) ≤
          ∑ a ∈ Finset.range N,
            μ (⋃ d ∈ (Finset.range N).filter (0 < ·),
              furstProgressionSet T A k a d) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ a ∈ Finset.range N, ∑ d ∈ (Finset.range N).filter (0 < ·),
          μ (furstProgressionSet T A k a d) := by
        apply Finset.sum_le_sum
        intro a _ha
        exact measure_biUnion_finset_le _ _
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        apply Finset.sum_eq_zero
        intro d hd
        exact hnull a ha d hd
  exact (ne_of_gt hgood) (measure_mono_null hcover hunion)

private theorem furst_unshift_progression {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} (hT : MeasurePreserving T μ μ)
    {A : Set α} (hA : MeasurableSet A) {k a d : ℕ}
    (hpos : 0 < μ (furstProgressionSet T A k a d)) :
    0 < μ (⋂ i ∈ Finset.range k, T^[i * d] ⁻¹' A) := by
  let B := ⋂ i ∈ Finset.range k, T^[i * d] ⁻¹' A
  have hB : MeasurableSet B := by
    dsimp [B]
    apply Finset.measurableSet_biInter
    intro i _hi
    exact hA.preimage (hT.iterate (i * d)).measurable
  have hset : furstProgressionSet T A k a d = T^[a] ⁻¹' B := by
    ext x
    simp only [furstProgressionSet, B, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro hx i hi
      have hiA := hx i hi
      rw [show a + i * d = i * d + a by omega, Function.iterate_add_apply] at hiA
      exact hiA
    · intro hx i hi
      have hiA := hx i hi
      rw [← Function.iterate_add_apply T (i * d) a x] at hiA
      simpa [Nat.add_comm] using hiA
  rw [hset, (hT.iterate a).measure_preimage hB.nullMeasurableSet] at hpos
  simpa [B] using hpos

/--
**Furstenberg multiple recurrence theorem.** Let $\mu$ be a probability measure on a measurable
space $\alpha$, let $T : \alpha \to \alpha$ be a measurable map preserving $\mu$, and let $A$ be a
measurable set with $\mu(A) > 0$. For $m \in \mathbb{N}$ write $T^{-m}(A)$ for the preimage of $A$
under the $m$-th iterate of $T$. Then for every integer $k > 0$ there is an integer $n > 0$ such
that

$$\mu\Big(\bigcap_{i=0}^{k-1} T^{-i n}(A)\Big) > 0.$$

Proves `Wanted` entry `furstenberg_multipleRecurrence`.

Proof: We apply the finitary Szemerédi theorem to dense sets of return times in finite orbit
segments, using an averaging argument to obtain a positive-measure family of such segments.

Source: H. Furstenberg, J. Analyse Math. 31 (1977) and Recurrence in Ergodic Theory (1981); Lean
states one-transformation arithmetic-progression k-term intersection form without ergodicity
hypothesis.
-/
public theorem furstenberg_multipleRecurrence
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ)
    {A : Set α} (hA : MeasurableSet A) (hApos : 0 < μ A)
    (k : ℕ) (hk : 0 < k) :
    ∃ n : ℕ, 0 < n ∧ 0 < μ (⋂ i ∈ Finset.range k, T^[i * n] ⁻¹' A) := by
  by_cases hk1 : k = 1
  · subst k
    refine ⟨1, by omega, ?_⟩
    simpa using hApos
  have hk2 : 2 ≤ k := by omega
  let δ : ℝ := (μ A).toReal / 2
  have hAreal : 0 < (μ A).toReal :=
    ENNReal.toReal_pos (ne_of_gt hApos) (measure_ne_top μ A)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨N₀, hN₀⟩ :=
    MathlibExt.Combinatorics.Additive.SzemerediWanted.szemeredi k hk δ hδ
  let N := N₀ + 1
  have hNpos : 0 < N := by omega
  have hN₀N : N₀ ≤ N := by omega
  have hSz : ∀ B : Finset ℕ, B ⊆ Finset.range N →
      δ * (N : ℝ) ≤ (B.card : ℝ) →
        ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ B :=
    hN₀ N hN₀N
  have hgood :
      0 < μ {x | δ * (N : ℝ) ≤ (furstVisitCount T A N x : ℝ)} := by
    simpa [δ] using furst_goodSet_pos hT hA hApos hNpos
  obtain ⟨a, _ha, d, hd, hpos⟩ :=
    furst_exists_positive_progression hk2 hSz hgood
  have hdpos : 0 < d := (Finset.mem_filter.mp hd).2
  exact ⟨d, hdpos, furst_unshift_progression hT hA hpos⟩

end MathlibExt.Dynamics.Ergodic.MultipleRecurrenceWanted
