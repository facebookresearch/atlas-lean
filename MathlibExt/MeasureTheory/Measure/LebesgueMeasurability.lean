/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.GDelta.Basic

/-!
# Lebesgue measurability by open and closed approximation

In Tao's *An Introduction to Measure Theory* a set `E ⊆ ℝᵈ` is *Lebesgue measurable* when for
every `ε > 0` it is contained in an open set `U` with `m*(U \ E) ≤ ε` (Definition 1.2.2, "outer
approximation by open sets"; Littlewood's first principle). Mathlib instead defines Lebesgue
measurability as null-measurability for `volume`, that is, measurability for the completion of
Lebesgue measure. This file proves that the two notions agree, for every outer regular,
σ-finite measure on a topological space (Lebesgue measure on `ℝᵈ` among them), together with the
equivalent forms "a `G_δ` set minus a null set" (Tao, Exercise 1.2.19 (i) ⇔ (ii)) and "inner
approximation by closed sets" (Tao, Exercise 1.2.7 (i) ⇔ (iv)).

Mathlib's `MeasurableSet.exists_isOpen_sdiff_lt` gives the outer approximation only for measurable
sets of finite measure; the σ-finite case uses the `ε / 2ⁿ` trick over a spanning sequence.

## Main results

* `MeasureTheory.NullMeasurableSet.exists_isOpen_measure_sdiff_le`: outer approximation by open
  sets for null-measurable sets of possibly infinite measure.
* `MeasureTheory.nullMeasurableSet_of_forall_exists_isOpen`: the converse, for any measure.
* `MeasureTheory.nullMeasurableSet_iff_forall_exists_isOpen`: Tao's definition of Lebesgue
  measurability agrees with Mathlib's.
* `MeasureTheory.nullMeasurableSet_iff_exists_isGδ`: `E` is null-measurable iff it is contained in
  a `G_δ` set `G` with `μ (G \ E) = 0`.
* `MeasureTheory.nullMeasurableSet_iff_forall_exists_isClosed`: inner approximation by closed sets.

## References

* T. Tao, *An Introduction to Measure Theory*, Graduate Studies in Mathematics 126, AMS, 2011,
  Definition 1.2.2, Lemma 1.2.13, Exercise 1.2.7 and Exercise 1.2.19.
-/

@[expose] public section

open Set Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] {μ : Measure α} {E : Set α}

/-- **Outer approximation by open sets** (Tao, *An Introduction to Measure Theory*,
Lemma 1.2.13 and Exercise 1.2.7 (ii)). For an outer regular, σ-finite measure `μ`, every
null-measurable set `E`, of finite or infinite measure, is contained in open sets `U` with
`μ (U \ E)` arbitrarily small. -/
theorem NullMeasurableSet.exists_isOpen_measure_sdiff_le [μ.OuterRegular] [SigmaFinite μ]
    (hE : NullMeasurableSet E μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U, E ⊆ U ∧ IsOpen U ∧ μ (U \ E) ≤ ε := by
  -- Split the error budget: `ε / 2` for a measurable kernel `T ⊆ E`, `ε / 2` for `E \ T`.
  have hε2 : ε / 2 ≠ 0 := by simpa using hε
  obtain ⟨T, hTE, hT, hTae⟩ := hE.exists_measurable_subset_ae_eq
  have hnull : μ (E \ T) = 0 := by
    rw [← ae_le_set]; exact hTae.symm.le
  -- The measurable kernel, piece by piece over a spanning sequence, with errors `ε' n`.
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε2 ℕ
  have hpiece : ∀ n, ∃ U, T ∩ spanningSets μ n ⊆ U ∧ IsOpen U ∧
      μ (U \ (T ∩ spanningSets μ n)) ≤ ε' n := by
    intro n
    obtain ⟨U, hU, hUo, -, hUlt⟩ :=
      (hT.inter (measurableSet_spanningSets μ n)).exists_isOpen_sdiff_lt (ε := ε' n)
        ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
        (by exact_mod_cast (hε'pos n).ne')
    exact ⟨U, hU, hUo, hUlt.le⟩
  choose U hTU hUo hUle using hpiece
  -- The null remainder `E \ T` sits in an open set of measure at most `ε / 2`.
  obtain ⟨V, hEV, hVo, hVlt⟩ := Set.exists_isOpen_lt_of_lt (μ := μ) (E \ T) (ε / 2)
    (by rw [hnull]; exact pos_iff_ne_zero.mpr hε2)
  refine ⟨(⋃ n, U n) ∪ V, fun x hx => ?_, (isOpen_iUnion hUo).union hVo, ?_⟩
  · by_cases hxT : x ∈ T
    · obtain ⟨n, hn⟩ := mem_iUnion.mp (by rw [iUnion_spanningSets]; exact mem_univ x :
        x ∈ ⋃ n, spanningSets μ n)
      exact Or.inl (mem_iUnion.mpr ⟨n, hTU n ⟨hxT, hn⟩⟩)
    · exact Or.inr (hEV ⟨hx, hxT⟩)
  · have hsub : ((⋃ n, U n) ∪ V) \ E ⊆ (⋃ n, U n \ (T ∩ spanningSets μ n)) ∪ V := by
      rintro x ⟨hxU | hxV, hxE⟩
      · obtain ⟨n, hn⟩ := mem_iUnion.mp hxU
        exact Or.inl (mem_iUnion.mpr ⟨n, hn, fun h => hxE (hTE h.1)⟩)
      · exact Or.inr hxV
    calc μ (((⋃ n, U n) ∪ V) \ E)
        ≤ μ ((⋃ n, U n \ (T ∩ spanningSets μ n)) ∪ V) := measure_mono hsub
      _ ≤ μ (⋃ n, U n \ (T ∩ spanningSets μ n)) + μ V := measure_union_le _ _
      _ ≤ (∑' n, μ (U n \ (T ∩ spanningSets μ n))) + ε / 2 :=
          add_le_add (measure_iUnion_le _) hVlt.le
      _ ≤ (∑' n, (ε' n : ℝ≥0∞)) + ε / 2 := by gcongr with n; exact hUle n
      _ ≤ ε / 2 + ε / 2 := by gcongr
      _ = ε := ENNReal.add_halves ε

/-- If `E` is contained in open sets `U` with `μ (U \ E)` arbitrarily small, then `E` is the
`G_δ` set `⋂ₙ Uₙ` minus a null set (Tao, *An Introduction to Measure Theory*, Exercise 1.2.19
(i) ⇒ (ii), by the argument in the proof of Lemma 1.2.13 (v)). No regularity of `μ` is needed. -/
theorem exists_isGδ_of_forall_exists_isOpen
    (h : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ U, E ⊆ U ∧ IsOpen U ∧ μ (U \ E) ≤ ε) :
    ∃ G, IsGδ G ∧ E ⊆ G ∧ μ (G \ E) = 0 := by
  choose U hEU hUo hUle using fun n : ℕ => h (n : ℝ≥0∞)⁻¹ (by simp)
  refine ⟨⋂ n, U n, .iInter_of_isOpen hUo, subset_iInter hEU, ?_⟩
  refine nonpos_iff_eq_zero.mp (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun n => ?_)
  exact (measure_mono (sdiff_subset_sdiff_left (iInter_subset _ n))).trans (hUle n)

/-- A subset of a `G_δ` set `G` with `μ (G \ E) = 0` is null-measurable (Tao, *An Introduction to
Measure Theory*, Exercise 1.2.19 (ii) ⇒ (i)). -/
theorem nullMeasurableSet_of_isGδ [OpensMeasurableSpace α] {G : Set α} (hG : IsGδ G)
    (hEG : E ⊆ G) (h0 : μ (G \ E) = 0) : NullMeasurableSet E μ := by
  have : E = G \ (G \ E) := by
    ext x; constructor
    · intro hx; exact ⟨hEG hx, fun h => h.2 hx⟩
    · rintro ⟨hxG, hx⟩; by_contra hxE; exact hx ⟨hxG, hxE⟩
  rw [this]
  exact hG.measurableSet.nullMeasurableSet.diff (NullMeasurableSet.of_null h0)

/-- **Tao's definition of Lebesgue measurability implies null-measurability**: if `E` is
contained in open sets `U` with `μ (U \ E)` arbitrarily small, then `E` is null-measurable
(Tao, *An Introduction to Measure Theory*, Definition 1.2.2 and Lemma 1.2.13). No regularity of
`μ` is needed. -/
theorem nullMeasurableSet_of_forall_exists_isOpen [OpensMeasurableSpace α]
    (h : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ U, E ⊆ U ∧ IsOpen U ∧ μ (U \ E) ≤ ε) :
    NullMeasurableSet E μ := by
  obtain ⟨G, hG, hEG, h0⟩ := exists_isGδ_of_forall_exists_isOpen h
  exact nullMeasurableSet_of_isGδ hG hEG h0

/-- **Lebesgue measurability by outer approximation** (Tao, *An Introduction to Measure Theory*,
Definition 1.2.2 and Exercise 1.2.7 (i) ⇔ (ii)). For an outer regular, σ-finite measure, such as
Lebesgue measure on `ℝᵈ`, a set is null-measurable iff for every `ε > 0` it is contained in an
open set `U` with `μ (U \ E) ≤ ε`. -/
theorem nullMeasurableSet_iff_forall_exists_isOpen [OpensMeasurableSpace α] [μ.OuterRegular]
    [SigmaFinite μ] :
    NullMeasurableSet E μ ↔ ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ U, E ⊆ U ∧ IsOpen U ∧ μ (U \ E) ≤ ε :=
  ⟨fun hE _ hε => hE.exists_isOpen_measure_sdiff_le hε, nullMeasurableSet_of_forall_exists_isOpen⟩

/-- **Measurable sets are `G_δ` sets up to null sets** (Tao, *An Introduction to Measure Theory*,
Exercise 1.2.19 (i) ⇔ (ii)). For an outer regular, σ-finite measure, `E` is null-measurable iff
`E ⊆ G` for some `G_δ` set `G` with `μ (G \ E) = 0`. -/
theorem nullMeasurableSet_iff_exists_isGδ [OpensMeasurableSpace α] [μ.OuterRegular]
    [SigmaFinite μ] :
    NullMeasurableSet E μ ↔ ∃ G, IsGδ G ∧ E ⊆ G ∧ μ (G \ E) = 0 :=
  ⟨fun hE => exists_isGδ_of_forall_exists_isOpen fun _ hε => hE.exists_isOpen_measure_sdiff_le hε,
    fun ⟨_, hG, hEG, h0⟩ => nullMeasurableSet_of_isGδ hG hEG h0⟩

/-- **Inner approximation by closed sets** (Tao, *An Introduction to Measure Theory*,
Exercise 1.2.7 (i) ⇔ (iv)). For an outer regular, σ-finite measure, `E` is null-measurable iff for
every `ε > 0` it contains a closed set `F` with `μ (E \ F) ≤ ε`. -/
theorem nullMeasurableSet_iff_forall_exists_isClosed [OpensMeasurableSpace α] [μ.OuterRegular]
    [SigmaFinite μ] :
    NullMeasurableSet E μ ↔ ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ F, F ⊆ E ∧ IsClosed F ∧ μ (E \ F) ≤ ε := by
  rw [← NullMeasurableSet.compl_iff, nullMeasurableSet_iff_forall_exists_isOpen]
  refine forall₂_congr fun ε _ => ⟨fun ⟨U, hU, hUo, hUle⟩ => ⟨Uᶜ, ?_, hUo.isClosed_compl, ?_⟩,
    fun ⟨F, hF, hFc, hFle⟩ => ⟨Fᶜ, compl_subset_compl.mpr hF, hFc.isOpen_compl, ?_⟩⟩
  · exact compl_subset_comm.mp hU
  · convert hUle using 2; ext x; simp [and_comm]
  · convert hFle using 2; ext x; simp [and_comm]

end MeasureTheory
