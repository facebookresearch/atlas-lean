/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.MetricSpace.CompactCover
public import Mathlib.Topology.Order.Compact

namespace MathlibExtTest.Topology.MetricSpace.CompactCoverTests

private def intervalIncl : C(↥(Set.Icc (0 : ℝ) 1), ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def coverU : Fin 2 → Set ℝ :=
  fun i => if i = 0 then Set.Iio (1 : ℝ) else Set.Ioi (0 : ℝ)

private theorem coverU_open (i : Fin 2) : IsOpen (coverU i) := by
  by_cases h : i = 0
  · simpa [coverU, h] using isOpen_Iio (a := (1 : ℝ))
  · simpa [coverU, h] using isOpen_Ioi (a := (0 : ℝ))

private theorem coverU_cover : (Set.univ : Set ℝ) ⊆ ⋃ i, coverU i := by
  intro x _
  rw [Set.mem_iUnion]
  cases lt_or_ge x (1 : ℝ) with
  | inl hlt =>
    exact ⟨0, by simpa [coverU, Set.mem_Iio] using hlt⟩
  | inr hge =>
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hge
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    exact ⟨1, by simpa [coverU, h10, Set.mem_Ioi] using hx0⟩

example :
    ∃ i0 i1 : Fin 2, i0 ≠ i1 ∧
      intervalIncl '' {⟨(0 : ℝ), le_rfl, zero_le_one⟩} ⊆ coverU i0 ∧
      intervalIncl '' {⟨(1 : ℝ), zero_le_one, le_rfl⟩} ⊆ coverU i1 := by
  have : CompactSpace ↥(Set.Icc (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.exists_diam_lt_subordinate_of_compact intervalIncl coverU coverU_open coverU_cover
  have hpt0 : ∃ i, intervalIncl '' {⟨(0 : ℝ), le_rfl, zero_le_one⟩} ⊆ coverU i := by
    apply hδ
    · exact Set.singleton_nonempty _
    · simpa using hδpos
  have hpt1 : ∃ i, intervalIncl '' {⟨(1 : ℝ), zero_le_one, le_rfl⟩} ⊆ coverU i := by
    apply hδ
    · exact Set.singleton_nonempty _
    · simpa using hδpos
  obtain ⟨i0, hi0⟩ := hpt0
  obtain ⟨i1, hi1⟩ := hpt1
  refine ⟨i0, i1, ?_, hi0, hi1⟩
  intro hEq
  subst i0
  have h0mem : (0 : ℝ) ∈ coverU i1 := by
    have hmem : intervalIncl ⟨(0 : ℝ), le_rfl, zero_le_one⟩ ∈
        intervalIncl '' {⟨(0 : ℝ), le_rfl, zero_le_one⟩} :=
      Set.mem_image_of_mem _ (by simp)
    have h := hi0 hmem
    have h0eq : intervalIncl ⟨(0 : ℝ), le_rfl, zero_le_one⟩ = (0 : ℝ) := rfl
    rw [h0eq] at h
    exact h
  have h1mem : (1 : ℝ) ∈ coverU i1 := by
    have hmem : intervalIncl ⟨(1 : ℝ), zero_le_one, le_rfl⟩ ∈
        intervalIncl '' {⟨(1 : ℝ), zero_le_one, le_rfl⟩} :=
      Set.mem_image_of_mem _ (by simp)
    have h := hi1 hmem
    have h1eq : intervalIncl ⟨(1 : ℝ), zero_le_one, le_rfl⟩ = (1 : ℝ) := rfl
    rw [h1eq] at h
    exact h
  by_cases hi : i1 = 0
  · have hIio : (1 : ℝ) ∈ Set.Iio (1 : ℝ) := by simp [coverU, hi] at h1mem
    exact lt_irrefl _ (Set.mem_Iio.mp hIio)
  · have hIoi : (0 : ℝ) ∈ Set.Ioi (0 : ℝ) := by simp [coverU, hi] at h0mem
    exact lt_irrefl _ (Set.mem_Ioi.mp hIoi)

example :
    ∃ k : ℕ, 0 < k ∧
      ∀ s : Set ↥(Set.Icc (0 : ℝ) 1),
        s.Nonempty → Metric.diam s ≤ (1 / 2 : ℝ) ^ k * Metric.diam (Set.univ : Set ↥(Set.Icc (0 : ℝ) 1)) →
        ∃ i, intervalIncl '' s ⊆ coverU i := by
  have : CompactSpace ↥(Set.Icc (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  have hq0 : (0 : ℝ) ≤ 1 / 2 := div_nonneg zero_le_one two_pos.le
  have hq1 : (1 / 2 : ℝ) < 1 := one_half_lt_one
  have hC : (0 : ℝ) ≤ Metric.diam (Set.univ : Set ↥(Set.Icc (0 : ℝ) 1)) :=
    Metric.diam_nonneg
  obtain ⟨k, hk⟩ :=
    Metric.exists_pow_mul_diam_subordinate_of_compact (1 / 2 : ℝ)
      (Metric.diam (Set.univ : Set ↥(Set.Icc (0 : ℝ) 1)))
      hq0 hq1 hC intervalIncl coverU coverU_open coverU_cover
  have hkpos : 0 < k := by
    by_contra hcon
    have hk0 : k = 0 := Nat.le_zero.mp (not_lt.mp hcon)
    subst hk0
    have huniv : (Set.univ : Set ↥(Set.Icc (0 : ℝ) 1)).Nonempty :=
      ⟨⟨(0 : ℝ), le_rfl, zero_le_one⟩, Set.mem_univ _⟩
    have hdiam : Metric.diam (Set.univ : Set ↥(Set.Icc (0 : ℝ) 1)) ≤
        (1 / 2 : ℝ) ^ 0 * Metric.diam (Set.univ : Set ↥(Set.Icc (0 : ℝ) 1)) := by
      simp
    obtain ⟨i, hi⟩ := hk _ huniv hdiam
    have h0mem : (0 : ℝ) ∈ coverU i := by
      have hmem : intervalIncl ⟨(0 : ℝ), le_rfl, zero_le_one⟩ ∈
          intervalIncl '' (Set.univ : Set ↥(Set.Icc (0 : ℝ) 1)) :=
        Set.mem_image_of_mem _ (Set.mem_univ _)
      have h := hi hmem
      have h0eq : intervalIncl ⟨(0 : ℝ), le_rfl, zero_le_one⟩ = (0 : ℝ) := rfl
      rw [h0eq] at h
      exact h
    have h1mem : (1 : ℝ) ∈ coverU i := by
      have hmem : intervalIncl ⟨(1 : ℝ), zero_le_one, le_rfl⟩ ∈
          intervalIncl '' (Set.univ : Set ↥(Set.Icc (0 : ℝ) 1)) :=
        Set.mem_image_of_mem _ (Set.mem_univ _)
      have h := hi hmem
      have h1eq : intervalIncl ⟨(1 : ℝ), zero_le_one, le_rfl⟩ = (1 : ℝ) := rfl
      rw [h1eq] at h
      exact h
    by_cases hi0 : i = 0
    · have hIio : (1 : ℝ) ∈ Set.Iio (1 : ℝ) := by simp [coverU, hi0] at h1mem
      exact lt_irrefl _ (Set.mem_Iio.mp hIio)
    · have hIoi : (0 : ℝ) ∈ Set.Ioi (0 : ℝ) := by simp [coverU, hi0] at h0mem
      exact lt_irrefl _ (Set.mem_Ioi.mp hIoi)
  exact ⟨k, hkpos, hk⟩

end MathlibExtTest.Topology.MetricSpace.CompactCoverTests
