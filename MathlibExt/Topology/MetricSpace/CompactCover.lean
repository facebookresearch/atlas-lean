/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

namespace Metric

universe w

/-!
# Neutral compact-cover subordination

Lebesgue-number/diameter corollaries for a continuous map from a compact
pseudometric space, plus the coefficient-free geometric-decay variant used by
iterated subdivision. No homology, simplex, or convexity API.
-/

/-- Lebesgue-number estimate for a continuous map from an arbitrary compact
pseudometric space: every sufficiently small-diameter nonempty set has `g`-image
subordinate to a given open cover of the target. -/
theorem exists_diam_lt_subordinate_of_compact
    {K : Type w} [PseudoMetricSpace K] [CompactSpace K]
    {X : Type*} [TopologicalSpace X]
    (g : C(K, X)) {ι : Sort*} (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    ∃ δ > 0, ∀ s : Set K,
      s.Nonempty → Metric.diam s < δ → ∃ i, g '' s ⊆ U i := by
  have hpreOpen : ∀ i, IsOpen (g ⁻¹' U i) :=
    fun i => (hUopen i).preimage g.continuous
  have hpreCover : (Set.univ : Set K) ⊆ ⋃ i, g ⁻¹' U i := by
    intro y _
    have hy : g y ∈ (Set.univ : Set X) := Set.mem_univ _
    have hmem := hUcover hy
    rw [Set.mem_iUnion] at hmem ⊢
    obtain ⟨i, hi⟩ := hmem
    exact ⟨i, hi⟩
  obtain ⟨δ, hδpos, hδcov⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hpreOpen hpreCover
  refine ⟨δ, hδpos, fun s hs hdiam => ?_⟩
  obtain ⟨x, hx⟩ := hs
  obtain ⟨i, hi⟩ := hδcov x (Set.mem_univ _)
  have hbd : Bornology.IsBounded s :=
    (isCompact_univ.isBounded).subset (Set.subset_univ s)
  have hball : s ⊆ Metric.ball x δ := by
    intro y hy
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.dist_le_diam_of_mem hbd hy hx) hdiam
  exact ⟨i, Set.image_subset_iff.mpr (hball.trans hi)⟩

/-- Geometric-decay subordinate cover for a compact pseudometric domain:
for `0 ≤ q`, `q < 1`, and `0 ≤ C` there is `k` so that every nonempty set with diameter at most
`q ^ k * C` has `g`-image subordinate to the given open cover. -/
theorem exists_pow_mul_diam_subordinate_of_compact
    (q C : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    {K : Type w} [PseudoMetricSpace K] [CompactSpace K]
    {X : Type*} [TopologicalSpace X]
    (g : C(K, X)) {ι : Sort*} (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    ∃ k : ℕ, ∀ s : Set K,
      s.Nonempty → Metric.diam s ≤ q ^ k * C → ∃ i, g '' s ⊆ U i := by
  obtain ⟨δ, hδpos, hδsmall⟩ :=
    exists_diam_lt_subordinate_of_compact (K := K) g U hUopen hUcover
  by_cases hC0 : C = 0
  · refine ⟨0, fun s hs hdiam => hδsmall s hs ?_⟩
    have h0 : q ^ 0 * C = 0 := by simp [hC0]
    have hle : Metric.diam s ≤ 0 := h0 ▸ hdiam
    exact lt_of_le_of_lt hle hδpos
  · have hCpos : 0 < C := lt_of_le_of_ne hC (fun h => hC0 h.symm)
    have _ : 0 ≤ q := hq0
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hδpos hCpos) hq1
    refine ⟨k, fun s hs hdiam => hδsmall s hs (lt_of_le_of_lt hdiam ?_)⟩
    have hCne : C ≠ 0 := ne_of_gt hCpos
    have h1 : q ^ k * C < (δ / C) * C :=
      mul_lt_mul_of_pos_right hk hCpos
    have h2 : (δ / C) * C = δ := div_mul_cancel₀ δ hCne
    rwa [h2] at h1

end Metric
