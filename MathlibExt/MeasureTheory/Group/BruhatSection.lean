/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions adapted from `anthropics/fermats-last-theorem` at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, the paired `Theorems/Thm_` and
`P2M/Sol/S_` files with stems:
* `MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul`
* `MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one`
* `MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant`
* `MeasureTheory_exists_continuous_integral_subgroup_mul_eq_one`
* `MeasureTheory_exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact`
Source: https://github.com/anthropics/fermats-last-theorem
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in their file headers.
Released under the Apache License, Version 2.0.
The extraction framework is removed. The common construction uses a positive
floor for the orbit average and works without separation or countability
hypotheses.
-/

module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.UrysohnsLemma

/-!
# Continuous Bruhat cutoffs

A closed-embedding homomorphism into a locally compact group admits continuous,
nonnegative compactly supported cutoffs normalized on the saturation of any
compact set. The acting measure is positive on nonempty open sets, finite on
compact sets, and right invariant. Neither group needs to be Hausdorff or
countable.

The denominator is the orbit average of a bump function, bounded below by a
positive constant before division. This ensures continuity even outside the
saturation where normalization is required. The older measurable subgroup
existence theorem is a corollary of this construction.
-/

public section

open scoped Pointwise Topology

namespace MeasureTheory

section Hom

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  (τ : Measure H) [IsFiniteMeasureOnCompacts τ]
  (ι : H →* G) (hι : Topology.IsClosedEmbedding ι)

include hι

omit [IsTopologicalGroup H] in
private theorem continuous_integral_comp_mul {f : G → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (fun x => ∫ h, f (ι h * x) ∂τ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hN, hx₀⟩ := exists_compact_mem_nhds x₀
  have hk : IsCompact (ι ⁻¹' (tsupport f * N⁻¹)) :=
    hι.isCompact_preimage (hfc.isCompact.mul hN.inv)
  have hc : ContinuousOn (fun x => ∫ h, f (ι h * x) ∂τ) N := by
    refine continuousOn_integral_of_compact_support hk ?_ ?_
    · exact (hf.comp ((hι.continuous.comp continuous_snd).mul
        continuous_fst)).continuousOn
    · intro x h hx hh
      by_contra hne
      exact hh ⟨ι h * x, subset_tsupport f hne,
        x⁻¹, Set.inv_mem_inv.mpr hx, by simp⟩
  exact hc.continuousAt hx₀

/-- **Continuous cutoff for a closed-embedding homomorphism.**
A continuous nonnegative compactly supported cutoff normalized on every
left orbit meeting `K`, for a closed-embedding homomorphism `ι`. The measure
may have any scale. No Hausdorff or countability hypotheses are required. -/
theorem exists_continuous_cutoff_of_isClosedEmbedding
    [τ.IsOpenPosMeasure] [τ.IsMulRightInvariant]
    (K : Set G) (hK : IsCompact K) :
    ∃ w : G → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ x, 0 ≤ w x) ∧
      ∀ (h : H) (k : G), k ∈ K → ∫ h', w (ι h' * (ι h * k)) ∂τ = 1 := by
  obtain ⟨b, hbK, -, hbc, hb01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  have hb0 : ∀ x, 0 ≤ b x := fun x => (hb01 x).1
  let A : G → ℝ := fun x => ∫ h, b (ι h * x) ∂τ
  have hAc : Continuous A := continuous_integral_comp_mul τ ι hι b.continuous hbc
  have hAi : ∀ (h : H) (x : G), A (ι h * x) = A x := by
    intro h x
    have heq : (fun h' => b (ι h' * (ι h * x))) =
        fun h' => (fun s => b (ι s * x)) (h' * h) := by
      funext h'
      simp only [map_mul, mul_assoc]
    change ∫ h', b (ι h' * (ι h * x)) ∂τ = _
    rw [heq]
    exact integral_mul_right_eq_self (fun s => b (ι s * x)) h
  have hApos : ∀ k ∈ K, 0 < A k := by
    intro k hk
    have he : Topology.IsClosedEmbedding (fun h => ι h * k) :=
      (Homeomorph.mulRight k).isClosedEmbedding.comp hι
    exact (b.continuous.comp he.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hbc.comp_isClosedEmbedding he) (fun h => hb0 _) (x := 1)
      (by simp [hbK hk])
  obtain ⟨m, hm, hmK⟩ : ∃ m : ℝ, 0 < m ∧ ∀ k ∈ K, m ≤ A k := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun k hk => by simp [hKe] at hk⟩
    · obtain ⟨k, hk, hmin⟩ := hK.exists_isMinOn hKne hAc.continuousOn
      exact ⟨A k, hApos k hk, fun k' hk' => hmin hk'⟩
  refine ⟨fun x => b x / max (A x) m, ?_, ?_, ?_, ?_⟩
  · exact b.continuous.div (hAc.max continuous_const)
      (fun x => (lt_max_of_lt_right hm).ne')
  · refine hbc.mono fun x hx => ?_
    exact fun hb => hx (by simp [hb])
  · exact fun x => div_nonneg (hb0 x) (le_max_of_le_right hm.le)
  · intro h k hk
    have hx : m ≤ A (ι h * k) := by rw [hAi]; exact hmK k hk
    have heq : ∀ h', max (A (ι h' * (ι h * k))) m = A (ι h * k) := by
      intro h'
      rw [hAi, max_eq_left hx]
    simp_rw [heq]
    rw [integral_div]
    exact div_self (lt_of_lt_of_le hm hx).ne'

end Hom

/-- **Continuous Bruhat cutoff for a closed subgroup.**
A continuous nonnegative compactly supported Bruhat cutoff for a closed
subgroup, normalized on any subset of the saturation of a compact set. -/
theorem exists_continuous_cutoff_of_subset_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (T : Subgroup G) (hT : IsClosed (T : Set G))
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T)
    [IsFiniteMeasureOnCompacts τ] [τ.IsOpenPosMeasure] [τ.IsMulRightInvariant]
    {E K : Set G} (hK : IsCompact K) (hE : E ⊆ (T : Set G) * K) :
    ∃ w : G → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ x, 0 ≤ w x) ∧
      ∀ x ∈ E, ∫ t : T, w ((t : G) * x) ∂τ = 1 := by
  obtain ⟨w, hwc, hws, hw0, hw1⟩ :=
    exists_continuous_cutoff_of_isClosedEmbedding τ T.subtype
      hT.isClosedEmbedding_subtypeVal K hK
  refine ⟨w, hwc, hws, hw0, ?_⟩
  intro x hx
  obtain ⟨t, ht, k, hk, rfl⟩ := hE hx
  exact hw1 ⟨t, ht⟩ k hk

/-- **Existence of a Bruhat section for a closed subgroup.**
A Bruhat section: given a closed subgroup `T` of a locally compact group
and a set `E` contained in `T * C` for compact `C`, there is a compactly
supported nonnegative measurable function `w` whose integral over each
`T`-translate meeting `E` equals `1`.

Use `exists_continuous_cutoff_of_subset_mul` when continuity or boundedness is
needed. These functions normalize subgroup integrals; they are not sections
of the quotient map. -/
theorem exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (T : Subgroup G) (hT : IsClosed (T : Set G))
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure]
    [τ.IsMulRightInvariant] {E C : Set G} (hC : IsCompact C)
    (hE : E ⊆ (T : Set G) * C) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x ∈ E, ∫ t : T, w ((t : G) * x) ∂τ = 1 := by
  obtain ⟨w, hwc, hws, hw0, hw1⟩ := exists_continuous_cutoff_of_subset_mul T hT τ hC hE
  exact ⟨w, hw0, hwc.measurable, hws, hw1⟩

end MeasureTheory
