/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneEscape

/-!
# Merging infinite clusters inside a half-plane

For finite source sets placed by a suitable translation, the probability that two of their
vertices lie in infinite clusters that are not connected inside a half-plane is small.

## i. Overview

`halfPlanePairMergeErrorUnion r L R` is the event that some `x ∈ L` and `y ∈ R` both lie in
infinite clusters but are not connected inside `H_r = {x ≥ r}`. Translating the sources far to the
right turns the half-plane into a large region around them, so this error is bounded by the
whole-plane merge error inside a buffered box (`PeriodicGraph.pairMergeErrorUnion`), which tends
to zero when the infinite cluster is almost surely unique.

Headline fidelity: the translation bounds are unconditional apart from translation invariance;
`exists_shift_halfPlanePairMergeErrorUnion_measureReal_lt` is conditional on translation
invariance and almost sure uniqueness of the infinite cluster.

## ii. Key results

- `PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion`
- `PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_lt`
- `PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_with_margin`

## iii. Table of contents

- A. The half-plane merge error
- B. Comparison with the whole-plane merge error

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. The half-plane merge error -/

/-- Half-plane merge error for finite source sets: some `x ∈ L` and `y ∈ R` lie in infinite open
clusters but are not connected within `H_r`. -/
def PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion
    (E : PeriodicPlaneEmbedding P) (r : ℝ) (L R : Finset V) :
    Set (ConfigSpace (Sym2 V)) :=
  ⋃ x ∈ L, ⋃ y ∈ R, E.halfPlanePairMergeError r x y

lemma PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : ℝ) (L R : Finset V) :
    MeasurableSet (E.halfPlanePairMergeErrorUnion r L R) :=
  MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
      E.halfPlanePairMergeError_measurableSet r x y

/-! ## B. Comparison with the whole-plane merge error -/

omit [Countable V] in
/-- After a suitable translation of the sources, the half-plane merge error pulls back into the
whole-plane merge error in the buffered box of radius `N`. -/
lemma PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_preimage_subset
    (E : PeriodicPlaneEmbedding P) (N : ℕ) (r : ℝ)
    (L R : Finset V) :
    ∃ z : Site 2,
      P.configTranslate z ⁻¹'
          E.halfPlanePairMergeErrorUnion r
            (L.image (P.shift z)) (R.image (P.shift z)) ⊆
        P.pairMergeErrorUnion L R N := by
  obtain ⟨z, htransport⟩ :=
    E.exists_shift_connectedWithinOrbit_into_rightHalfPlane N r
  refine ⟨z, ?_⟩
  intro omega herror
  change P.configTranslate z omega ∈
    E.halfPlanePairMergeErrorUnion r
      (L.image (P.shift z)) (R.image (P.shift z)) at herror
  rw [PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion] at herror
  obtain ⟨xz, hxz⟩ := Set.mem_iUnion.mp herror
  obtain ⟨hxzL, hxz⟩ := Set.mem_iUnion.mp hxz
  obtain ⟨yz, hyz⟩ := Set.mem_iUnion.mp hxz
  obtain ⟨hyzR, hpair⟩ := Set.mem_iUnion.mp hyz
  obtain ⟨x, hxL, rfl⟩ := Finset.mem_image.mp hxzL
  obtain ⟨y, hyR, rfl⟩ := Finset.mem_image.mp hyzR
  rw [PeriodicGraph.pairMergeErrorUnion]
  apply Set.mem_iUnion.2
  refine ⟨x, Set.mem_iUnion.2 ⟨hxL, ?_⟩⟩
  apply Set.mem_iUnion.2
  refine ⟨y, Set.mem_iUnion.2 ⟨hyR, ?_⟩⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (P.cluster_infinite_configTranslate z omega x).mp hpair.1.1
  · exact (P.cluster_infinite_configTranslate z omega y).mp hpair.1.2
  · intro hmerge
    exact hpair.2 (htransport omega x y hmerge)

lemma PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (N : ℕ) (r : ℝ)
    (L R : Finset V) :
    ∃ z : Site 2,
      mu.real (E.halfPlanePairMergeErrorUnion r
        (L.image (P.shift z)) (R.image (P.shift z))) ≤
        mu.real (P.pairMergeErrorUnion L R N) := by
  obtain ⟨z, hsub⟩ :=
    E.exists_shift_halfPlanePairMergeErrorUnion_preimage_subset N r L R
  refine ⟨z, ?_⟩
  let A := E.halfPlanePairMergeErrorUnion r
    (L.image (P.shift z)) (R.image (P.shift z))
  have hmeasure := P.translateEvent_measure_eq mu hTI z
    (E.halfPlanePairMergeErrorUnion_measurableSet r
      (L.image (P.shift z)) (R.image (P.shift z)))
  have hreal : mu.real (P.configTranslate z ⁻¹' A) = mu.real A :=
    congrArg ENNReal.toReal hmeasure
  rw [← hreal]
  exact measureReal_mono hsub

/-- Under translation invariance and almost sure uniqueness, a suitable translate of the sources
has half-plane merge error below `ε`. -/
theorem PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_lt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : ℝ) (L R : Finset V) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Site 2,
      mu.real (E.halfPlanePairMergeErrorUnion r
        (L.image (P.shift z)) (R.image (P.shift z))) < ε := by
  have ht := P.pairMergeErrorUnion_real_tendsto_zero mu hunique L R
  have hev := (tendsto_order.1 ht).2 ε hε
  obtain ⟨N, hN⟩ := hev.exists
  obtain ⟨z, hz⟩ :=
    E.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le
      mu hTI N r L R
  exact ⟨z, hz.trans_lt hN⟩

/-- Translation bound that also places the translated sources in `H_r`. This is the case `R = r`
of `exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_with_margin`. -/
lemma PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_with_sources
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (N : Nat) (r : Real)
    (L R : Finset V)
    (hLR : ∀ v ∈ L ∪ R, v ∈ P.orbitBox (P.bufferedRadius N)) :
    ∃ z : Site 2,
      (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices r ∧
      (R.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices r ∧
      mu.real (E.halfPlanePairMergeErrorUnion r
        (L.image (P.shift z)) (R.image (P.shift z))) ≤
        mu.real (P.pairMergeErrorUnion L R N) := by
  obtain ⟨z, hz⟩ :=
    E.exists_shift_orbitBox_subset_rightHalfPlane (P.bufferedRadius N) r
  have htransport : ∀ (omega : ConfigSpace (Sym2 V)) (x y : V),
      omega ∈ P.connectedWithinOrbit x y N →
        P.configTranslate z omega ∈
          P.connectedWithinSet (E.rightHalfPlaneVertices r)
            (P.shift z x) (P.shift z y) := by
    intro omega x y hxy
    have hsub : P.shift z '' (P.orbitBox (P.bufferedRadius N) : Set V) ⊆
        E.rightHalfPlaneVertices r := by
      rintro v ⟨u, hu, rfl⟩
      exact hz u hu
    apply P.connectedWithinSet_mono_region hsub (P.shift z x) (P.shift z y)
    apply (P.connectedWithinSet_configTranslate z omega
      (P.orbitBox (P.bufferedRadius N) : Set V) x y).2
    exact hxy
  have hpre : P.configTranslate z ⁻¹'
      E.halfPlanePairMergeErrorUnion r
        (L.image (P.shift z)) (R.image (P.shift z)) ⊆
      P.pairMergeErrorUnion L R N := by
    intro omega herror
    change P.configTranslate z omega ∈
      E.halfPlanePairMergeErrorUnion r
        (L.image (P.shift z)) (R.image (P.shift z)) at herror
    rw [PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion] at herror
    obtain ⟨xz, hxz⟩ := Set.mem_iUnion.mp herror
    obtain ⟨hxzL, hxz⟩ := Set.mem_iUnion.mp hxz
    obtain ⟨yz, hyz⟩ := Set.mem_iUnion.mp hxz
    obtain ⟨hyzR, hpair⟩ := Set.mem_iUnion.mp hyz
    obtain ⟨x, hxL, rfl⟩ := Finset.mem_image.mp hxzL
    obtain ⟨y, hyR, rfl⟩ := Finset.mem_image.mp hyzR
    rw [PeriodicGraph.pairMergeErrorUnion]
    apply Set.mem_iUnion.2
    refine ⟨x, Set.mem_iUnion.2 ⟨hxL, ?_⟩⟩
    apply Set.mem_iUnion.2
    refine ⟨y, Set.mem_iUnion.2 ⟨hyR, ?_⟩⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (P.cluster_infinite_configTranslate z omega x).mp hpair.1.1
    · exact (P.cluster_infinite_configTranslate z omega y).mp hpair.1.2
    · intro hmerge
      exact hpair.2 (htransport omega x y hmerge)
  refine ⟨z, ?_, ?_, ?_⟩
  · intro w hw
    change w ∈ L.image (P.shift z) at hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact hz v (hLR v (Finset.mem_union_left R hv))
  · intro w hw
    change w ∈ R.image (P.shift z) at hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact hz v (hLR v (Finset.mem_union_right L hv))
  · let A := E.halfPlanePairMergeErrorUnion r
      (L.image (P.shift z)) (R.image (P.shift z))
    have hmeasure := P.translateEvent_measure_eq mu hTI z
      (E.halfPlanePairMergeErrorUnion_measurableSet r
        (L.image (P.shift z)) (R.image (P.shift z)))
    have hreal : mu.real (P.configTranslate z ⁻¹' A) = mu.real A :=
      congrArg ENNReal.toReal hmeasure
    rw [← hreal]
    exact measureReal_mono hpre

/-- Translation bound that places the translated sources in `H_R` for a given `R ≥ r` while the
merge error is measured in `H_r`. -/
lemma PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_with_margin
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (N : Nat) {r R : Real}
    (hrR : r ≤ R) (L Rset : Finset V)
    (hLR : ∀ v ∈ L ∪ Rset, v ∈ P.orbitBox (P.bufferedRadius N)) :
    ∃ z : Site 2,
      (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      (Rset.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      mu.real (E.halfPlanePairMergeErrorUnion r
        (L.image (P.shift z)) (Rset.image (P.shift z))) ≤
        mu.real (P.pairMergeErrorUnion L Rset N) := by
  obtain ⟨z, hz⟩ :=
    E.exists_shift_orbitBox_subset_rightHalfPlane (P.bufferedRadius N) R
  have htransport : ∀ (omega : ConfigSpace (Sym2 V)) (x y : V),
      omega ∈ P.connectedWithinOrbit x y N →
        P.configTranslate z omega ∈
          P.connectedWithinSet (E.rightHalfPlaneVertices r)
            (P.shift z x) (P.shift z y) := by
    intro omega x y hxy
    have hsub : P.shift z '' (P.orbitBox (P.bufferedRadius N) : Set V) ⊆
        E.rightHalfPlaneVertices r := by
      rintro v ⟨u, hu, rfl⟩
      exact hrR.trans (hz u hu)
    apply P.connectedWithinSet_mono_region hsub (P.shift z x) (P.shift z y)
    apply (P.connectedWithinSet_configTranslate z omega
      (P.orbitBox (P.bufferedRadius N) : Set V) x y).2
    exact hxy
  have hpre : P.configTranslate z ⁻¹'
      E.halfPlanePairMergeErrorUnion r
        (L.image (P.shift z)) (Rset.image (P.shift z)) ⊆
      P.pairMergeErrorUnion L Rset N := by
    intro omega herror
    change P.configTranslate z omega ∈
      E.halfPlanePairMergeErrorUnion r
        (L.image (P.shift z)) (Rset.image (P.shift z)) at herror
    rw [PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion] at herror
    obtain ⟨xz, hxz⟩ := Set.mem_iUnion.mp herror
    obtain ⟨hxzL, hxz⟩ := Set.mem_iUnion.mp hxz
    obtain ⟨yz, hyz⟩ := Set.mem_iUnion.mp hxz
    obtain ⟨hyzR, hpair⟩ := Set.mem_iUnion.mp hyz
    obtain ⟨x, hxL, rfl⟩ := Finset.mem_image.mp hxzL
    obtain ⟨y, hyR, rfl⟩ := Finset.mem_image.mp hyzR
    rw [PeriodicGraph.pairMergeErrorUnion]
    apply Set.mem_iUnion.2
    refine ⟨x, Set.mem_iUnion.2 ⟨hxL, ?_⟩⟩
    apply Set.mem_iUnion.2
    refine ⟨y, Set.mem_iUnion.2 ⟨hyR, ?_⟩⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (P.cluster_infinite_configTranslate z omega x).mp hpair.1.1
    · exact (P.cluster_infinite_configTranslate z omega y).mp hpair.1.2
    · intro hmerge
      exact hpair.2 (htransport omega x y hmerge)
  refine ⟨z, ?_, ?_, ?_⟩
  · intro w hw
    change w ∈ L.image (P.shift z) at hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact hz v (hLR v (Finset.mem_union_left Rset hv))
  · intro w hw
    change w ∈ Rset.image (P.shift z) at hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact hz v (hLR v (Finset.mem_union_right L hv))
  · let A := E.halfPlanePairMergeErrorUnion r
      (L.image (P.shift z)) (Rset.image (P.shift z))
    have hmeasure := P.translateEvent_measure_eq mu hTI z
      (E.halfPlanePairMergeErrorUnion_measurableSet r
        (L.image (P.shift z)) (Rset.image (P.shift z)))
    have hreal : mu.real (P.configTranslate z ⁻¹' A) = mu.real A :=
      congrArg ENNReal.toReal hmeasure
    rw [← hreal]
    exact measureReal_mono hpre

end StatMech.FK.PeriodicPlanar
