/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.MonotoneAutomatonNearestMeasurable

open MeasureTheory Set

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


def pairFiniteNearestAt (y : Site d) : Set (PairSiteConfig d) :=
  {omega | (pairHighCluster omega y).Infinite ∧
    (pairLowInfiniteVertices omega).Nonempty ∧
    (pairNearestHighSet omega y).Finite ∧
    y ∈ pairNearestHighSet omega y}


theorem measurableSet_pairLowInfiniteVertices_nonempty :
    MeasurableSet {omega : PairSiteConfig d |
      (pairLowInfiniteVertices omega).Nonempty} := by
  have heq : {omega : PairSiteConfig d |
      (pairLowInfiniteVertices omega).Nonempty} =
      ⋃ x : Site d, {omega | x ∈ pairLowInfiniteVertices omega} := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact Set.nonempty_def
  rw [heq]
  exact MeasurableSet.iUnion measurableSet_pairLowInfinite


theorem measurableSet_pairFiniteNearestAt (y : Site d) :
    MeasurableSet (pairFiniteNearestAt y) := by
  exact (measurableSet_pairHighInfinite y).inter
    (measurableSet_pairLowInfiniteVertices_nonempty.inter
      ((measurableSet_pairNearestHighSet_finite y).inter
        (measurableSet_pairNearestHighSet y y)))


theorem pairFiniteNearestAt_origin_measure_zero
    (mu : Measure (PairSiteConfig d)) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
    mu (pairFiniteNearestAt (0 : Site d)) = 0 := by
  apply lattice_mass_transport_forbidden_event_null mu hinv
    (pairNearestTransport (d := d)) measurable_pairNearestTransport
    pairNearestTransport_diagonallyInvariant
    (fun omega => pairNearestTransport_outgoing_le_one omega 0)
  intro omega homega
  exact pairNearestTransport_incoming_eq_top omega homega.1 homega.2.1
    homega.2.2.1 homega.2.2.2


theorem pairFiniteNearestAt_shift (g : Multiplicative (Site d))
    (omega : PairSiteConfig d) (x : Site d) :
    StatMech.ConfigSpace.shift g omega ∈ pairFiniteNearestAt (g • x) ↔
      omega ∈ pairFiniteNearestAt x := by
  unfold pairFiniteNearestAt
  simp only [Set.mem_setOf_eq]
  rw [pairHighCluster_shift, pairLowInfiniteVertices_shift,
    pairNearestHighSet_shift]
  have hinj : Function.Injective (fun z : Site d => g • z) := smul_injective g
  change ((fun z : Site d => g • z) '' pairHighCluster omega x).Infinite ∧
      ((fun z : Site d => g • z) '' pairLowInfiniteVertices omega).Nonempty ∧
      ((fun z : Site d => g • z) '' pairNearestHighSet omega x).Finite ∧
      g • x ∈ (fun z : Site d => g • z) '' pairNearestHighSet omega x ↔ _
  rw [Set.infinite_image_iff (Set.injOn_of_injective hinj),
    Set.image_nonempty,
    Set.finite_image_iff (Set.injOn_of_injective hinj)]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨hhigh, hlow, hfin, y, hy, hxy⟩
    exact ⟨hhigh, hlow, hfin, (hinj hxy) ▸ hy⟩
  · rintro ⟨hhigh, hlow, hfin, hx⟩
    exact ⟨hhigh, hlow, hfin, x, hx, rfl⟩


theorem pairFiniteNearestAt_measure_zero
    (mu : Measure (PairSiteConfig d)) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (y : Site d) :
    mu (pairFiniteNearestAt y) = 0 := by
  let g : Multiplicative (Site d) := Multiplicative.ofAdd y
  have hgy : g • (0 : Site d) = y := by
    change y + 0 = y
    simp
  have hpre :
      (StatMech.ConfigSpace.shift g : PairSiteConfig d → PairSiteConfig d) ⁻¹'
        pairFiniteNearestAt y = pairFiniteNearestAt (0 : Site d) := by
    ext omega
    change StatMech.ConfigSpace.shift g omega ∈ pairFiniteNearestAt y ↔
      omega ∈ pairFiniteNearestAt (0 : Site d)
    rw [← hgy]
    exact pairFiniteNearestAt_shift g omega 0
  calc
    mu (pairFiniteNearestAt y) =
        mu ((StatMech.ConfigSpace.shift g : PairSiteConfig d → PairSiteConfig d) ⁻¹'
          pairFiniteNearestAt y) :=
      (hinv.measure_preimage g (measurableSet_pairFiniteNearestAt y)).symm
    _ = mu (pairFiniteNearestAt (0 : Site d)) := by rw [hpre]
    _ = 0 := pairFiniteNearestAt_origin_measure_zero mu hinv



def pairHasFiniteNearestHighCluster : Set (PairSiteConfig d) :=
  {omega | (pairLowInfiniteVertices omega).Nonempty ∧
    ∃ x : Site d, (pairHighCluster omega x).Infinite ∧
      (pairNearestHighSet omega x).Finite}



theorem pairHasFiniteNearestHighCluster_subset :
    pairHasFiniteNearestHighCluster (d := d) ⊆
      ⋃ y : Site d, pairFiniteNearestAt y := by
  intro omega homega
  rcases homega with ⟨hlow, x, hhigh, hfin⟩
  obtain ⟨y, hy⟩ := pairNearestHighSet_nonempty omega x hlow
  have hyCluster : y ∈ pairHighCluster omega x :=
    pairNearestHighSet_subset_cluster omega x hy
  have hcluster : pairHighCluster omega y = pairHighCluster omega x :=
    pairHighCluster_eq_of_mem hyCluster
  have hnearest : pairNearestHighSet omega y = pairNearestHighSet omega x :=
    pairNearestHighSet_eq_of_mem hyCluster
  rw [Set.mem_iUnion]
  refine ⟨y, ?_⟩
  exact ⟨hcluster.symm ▸ hhigh, hlow, hnearest.symm ▸ hfin,
    hnearest.symm ▸ hy⟩




theorem pairHasFiniteNearestHighCluster_measure_zero
    (mu : Measure (PairSiteConfig d)) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
    mu (pairHasFiniteNearestHighCluster (d := d)) = 0 := by
  apply measure_mono_null pairHasFiniteNearestHighCluster_subset
  apply measure_iUnion_null
  exact pairFiniteNearestAt_measure_zero mu hinv


theorem interpolatedHighPair_no_finite_nearest
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hinv : IsTripleFieldTranslationInvariant mu) :
    (interpolatedHighPairLaw T mu)
      (pairHasFiniteNearestHighCluster (d := d)) = 0 := by
  letI : IsProbabilityMeasure (interpolatedHighPairLaw T mu) := by
    unfold interpolatedHighPairLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_interpolatedHighPair T).aemeasurable
  exact pairHasFiniteNearestHighCluster_measure_zero
    (interpolatedHighPairLaw T mu)
    (interpolatedHighPairLaw_isTranslationInvariant T mu hinv)

end StatMech.FrontierA
