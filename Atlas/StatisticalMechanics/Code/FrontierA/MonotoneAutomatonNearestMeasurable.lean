/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.MonotoneAutomatonNearestTransport

open MeasureTheory Set
open scoped ENNReal

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem measurableSet_pairHighConnected (x y : Site d) :
    MeasurableSet {omega : PairSiteConfig d | y ∈ pairHighCluster omega x} := by
  exact (measurable_siteToBond.comp measurable_pairSiteRight)
    (measurableSet_connected x y)


theorem measurableSet_pairLowInfinite (x : Site d) :
    MeasurableSet {omega : PairSiteConfig d | x ∈ pairLowInfiniteVertices omega} := by
  exact (measurable_siteToBond.comp measurable_pairSiteLeft)
    (measurableSet_clusterInfinite x)


theorem measurableSet_pairHighInfinite (x : Site d) :
    MeasurableSet {omega : PairSiteConfig d |
      (pairHighCluster omega x).Infinite} := by
  exact (measurable_siteToBond.comp measurable_pairSiteRight)
    (measurableSet_clusterInfinite x)


def pairNearestComparisonEvent (x y z x' y' : Site d) :
    Set (PairSiteConfig d) :=
  if l1dist d y z ≤ l1dist d x' y' then Set.univ
  else {omega | x' ∉ pairHighCluster omega x} ∪
    {omega | y' ∉ pairLowInfiniteVertices omega}

theorem measurableSet_pairNearestComparisonEvent
    (x y z x' y' : Site d) :
    MeasurableSet (pairNearestComparisonEvent x y z x' y') := by
  unfold pairNearestComparisonEvent
  split
  · exact MeasurableSet.univ
  · exact (measurableSet_pairHighConnected x x').compl.union
      (measurableSet_pairLowInfinite y').compl


theorem measurableSet_pairNearestHighSet (x y : Site d) :
    MeasurableSet {omega : PairSiteConfig d | y ∈ pairNearestHighSet omega x} := by
  have heq : {omega : PairSiteConfig d | y ∈ pairNearestHighSet omega x} =
      {omega | y ∈ pairHighCluster omega x} ∩
        ⋃ z : Site d, {omega | z ∈ pairLowInfiniteVertices omega} ∩
          ⋂ x' : Site d, ⋂ y' : Site d,
            pairNearestComparisonEvent x y z x' y' := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_setOf_eq, pairNearestHighSet, mem_nearestSourceSet_iff]
    constructor
    · rintro ⟨hy, z, hz, hmin⟩
      refine ⟨hy, z, hz, ?_⟩
      intro x' y'
      unfold pairNearestComparisonEvent
      by_cases hle : l1dist d y z ≤ l1dist d x' y'
      · simp [hle]
      · simp only [hle, if_false, Set.mem_union, Set.mem_setOf_eq]
        by_cases hx' : x' ∈ pairHighCluster omega x
        · right
          intro hy'
          exact hle (hmin x' hx' y' hy')
        · exact Or.inl hx'
    · rintro ⟨hy, z, hz, hall⟩
      refine ⟨hy, z, hz, ?_⟩
      intro x' hx' y' hy'
      have h := hall x' y'
      unfold pairNearestComparisonEvent at h
      by_cases hle : l1dist d y z ≤ l1dist d x' y'
      · exact hle
      · simp only [hle, if_false, Set.mem_union, Set.mem_setOf_eq] at h
        exact (h.elim (fun h => h hx') (fun h => h hy')).elim
  rw [heq]
  exact (measurableSet_pairHighConnected x y).inter
    (MeasurableSet.iUnion fun z =>
      (measurableSet_pairLowInfinite z).inter
        (MeasurableSet.iInter fun x' => MeasurableSet.iInter fun y' =>
          measurableSet_pairNearestComparisonEvent x y z x' y'))


theorem measurable_encard_setOf_countable {Omega alpha : Type*}
    [MeasurableSpace Omega] [Countable alpha]
    (p : Omega → alpha → Prop)
    (hp : ∀ a, Measurable (fun omega => p omega a)) :
    Measurable (fun omega => Set.encard {a | p omega a}) := by
  have hset : Measurable (fun omega => {a | p omega a}) := by
    exact measurable_setOf.comp (measurable_pi_lambda _ hp)
  exact measurable_encard.comp hset


theorem measurable_pairNearestHighSet_encard (x : Site d) :
    Measurable (fun omega : PairSiteConfig d =>
      (pairNearestHighSet omega x).encard) := by
  apply measurable_encard_setOf_countable
  intro y
  exact measurable_mem.mpr (measurableSet_pairNearestHighSet x y)


theorem measurable_pairNearestHighSet_ncard (x : Site d) :
    Measurable (fun omega : PairSiteConfig d =>
      (pairNearestHighSet omega x).ncard) := by
  have hset : Measurable (fun omega : PairSiteConfig d =>
      pairNearestHighSet omega x) := by
    exact measurable_setOf.comp (measurable_pi_lambda _ fun y =>
      measurable_mem.mpr (measurableSet_pairNearestHighSet x y))
  exact measurable_ncard.comp hset


theorem measurableSet_pairNearestHighSet_finite (x : Site d) :
    MeasurableSet {omega : PairSiteConfig d |
      (pairNearestHighSet omega x).Finite} := by
  have heq : {omega : PairSiteConfig d |
      (pairNearestHighSet omega x).Finite} =
      {omega | (pairNearestHighSet omega x).encard ≠ ⊤} := by
    ext omega
    exact Set.encard_ne_top_iff.symm
  rw [heq]
  change MeasurableSet
    ((fun omega : PairSiteConfig d => (pairNearestHighSet omega x).encard) ⁻¹'
      {n : ℕ∞ | n ≠ ⊤})
  exact (measurable_pairNearestHighSet_encard x)
    (MeasurableSet.of_discrete)


theorem measurableSet_pairNearestHighFinset (x y : Site d) :
    MeasurableSet {omega : PairSiteConfig d |
      y ∈ pairNearestHighFinset omega x} := by
  have heq : {omega : PairSiteConfig d | y ∈ pairNearestHighFinset omega x} =
      {omega | (pairNearestHighSet omega x).Finite} ∩
        {omega | y ∈ pairNearestHighSet omega x} := by
    ext omega
    exact mem_nearestSourceFinset_iff_finite
  rw [heq]
  exact (measurableSet_pairNearestHighSet_finite x).inter
    (measurableSet_pairNearestHighSet x y)


theorem measurable_pairNearestHighFinset_card (x : Site d) :
    Measurable (fun omega : PairSiteConfig d =>
      (pairNearestHighFinset omega x).card) := by
  have heq : (fun omega : PairSiteConfig d =>
      (pairNearestHighFinset omega x).card) =
      fun omega => (pairNearestHighSet omega x).ncard := by
    funext omega
    exact nearestSourceFinset_card _ _
  rw [heq]
  exact measurable_pairNearestHighSet_ncard x


theorem measurable_pairNearestTransport (x y : Site d) :
    Measurable (pairNearestTransport x y : PairSiteConfig d → ℝ≥0∞) := by
  classical
  have hval : Measurable (fun omega : PairSiteConfig d =>
      (((pairNearestHighFinset omega x).card : ℝ≥0∞)⁻¹)) := by
    have hcast : Measurable (fun n : ℕ => ((n : ℝ≥0∞)⁻¹)) :=
      Measurable.of_discrete
    exact hcast.comp (measurable_pairNearestHighFinset_card x)
  have hself : ∀ omega : PairSiteConfig d, x ∈ pairHighCluster omega x :=
    fun omega => self_mem_cluster _ x
  have hite : Measurable (fun omega : PairSiteConfig d =>
      if y ∈ pairNearestHighFinset omega x then
        (((pairNearestHighFinset omega x).card : ℝ≥0∞)⁻¹) else 0) :=
    Measurable.ite (measurableSet_pairNearestHighFinset x y) hval measurable_const
  convert hite using 1
  funext omega
  unfold pairNearestTransport finiteTargetTransport
  simp [hself omega]

end StatMech.FrontierA
