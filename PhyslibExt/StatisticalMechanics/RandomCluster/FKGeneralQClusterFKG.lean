/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.FKGeneralQInfiniteFKG
public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteFiniteEnergy
public import PhyslibExt.StatisticalMechanics.RandomCluster.TwoPointConnectivity
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ZhangHarris

/-!
# Positive correlation of infinite clusters in the planar free FK measure

For `q ≥ 1` the events "`x` lies in an infinite cluster" and "`y` lies in an infinite cluster" are
positively correlated under the free infinite-volume random-cluster measure on `ℤ²`.

## i. Overview

Each event `{x ↔ ∞}` is the decreasing intersection of the increasing events "the cluster of `x`
leaves the box of radius `n`", each of which depends on finitely many edges. The finite-volume FKG
inequality for the free measure applies to every stage, and continuity of measure along decreasing
intersections passes it to the limit.
The headline `fkgq_freeInfiniteVolume_clusterInfinite_fkg` is proved unconditionally (only
`0 < p < 1` and `1 ≤ q`).

## ii. Key results

- `fkgq_freeInfiniteVolume_clusterInfinite_fkg` : `P(x ↔ ∞) P(y ↔ ∞) ≤ P(x ↔ ∞, y ↔ ∞)` for the
  free infinite-volume measure on `ℤ²`.

## iii. Table of contents

- A. FKG for infinite-cluster events

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 4.
-/

@[expose] public section

open MeasureTheory Set

namespace StatMech.FK

open StatMech.Lattice

/-! ## A. FKG for infinite-cluster events -/

/-- Harris–FKG inequality for the infinite-cluster events of two sites under the free
infinite-volume random-cluster measure on `ℤ²` with `q ≥ 1`. -/
theorem fkgq_freeInfiniteVolume_clusterInfinite_fkg
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (x y : Site 2) :
    let mu := (freeInfiniteVolume 2 hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2))))
    mu.real (clusterInfiniteEvent 2 x) *
        mu.real (clusterInfiniteEvent 2 y) <=
      mu.real (clusterInfiniteEvent 2 x ∩ clusterInfiniteEvent 2 y) := by
  classical
  let mu := (freeInfiniteVolume 2 hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2))))
  let A : Nat -> Set (ConfigSpace (Sym2 (Site 2))) :=
    TwoDim.zih_clusterApprox x
  let B : Nat -> Set (ConfigSpace (Sym2 (Site 2))) :=
    TwoDim.zih_clusterApprox y
  have hstage : forall n, mu.real (A n) * mu.real (B n) <=
      mu.real (A n ∩ B n) := by
    intro n
    let F := TwoDim.zih_clusterSupport x n
    let G := TwoDim.zih_clusterSupport y n
    let K := F ∪ G
    have hAK : StatMech.DependsOn (A n)
        (K : Set (Sym2 (Site 2))) :=
      (TwoDim.zih_clusterApprox_dependsOn x n).mono (by
        intro e he
        exact Finset.mem_union_left G he)
    have hBK : StatMech.DependsOn (B n)
        (K : Set (Sym2 (Site 2))) :=
      (TwoDim.zih_clusterApprox_dependsOn y n).mono (by
        intro e he
        exact Finset.mem_union_right F he)
    obtain ⟨N, t, ht⟩ := cdc_finset_in_box K
    have hrange : ∀ e ∈ K, e ∈ Set.range (edgeIncl 2 N) := by
      intro e he
      rw [ht] at he
      obtain ⟨eb, _, heb⟩ := Finset.mem_image.mp he
      exact ⟨eb, heb⟩
    apply fkgq_freeInfiniteVolume_fkg_of_dependsOn N hp hp1 hq
    · exact hAK.mono hrange
    · exact hBK.mono hrange
    · exact TwoDim.zih_clusterApprox_isIncreasing x n
    · exact TwoDim.zih_clusterApprox_isIncreasing y n
  have hlim := StatMech.ih_harris_iInter_of_antitone mu A B
    (TwoDim.zih_clusterApprox_antitone x)
    (TwoDim.zih_clusterApprox_antitone y)
    (TwoDim.zih_clusterApprox_measurableSet x)
    (TwoDim.zih_clusterApprox_measurableSet y) hstage
  rw [<- TwoDim.zih_clusterInfinite_eq_iInter x,
    <- TwoDim.zih_clusterInfinite_eq_iInter y] at hlim
  exact hlim

end StatMech.FK
