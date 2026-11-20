/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.FKGeneralQInfiniteFKG
import Code.FK.InfiniteFiniteEnergy
import Code.FK.TwoPointPositiveFull
import Code.TwoDim.ZhangHarris

open MeasureTheory Set

namespace StatMech.FK

open StatMech.Lattice




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
