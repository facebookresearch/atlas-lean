/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.ExteriorConnected
import Code.Walls.kc2_core

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice










theorem kc3_leftRegion_eq_oddRay {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    jec_leftRegion Vc = {z : Site 2 | ¬ Even (jec_rayCount z Vc)} := rfl




theorem kc3_mem_leftRegion_iff_oddRay {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) : z ∈ jec_leftRegion Vc ↔ ¬ Even (jec_rayCount z Vc) :=
  jec_mem_leftRegion Vc z




theorem kc3_evenRay_iff_not_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) : Even (jec_rayCount z Vc) ↔ z ∉ jec_leftRegion Vc := by
  rw [kc3_mem_leftRegion_iff_oddRay]; exact (not_not).symm








theorem kc3_mem_orbitLeftRegion_iff_oddRay (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2) :
    z ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) :=
  jec_mem_leftRegion (mpl_orbitLoop K a) z










def kc3_LeftRegionSupportSubset (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  jec_leftRegion (mpl_orbitLoop K a) ∩ {z | z ∈ (mpl_orbitLoop K a).support} ⊆ K








theorem kc3_supportOddInK_iff_leftRegion_subset {K : Set (Site 2)}
    {a : {e : Dart // IsBoundaryDart K e}} :
    exc_SupportOddInK K a ↔ kc3_LeftRegionSupportSubset K a := by
  unfold exc_SupportOddInK kc3_LeftRegionSupportSubset
  constructor
  · intro h z hz
    obtain ⟨hzL, hzs⟩ := hz
    rw [jec_mem_leftRegion] at hzL
    exact h z hzs hzL
  · intro h z hzs hodd
    exact h ⟨(jec_mem_leftRegion _ z).mpr hodd, hzs⟩




theorem kc3_supportOddInK_of_leftRegion_subset {K : Set (Site 2)}
    {a : {e : Dart // IsBoundaryDart K e}} (h : kc3_LeftRegionSupportSubset K a) :
    exc_SupportOddInK K a :=
  kc3_supportOddInK_iff_leftRegion_subset.mpr h











theorem kc3_leftRegion_subset_of_three {K : Set (Site 2)}
    {a : {e : Dart // IsBoundaryDart K e}}
    (hdown : kc2_DownFaceEven K a) (hup : kc2_UpFaceInK K a) (hleft : kc2_LeftFaceInK K a) :
    kc3_LeftRegionSupportSubset K a :=
  kc3_supportOddInK_iff_leftRegion_subset.mp (kc2_supportOddInK_of_three hdown hup hleft)





theorem kc3_leftRegion_subset_iff_three {K : Set (Site 2)}
    {a : {e : Dart // IsBoundaryDart K e}} :
    kc3_LeftRegionSupportSubset K a ↔
      (kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a) :=
  kc3_supportOddInK_iff_leftRegion_subset.symm.trans kc2_core_iff_three










theorem kc3_unitCell_leftRegion_subset :
    kc3_LeftRegionSupportSubset unitCell ucBase :=
  kc3_supportOddInK_iff_leftRegion_subset.mp kc2_unitCell_core

end Walls

end StatMech
