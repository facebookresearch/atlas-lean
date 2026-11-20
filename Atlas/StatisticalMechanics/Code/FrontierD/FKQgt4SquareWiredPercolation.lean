/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4SquareWiredPhaseTransport
import Code.FrontierD.FKQgt4SquareFaceDualPercolation
import Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Code.FK.TwoPointPositiveFull
import Code.TwoDim.ZhangHarris
import Code.Sharpness.PercoItems

open Filter MeasureTheory Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK
open StatMech.Percolation StatMech.Universality
open StatMech.FK.PeriodicPlanar

noncomputable section


theorem fci_faceDualConfig_shift
    (g : Multiplicative (Site 2))
    (omega : ConfigSpace (Sym2 (Site 2))) :
    fci_faceDualConfig (ConfigSpace.shift g omega) =
      ConfigSpace.shift g (fci_faceDualConfig omega) := by
  have hsmul (e : Sym2 (Site 2)) :
      g⁻¹ • e =
        Sym2.map (siteTranslate (Multiplicative.toAdd g⁻¹)) e := by
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [smul_sym2_mk, Sym2.map_mk]
        congr 1 <;> funext i <;>
          simp [smul_site_apply, siteTranslate, add_comm]
  funext e
  simp only [fci_faceDualConfig, ConfigSpace.shift_apply]
  rw [hsmul (fci_faceEdgeEquiv e), hsmul e,
    fci_faceEdgeEquiv_shift]

private def faceDualInfiniteAt (x : Site 2) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | (cluster 2 (fci_faceDualConfig omega) x).Infinite}

private theorem measurableSet_faceDualInfiniteAt (x : Site 2) :
    MeasurableSet (faceDualInfiniteAt x) := by
  exact (FK.measurableSet_clusterInfiniteEvent x).preimage
    fci_faceDualConfig_measurePreserving.measurable



theorem fkQgt4CriticalFree_faceDual_originInfinite_pos_of_ratePos
    {q : Real} (hq : 4 < q)
    (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
    let mu := ((FK.freeInfiniteVolume 2
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
    0 < mu.real (faceDualInfiniteAt (Percolation.origin 2)) := by
  dsimp only
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
  let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) ≤ q := by linarith
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  have hTI : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site 2)) mu := by
    simpa [mu, hp, hp1, hq0] using
      (FK.fkgqt_freeIV_isTranslationInvariant (d := 2) hp hp1 hq1)
  have hpre (x : Site 2) :
      (ConfigSpace.shift (TwoDim.zih_centerShift x)) ⁻¹'
          faceDualInfiniteAt (Percolation.origin 2) =
        faceDualInfiniteAt x := by
    ext omega
    change (cluster 2
        (fci_faceDualConfig
          (ConfigSpace.shift (TwoDim.zih_centerShift x) omega))
        (Percolation.origin 2)).Infinite ↔
      (cluster 2 (fci_faceDualConfig omega) x).Infinite
    rw [fci_faceDualConfig_shift]
    exact TwoDim.zih_cluster_shift_infinite_iff
      (fci_faceDualConfig omega) x
  have hmass (x : Site 2) :
      mu (faceDualInfiniteAt x) =
        mu (faceDualInfiniteAt (Percolation.origin 2)) := by
    rw [← hpre x]
    exact hTI.measure_preimage (TwoDim.zih_centerShift x)
      (measurableSet_faceDualInfiniteAt (Percolation.origin 2))
  have hglobal : mu {omega | ∃ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Infinite} = 1 := by
    simpa [mu, hp, hp1, hq0] using
      fkQgt4CriticalFree_faceDual_hasInfiniteCluster_of_ratePos hq hpos
  change 0 < mu.real (faceDualInfiniteAt (Percolation.origin 2))
  by_contra hnot
  have hrealZero : mu.real (faceDualInfiniteAt (Percolation.origin 2)) = 0 :=
    le_antisymm (not_lt.mp hnot) measureReal_nonneg
  have horiginZero : mu (faceDualInfiniteAt (Percolation.origin 2)) = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top mu _)).mp hrealZero
  have hallZero : ∀ x : Site 2, mu (faceDualInfiniteAt x) = 0 := by
    intro x
    rw [hmass x, horiginZero]
  have hglobalZero : mu {omega | ∃ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Infinite} = 0 := by
    have hevent : {omega | ∃ x : Site 2,
        (cluster 2 (fci_faceDualConfig omega) x).Infinite} =
        ⋃ x : Site 2, faceDualInfiniteAt x := by
      ext omega
      simp [faceDualInfiniteAt]
    rw [hevent]
    exact measure_iUnion_null hallZero
  rw [hglobal] at hglobalZero
  exact one_ne_zero hglobalZero




theorem fkQgt4CriticalFree_faceDual_originInfinite_pos_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    let mu := ((FK.freeInfiniteVolume 2
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
    0 < mu.real (faceDualInfiniteAt (Percolation.origin 2)) := by
  dsimp only
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
  let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) ≤ q := by linarith
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  have hTI : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site 2)) mu := by
    simpa [mu, hp, hp1, hq0] using
      (FK.fkgqt_freeIV_isTranslationInvariant (d := 2) hp hp1 hq1)
  have hpre (x : Site 2) :
      (ConfigSpace.shift (TwoDim.zih_centerShift x)) ⁻¹'
          faceDualInfiniteAt (Percolation.origin 2) =
        faceDualInfiniteAt x := by
    ext omega
    change (cluster 2
        (fci_faceDualConfig
          (ConfigSpace.shift (TwoDim.zih_centerShift x) omega))
        (Percolation.origin 2)).Infinite ↔
      (cluster 2 (fci_faceDualConfig omega) x).Infinite
    rw [fci_faceDualConfig_shift]
    exact TwoDim.zih_cluster_shift_infinite_iff
      (fci_faceDualConfig omega) x
  have hmass (x : Site 2) :
      mu (faceDualInfiniteAt x) =
        mu (faceDualInfiniteAt (Percolation.origin 2)) := by
    rw [← hpre x]
    exact hTI.measure_preimage (TwoDim.zih_centerShift x)
      (measurableSet_faceDualInfiniteAt (Percolation.origin 2))
  have hglobal : mu {omega | ∃ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Infinite} = 1 := by
    simpa [mu, hp, hp1, hq0] using
      fkQgt4CriticalFree_faceDual_hasInfiniteCluster_of_winding hq hwind
  change 0 < mu.real (faceDualInfiniteAt (Percolation.origin 2))
  by_contra hnot
  have hrealZero : mu.real (faceDualInfiniteAt (Percolation.origin 2)) = 0 :=
    le_antisymm (not_lt.mp hnot) measureReal_nonneg
  have horiginZero : mu (faceDualInfiniteAt (Percolation.origin 2)) = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top mu _)).mp hrealZero
  have hallZero : ∀ x : Site 2, mu (faceDualInfiniteAt x) = 0 := by
    intro x
    rw [hmass x, horiginZero]
  have hglobalZero : mu {omega | ∃ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Infinite} = 0 := by
    have hevent : {omega | ∃ x : Site 2,
        (cluster 2 (fci_faceDualConfig omega) x).Infinite} =
        ⋃ x : Site 2, faceDualInfiniteAt x := by
      ext omega
      simp [faceDualInfiniteAt]
    rw [hevent]
    exact measure_iUnion_null hallZero
  rw [hglobal] at hglobalZero
  exact one_ne_zero hglobalZero



theorem fkQgt4CriticalWired_percolation_pos_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    let mu := ((FK.wiredInfiniteVolume 2
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
    0 < mu.real (Percolation.percolationEvent 2) := by
  dsimp only
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
  let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) ≤ q := by linarith
  let muFree : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  let muWired : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.wiredInfiniteVolume 2 hp hp1 hq0
  let c : Real := muFree.real (faceDualInfiniteAt (Percolation.origin 2))
  have hc : 0 < c := by
    simpa [c, muFree, hp, hp1, hq0] using
      fkQgt4CriticalFree_faceDual_originInfinite_pos_of_winding hq hwind
  have hbound : ∀ N : Nat, 1 ≤ N →
      c ≤ muWired.real (FK.boxBdryConnEvent 2 N) := by
    intro N hN
    let x : FK.boxVerts 2 N := IsingFK.boxOrigin 2 N
    let A := fkSquareActiveConnToBoundaryEvent N x
    have hsubset : faceDualInfiniteAt (Percolation.origin 2) ⊆
        fkSquareFaceDualInnerEvent N A := by
      intro omega hinfinite
      rw [fkSquare_faceDualInnerEvent_connToBoundary]
      have hcross : fci_faceDualConfig omega ∈ crossingEvent 2 (N + 1) :=
        Sharpness.percolationEvent_subset_crossingEvent (N + 1) hinfinite
      have hbox := FK.crossingEvent_succ_subset_boxBdryConnEvent
        (d := 2) N hN hcross
      simpa [FK.boxBdryConnEvent, x] using hbox
    have hleft : c ≤ muFree.real (fkSquareFaceDualInnerEvent N A) :=
      measureReal_mono hsubset
    have hdom := criticalFree_faceDual_cylinder_le_wired N hq1
      (fkSquareActiveConnToBoundaryEvent_isIncreasing N x)
    have hevent :
        FK.boxRestrict 2 N ⁻¹'
            (restrictActive (FK.boxGraph 2 N) ⁻¹' A) =
          FK.boxBdryConnEvent 2 N := by
      rw [fkSquare_activeConnToBoundary_cylinder]
      rfl
    change muFree.real (fkSquareFaceDualInnerEvent N A) ≤
      muWired.real
        (FK.boxRestrict 2 N ⁻¹'
          (restrictActive (FK.boxGraph 2 N) ⁻¹' A)) at hdom
    rw [hevent] at hdom
    exact hleft.trans hdom
  have htend := FK.boxBdryConnEvent_real_tendsto_percolation
    (d := 2) muWired
  have hlimit : c ≤ muWired.real (Percolation.percolationEvent 2) := by
    apply ge_of_tendsto htend
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact hbound N hN
  change 0 < muWired.real (Percolation.percolationEvent 2)
  exact hc.trans_le hlimit



theorem fkQgt4CriticalWired_percolation_pos_of_ratePos
    {q : Real} (hq : 4 < q)
    (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
    let mu := ((FK.wiredInfiniteVolume 2
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
    0 < mu.real (Percolation.percolationEvent 2) := by
  dsimp only
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
  let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) ≤ q := by linarith
  let muFree : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  let muWired : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.wiredInfiniteVolume 2 hp hp1 hq0
  let c : Real := muFree.real (faceDualInfiniteAt (Percolation.origin 2))
  have hc : 0 < c := by
    simpa [c, muFree, hp, hp1, hq0] using
      fkQgt4CriticalFree_faceDual_originInfinite_pos_of_ratePos hq hpos
  have hbound : ∀ N : Nat, 1 ≤ N →
      c ≤ muWired.real (FK.boxBdryConnEvent 2 N) := by
    intro N hN
    let x : FK.boxVerts 2 N := IsingFK.boxOrigin 2 N
    let A := fkSquareActiveConnToBoundaryEvent N x
    have hsubset : faceDualInfiniteAt (Percolation.origin 2) ⊆
        fkSquareFaceDualInnerEvent N A := by
      intro omega hinfinite
      rw [fkSquare_faceDualInnerEvent_connToBoundary]
      have hcross : fci_faceDualConfig omega ∈ crossingEvent 2 (N + 1) :=
        Sharpness.percolationEvent_subset_crossingEvent (N + 1) hinfinite
      have hbox := FK.crossingEvent_succ_subset_boxBdryConnEvent
        (d := 2) N hN hcross
      simpa [FK.boxBdryConnEvent, x] using hbox
    have hleft : c ≤ muFree.real (fkSquareFaceDualInnerEvent N A) :=
      measureReal_mono hsubset
    have hdom := criticalFree_faceDual_cylinder_le_wired N hq1
      (fkSquareActiveConnToBoundaryEvent_isIncreasing N x)
    have hevent :
        FK.boxRestrict 2 N ⁻¹'
            (restrictActive (FK.boxGraph 2 N) ⁻¹' A) =
          FK.boxBdryConnEvent 2 N := by
      rw [fkSquare_activeConnToBoundary_cylinder]
      rfl
    change muFree.real (fkSquareFaceDualInnerEvent N A) ≤
      muWired.real
        (FK.boxRestrict 2 N ⁻¹'
          (restrictActive (FK.boxGraph 2 N) ⁻¹' A)) at hdom
    rw [hevent] at hdom
    exact hleft.trans hdom
  have htend := FK.boxBdryConnEvent_real_tendsto_percolation
    (d := 2) muWired
  have hlimit : c ≤ muWired.real (Percolation.percolationEvent 2) := by
    apply ge_of_tendsto htend
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact hbound N hN
  change 0 < muWired.real (Percolation.percolationEvent 2)
  exact hc.trans_le hlimit



theorem fkQgt4_firstOrder_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    FK.IsFirstOrderTransition 2
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) := by
  have hxi : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
    linarith [fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_winding hq hwind]
  have hresult := fkQgt4_discontinuity_of_winding_and_positive_order hq hxi
    (fkQgt4CriticalFreeDiagonalRate_tendsto_unconditional hq)
    (fkQgt4CriticalWired_percolation_pos_of_winding hq hwind) hwind
  exact hresult.1

end

end StatMech.FrontierD
