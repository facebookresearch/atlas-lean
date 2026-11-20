/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4SquareDualCoordinates
import Code.FK.FKGeneralQConsumer

open Filter Finset MeasureTheory Set SimpleGraph Topology

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK
open StatMech.Universality

noncomputable section



def fkSquareFaceDualInnerEvent (N : Nat)
    (A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  fkSquareFaceDualInnerActive N ⁻¹' A

theorem continuous_fkSquareFaceDualInnerActive (N : Nat) :
    Continuous (fkSquareFaceDualInnerActive N) := by
  apply continuous_pi
  intro a
  unfold fkSquareFaceDualInnerActive fci_faceDualConfig
  exact (continuous_of_discreteTopology : Continuous (fun b : Bool => !b)).comp
    (continuous_apply (fci_faceEdgeEquiv (FK.edgeIncl 2 N a.1)))

theorem isClopen_fkSquareFaceDualInnerEvent (N : Nat)
    (A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)) :
    IsClopen (fkSquareFaceDualInnerEvent N A) :=
  (isClopen_discrete A).preimage (continuous_fkSquareFaceDualInnerActive N)

theorem measurableSet_fkSquareFaceDualInnerEvent (N : Nat)
    (A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)) :
    MeasurableSet (fkSquareFaceDualInnerEvent N A) :=
  (isClopen_fkSquareFaceDualInnerEvent N A).isOpen.measurableSet



theorem freeFiniteMeasure_real_faceDualInnerEvent_eq_pfd
    {N m : Nat} (hNm : N < m) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hself : dualParam p q = p)
    (A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)) :
    (FK.freeFiniteMeasure 2 m hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (fkSquareFaceDualInnerEvent N A) =
      ∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
        A.indicator (fun _ => (1 : Real))
            (fkSquareDualInnerActiveRestrict hNm
              (fkSquarePfdSupport m omega)) *
          pfdDualProb (fkSquareBoxPlanar m) p q omega := by
  have hmeas := measurableSet_fkSquareFaceDualInnerEvent N A
  unfold FK.freeFiniteMeasure Measure.real
  simp only [ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply (FK.measurable_extendEdge 2 m) hmeas,
    FK.fkPMF_toMeasure_toReal 2 m hp hp1 hq]
  apply Finset.sum_congr rfl
  intro omega _
  rw [fkSquareBox_fkProb_duality m omega hp hp1 hq, hself]
  rw [fkSquareDualInnerActiveRestrict_pfdSupport_eq_faceDual hNm]
  rfl



theorem activeBCMean_wired_eq_wiredFiniteMeasure
    (N : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)) :
    activeBCMean (FK.boxGraph 2 N)
        (boundaryCliqueGraph (FK.boxBoundary 2 N)) (fun _ => p) q
        (A.indicator fun _ => (1 : Real)) =
      (FK.wiredFiniteMeasure 2 N hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxRestrict 2 N ⁻¹'
          (restrictActive (FK.boxGraph 2 N) ⁻¹' A)) := by
  rw [activeBCMean_boundaryClique_eq_wired
    (FK.boxGraph 2 N) (FK.boxBoundary 2 N) hp hp1 hq]
  rw [FK.fkgq_wiredFiniteMeasure_real_boxRestrictEvent
    N hp hp1 hq (restrictActive (FK.boxGraph 2 N) ⁻¹' A)
    ((FK.continuous_boxRestrict 2 N).measurable MeasurableSet.of_discrete)]
  rfl



theorem freeFinite_faceDual_le_wiredFinite
    {R N m : Nat} (hRN : R ≤ N) (hNm : N < m) (hN : 1 ≤ N)
    {q : Real} (hq : 1 ≤ q)
    {A : Set (ConfigSpace (FK.boxGraph 2 R).edgeSet)}
    (hA : IsIncreasing A) :
    (FK.freeFiniteMeasure 2 m
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (fkSquareFaceDualInnerEvent R A) ≤
      (FK.wiredFiniteMeasure 2 N
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxRestrict 2 R ⁻¹'
          (restrictActive (FK.boxGraph 2 R) ⁻¹' A)) := by
  let p := selfDualPoint q
  let hq0 : (0 : Real) < q := zero_lt_one.trans_le hq
  let AN : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet) :=
    fkSquareActiveRestrictLE hRN ⁻¹' A
  have hAN : IsIncreasing AN := by
    intro rho eta hrho hmem
    exact hA (fkSquareActiveRestrictLE_monotone hRN hrho) hmem
  have hdom := fkSquare_pfdDual_inner_dominated_wired hNm hN
    (selfDualPoint_mem_Ioo hq0).1 (selfDualPoint_mem_Ioo hq0).2 hq hAN
  rw [← freeFiniteMeasure_real_faceDualInnerEvent_eq_pfd
      hNm
      (selfDualPoint_mem_Ioo hq0).1 (selfDualPoint_mem_Ioo hq0).2 hq0
      (selfDualPoint_is_fixed hq0) AN] at hdom
  have hleft : fkSquareFaceDualInnerEvent N AN =
      fkSquareFaceDualInnerEvent R A := by
    ext omega
    simp only [fkSquareFaceDualInnerEvent, AN, Set.mem_preimage]
    rw [fkSquareActiveRestrictLE_faceDual]
  rw [hleft] at hdom
  rw [activeBCMean_wired_eq_wiredFiniteMeasure N
      (selfDualPoint_mem_Ioo hq0).1 (selfDualPoint_mem_Ioo hq0).2 hq0 AN] at hdom
  have hevent :
      FK.boxRestrict 2 N ⁻¹'
          (restrictActive (FK.boxGraph 2 N) ⁻¹' AN) =
        FK.boxRestrict 2 R ⁻¹'
          (restrictActive (FK.boxGraph 2 R) ⁻¹' A) := by
    ext omega
    simp only [Set.mem_preimage, AN]
    rw [fkSquareActiveRestrictLE_restrictActive hRN,
      FK.boxRestrictLE_boxRestrict]
  rwa [hevent] at hdom



set_option maxHeartbeats 800000 in

theorem criticalFree_faceDual_cylinder_le_wired
    (R : Nat) {q : Real} (hq : 1 ≤ q)
    {A : Set (ConfigSpace (FK.boxGraph 2 R).edgeSet)}
    (hA : IsIncreasing A) :
    (FK.freeInfiniteVolume 2
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (fkSquareFaceDualInnerEvent R A) ≤
      (FK.wiredInfiniteVolume 2
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxRestrict 2 R ⁻¹'
          (restrictActive (FK.boxGraph 2 R) ⁻¹' A)) := by
  let hq0 : (0 : Real) < q := zero_lt_one.trans_le hq
  let hp : 0 < selfDualPoint q := (selfDualPoint_mem_Ioo hq0).1
  let hp1 : selfDualPoint q < 1 := (selfDualPoint_mem_Ioo hq0).2
  let S : Set (ConfigSpace (Sym2 (FK.boxVerts 2 R))) :=
    restrictActive (FK.boxGraph 2 R) ⁻¹' A
  have hS : IsIncreasing S := by
    intro eta rho heta hmem
    exact hA (fun e => heta e.1) hmem
  obtain ⟨phi, hphi, hfree⟩ :=
    FK.freeInfiniteVolume_isLimit 2 hp hp1 hq0
  have hfreeEvent := hfree.tendsto_real_of_isClopen
    (isClopen_fkSquareFaceDualInnerEvent R A)
  have hfiniteBound : ∀ N : Nat, R ≤ N → 1 ≤ N →
      (FK.freeInfiniteVolume 2 hp hp1 hq0 :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (fkSquareFaceDualInnerEvent R A) ≤
        (FK.wiredFiniteMeasure 2 N hp hp1 hq0 :
          Measure (ConfigSpace (Sym2 (Site 2)))).real
            (FK.boxRestrict 2 R ⁻¹' S) := by
    intro N hRN hN
    refine le_of_tendsto hfreeEvent ?_
    filter_upwards
        [hphi.tendsto_atTop.eventually (eventually_gt_atTop N)] with k hk
    exact freeFinite_faceDual_le_wiredFinite hRN hk hN hq hA
  have hwired := FK.fkgq_wired_infinite_measure
    (d := 2) R hp hp1 hq hS
  refine ge_of_tendsto hwired ?_
  filter_upwards [eventually_ge_atTop R, eventually_ge_atTop 1] with N hRN hN
  exact hfiniteBound N hRN hN

end

end StatMech.FrontierD
