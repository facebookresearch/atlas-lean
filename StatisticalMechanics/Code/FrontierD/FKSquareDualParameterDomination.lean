/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKQgt4SquarePeriodicExchange










open Filter Finset MeasureTheory Set SimpleGraph Topology

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK
open StatMech.Universality

noncomputable section


theorem freeFinite_faceDual_le_wiredFinite_dualParam
    {R N m : Nat} (hRN : R ≤ N) (hNm : N < m) (hN : 1 ≤ N)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (FK.boxGraph 2 R).edgeSet)}
    (hA : IsIncreasing A) :
    (FK.freeFiniteMeasure 2 m hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (fkSquareFaceDualInnerEvent R A) ≤
      (FK.wiredFiniteMeasure 2 N
        (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
        (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxRestrict 2 R ⁻¹'
          (restrictActive (FK.boxGraph 2 R) ⁻¹' A)) := by
  let hq0 : (0 : Real) < q := zero_lt_one.trans_le hq
  let pDual := dualParam p q
  let hpDual : 0 < pDual := dualParam_pos hp hp1 hq0
  let hpDual1 : pDual < 1 := dualParam_lt_one hp hp1 hq0
  let AN : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet) :=
    fkSquareActiveRestrictLE hRN ⁻¹' A
  have hAN : IsIncreasing AN := by
    intro rho eta hrho hmem
    exact hA (fkSquareActiveRestrictLE_monotone hRN hrho) hmem
  have hdom := fkSquare_lumped_inner_dominated_wired hNm hN
    hpDual hpDual1 hq hAN
  rw [← fkSquare_freeFiniteMeasure_real_faceDualInnerEvent_eq_lumpedDual
      hNm hp hp1 hq0 AN] at hdom
  have hleft : fkSquareFaceDualInnerEvent N AN =
      fkSquareFaceDualInnerEvent R A := by
    ext omega
    simp only [fkSquareFaceDualInnerEvent, AN, Set.mem_preimage]
    rw [fkSquareActiveRestrictLE_faceDual]
  rw [hleft] at hdom
  rw [activeBCMean_wired_eq_wiredFiniteMeasure N
      hpDual hpDual1 hq0 AN] at hdom
  have hevent :
      FK.boxRestrict 2 N ⁻¹'
          (restrictActive (FK.boxGraph 2 N) ⁻¹' AN) =
        FK.boxRestrict 2 R ⁻¹'
          (restrictActive (FK.boxGraph 2 R) ⁻¹' A) := by
    ext omega
    simp only [Set.mem_preimage, AN]
    rw [fkSquareActiveRestrictLE_restrictActive hRN,
      FK.boxRestrictLE_boxRestrict]
  simpa [pDual, hpDual, hpDual1, hq0, hevent] using hdom



set_option maxHeartbeats 800000 in

theorem freeInfinite_faceDual_cylinder_le_wired_dualParam
    (R : Nat) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (FK.boxGraph 2 R).edgeSet)}
    (hA : IsIncreasing A) :
    (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (fkSquareFaceDualInnerEvent R A) ≤
      (FK.wiredInfiniteVolume 2
        (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
        (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxRestrict 2 R ⁻¹'
          (restrictActive (FK.boxGraph 2 R) ⁻¹' A)) := by
  let hq0 : (0 : Real) < q := zero_lt_one.trans_le hq
  let pDual := dualParam p q
  let hpDual : 0 < pDual := dualParam_pos hp hp1 hq0
  let hpDual1 : pDual < 1 := dualParam_lt_one hp hp1 hq0
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
        (FK.wiredFiniteMeasure 2 N hpDual hpDual1 hq0 :
          Measure (ConfigSpace (Sym2 (Site 2)))).real
            (FK.boxRestrict 2 R ⁻¹' S) := by
    intro N hRN hN
    refine le_of_tendsto hfreeEvent ?_
    filter_upwards
        [hphi.tendsto_atTop.eventually (eventually_gt_atTop N)] with m hm
    exact freeFinite_faceDual_le_wiredFinite_dualParam
      hRN hm hN hp hp1 hq hA
  have hwired := FK.fkgq_wired_infinite_measure
    (d := 2) R hpDual hpDual1 hq hS
  refine ge_of_tendsto hwired ?_
  filter_upwards [eventually_ge_atTop R, eventually_ge_atTop 1] with N hRN hN
  exact hfiniteBound N hRN hN

end

end StatMech.FrontierD
