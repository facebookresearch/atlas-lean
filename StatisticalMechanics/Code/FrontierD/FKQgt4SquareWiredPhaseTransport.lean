/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKQgt4SquareDualInfiniteDomination
import Code.FrontierD.FKQgt4SquareFaceDualFrame
import Code.FrontierD.FKQgt4SquareInverseDualPercolation
import Code.FrontierB.CurrentContinuityBoxInfluence
import Code.IsingFK.PcUpperAllDimensions









open Filter Finset MeasureTheory Set SimpleGraph Topology

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK
open StatMech.Percolation StatMech.Universality
open StatMech.FK.PeriodicPlanar

noncomputable section



theorem freeInfinite_faceDual_le_wiredFinite
    {R N : Nat} (hRN : R ≤ N) (hN : 1 ≤ N)
    {q : Real} (hq : 1 ≤ q)
    {A : Set (ConfigSpace (FK.boxGraph 2 R).edgeSet)}
    (hA : IsIncreasing A) :
    ((FK.freeInfiniteVolume 2
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (fkSquareFaceDualInnerEvent R A) ≤
      (FK.wiredFiniteMeasure 2 N
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxRestrict 2 R ⁻¹'
          (restrictActive (FK.boxGraph 2 R) ⁻¹' A)) := by
  let hp := (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1
  let hp1 := (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2
  let hq0 := zero_lt_one.trans_le hq
  obtain ⟨phi, hphi, hconv⟩ := FK.freeInfiniteVolume_isLimit 2 hp hp1 hq0
  have hport := hconv.tendsto_real_of_isClopen
    (isClopen_fkSquareFaceDualInnerEvent R A)
  apply le_of_tendsto hport
  filter_upwards
    [hphi.tendsto_atTop.eventually (eventually_gt_atTop N)] with n hn
  exact freeFinite_faceDual_le_wiredFinite hRN hn hN hq hA



theorem fkSquare_openSub_extendActive_restrictActive
    (N : Nat) (eta : ConfigSpace (Sym2 (FK.boxVerts 2 N))) :
    openSub (FK.boxGraph 2 N)
        (extendActive (FK.boxGraph 2 N)
          (restrictActive (FK.boxGraph 2 N) eta)) =
      openSub (FK.boxGraph 2 N) eta := by
  ext u v
  by_cases huv : (FK.boxGraph 2 N).Adj u v
  · have he : s(u, v) ∈ (FK.boxGraph 2 N).edgeSet := by
      rwa [SimpleGraph.mem_edgeSet]
    simp [openSub_adj, huv, extendActive, restrictActive, he]
  · simp [openSub_adj, huv]



def fkSquareActiveConnToBoundaryEvent
    (N : Nat) (x : FK.boxVerts 2 N) :
    Set (ConfigSpace (FK.boxGraph 2 N).edgeSet) :=
  {rho | IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N)
    (extendActive (FK.boxGraph 2 N) rho) x}

theorem fkSquareActiveConnToBoundaryEvent_isIncreasing
    (N : Nat) (x : FK.boxVerts 2 N) :
    IsIncreasing (fkSquareActiveConnToBoundaryEvent N x) := by
  intro rho eta hrho hmem
  obtain ⟨y, hy, hreach⟩ := hmem
  refine ⟨y, hy, hreach.mono ?_⟩
  apply openSub_mono
  intro e
  by_cases he : e ∈ (FK.boxGraph 2 N).edgeSet
  · simpa [extendActive, he] using hrho ⟨e, he⟩
  · simp [extendActive, he]



theorem fkSquare_activeConnToBoundary_cylinder
    (N : Nat) (x : FK.boxVerts 2 N) :
    FK.boxRestrict 2 N ⁻¹'
        (restrictActive (FK.boxGraph 2 N) ⁻¹'
          fkSquareActiveConnToBoundaryEvent N x) =
      {omega : ConfigSpace (Sym2 (Site 2)) |
        IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N)
          (FK.boxRestrict 2 N omega) x} := by
  ext omega
  change IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N)
      (extendActive (FK.boxGraph 2 N)
        (restrictActive (FK.boxGraph 2 N) (FK.boxRestrict 2 N omega))) x ↔
    IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N)
      (FK.boxRestrict 2 N omega) x
  unfold IsingFK.ConnToBdry FK.Connected
  rw [fkSquare_openSub_extendActive_restrictActive]




theorem fkSquare_faceDualInnerEvent_connToBoundary
    (N : Nat) (x : FK.boxVerts 2 N) :
    fkSquareFaceDualInnerEvent N
        (fkSquareActiveConnToBoundaryEvent N x) =
      {omega : ConfigSpace (Sym2 (Site 2)) |
        IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N)
          (FK.boxRestrict 2 N (fci_faceDualConfig omega)) x} := by
  ext omega
  change IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N)
      (extendActive (FK.boxGraph 2 N)
        (fkSquareFaceDualInnerActive N omega)) x ↔ _
  have hactive : fkSquareFaceDualInnerActive N omega =
      restrictActive (FK.boxGraph 2 N)
        (FK.boxRestrict 2 N (fci_faceDualConfig omega)) := by
    rfl
  rw [hactive]
  unfold IsingFK.ConnToBdry FK.Connected
  rw [fkSquare_openSub_extendActive_restrictActive]
  rfl

end

end StatMech.FrontierD
