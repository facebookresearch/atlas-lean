/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexBrickDualInfiniteDomination
import Code.FK.TriangularSharpnessCritical





open Filter Finset MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC
open StatMech.OSSS

noncomputable section



def triangularBoxActiveRestrictLE {n m : Nat} (hnm : n ≤ m)
    (rho : ConfigSpace (triangularBoxGraph m).edgeSet) :
    ConfigSpace (triangularBoxGraph n).edgeSet :=
  restrictConfig (triangularBoxEdgeLE hnm) rho

theorem monotone_triangularBoxActiveRestrictLE {n m : Nat} (hnm : n ≤ m) :
    Monotone (triangularBoxActiveRestrictLE hnm) := by
  intro rho eta hrho e
  exact hrho (triangularBoxEdgeLE hnm e)



theorem triHexFaceDualInnerActive_restrictLE {n m : Nat} (hnm : n ≤ m)
    (omega : ConfigSpace (Sym2 HexVertex)) :
    triangularBoxActiveRestrictLE hnm
        (triHexFaceDualInnerActive m omega) =
      triHexFaceDualInnerActive n omega := by
  funext e
  unfold triangularBoxActiveRestrictLE restrictConfig
  unfold triHexFaceDualInnerActive
  apply congrArg (fun b : Bool => !b)
  apply congrArg omega
  apply congrArg triHexFullDualEdgeEquiv
  change edgeIncl 2 m (innerEdgeLE 2 hnm e.1) = edgeIncl 2 n e.1
  exact edgeIncl_innerEdgeLE 2 hnm e.1


def triangularBoxLiftEvent {n m : Nat} (hnm : n ≤ m)
    (A : Set (ConfigSpace (triangularBoxGraph n).edgeSet)) :
    Set (ConfigSpace (triangularBoxGraph m).edgeSet) :=
  triangularBoxActiveRestrictLE hnm ⁻¹' A

theorem triangularBoxLiftEvent_increasing {n m : Nat} (hnm : n ≤ m)
    {A : Set (ConfigSpace (triangularBoxGraph n).edgeSet)}
    (hA : IsIncreasing A) : IsIncreasing (triangularBoxLiftEvent hnm A) := by
  intro rho eta hrho hmem
  exact hA (monotone_triangularBoxActiveRestrictLE hnm hrho) hmem

theorem triHexFaceDualInnerEvent_lift {n m : Nat} (hnm : n ≤ m)
    (A : Set (ConfigSpace (triangularBoxGraph n).edgeSet)) :
    triHexFaceDualInnerEvent m (triangularBoxLiftEvent hnm A) =
      triHexFaceDualInnerEvent n A := by
  ext omega
  change triangularBoxActiveRestrictLE hnm
      (triHexFaceDualInnerActive m omega) ∈ A ↔
    triHexFaceDualInnerActive n omega ∈ A
  rw [triHexFaceDualInnerActive_restrictLE]



def triangularBoxBufferedActiveRestrict (k m : Nat)
    (hkm : 2 * k ≤ triangular.bufferedRadius m)
    (rho : ConfigSpace (triangular.bufferedGraph m).edgeSet) :
    ConfigSpace (triangularBoxGraph (2 * k)).edgeSet :=
  ocd_innerRestrictActive (triangularBoxGraph (2 * k))
    (triangular.bufferedGraph m) (triangularBoxToBufferedAt k m hkm)
    (triangularBoxToBufferedAt_adjMatch k m hkm) rho

theorem monotone_triangularBoxBufferedActiveRestrict (k m : Nat)
    (hkm : 2 * k ≤ triangular.bufferedRadius m) :
    Monotone (triangularBoxBufferedActiveRestrict k m hkm) := by
  intro rho eta hrho e
  exact hrho _



def triangularBufferedBoxActiveEvent (k m : Nat)
    (hkm : 2 * k ≤ triangular.bufferedRadius m)
    (A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)) :
    Set (ConfigSpace (triangular.bufferedGraph m).edgeSet) :=
  triangularBoxBufferedActiveRestrict k m hkm ⁻¹' A

theorem triangularBufferedBoxActiveEvent_increasing (k m : Nat)
    (hkm : 2 * k ≤ triangular.bufferedRadius m)
    {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
    (hA : IsIncreasing A) :
    IsIncreasing (triangularBufferedBoxActiveEvent k m hkm A) := by
  intro rho eta hrho hmem
  exact hA (monotone_triangularBoxBufferedActiveRestrict k m hkm hrho) hmem



def triangularBufferedBoxEvent (k : Nat)
    (A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)) :
    Set (ConfigSpace (Sym2 (triangular.BufferedVertex (2 * k)))) :=
  {rho | triangularBoxBufferedActiveRestrict k (2 * k)
      ((triangular.id_le_bufferedRadius (2 * k)))
      (restrictActive (triangular.bufferedGraph (2 * k)) rho) ∈ A}

theorem triangularBufferedBoxEvent_increasing (k : Nat)
    {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
    (hA : IsIncreasing A) : IsIncreasing (triangularBufferedBoxEvent k A) := by
  intro rho eta hrho hmem
  apply hA _ hmem
  intro e
  exact hrho _



theorem triangularBoxBufferedActiveRestrict_bufferedRestrictLE
    (k m : Nat) (hkm : 2 * k ≤ m)
    (rho : ConfigSpace (Sym2 (triangular.BufferedVertex m))) :
    triangularBoxBufferedActiveRestrict k (2 * k)
        (triangular.id_le_bufferedRadius (2 * k))
        (restrictActive (triangular.bufferedGraph (2 * k))
          (triangular.bufferedRestrictLE hkm rho)) =
      triangularBoxBufferedActiveRestrict k m
        ((triangular.id_le_bufferedRadius (2 * k)).trans
          (triangular.bufferedRadius_strictMono.monotone hkm))
        (restrictActive (triangular.bufferedGraph m) rho) := by
  let hrad : 2 * k ≤ triangular.bufferedRadius m :=
    (triangular.id_le_bufferedRadius (2 * k)).trans
      (triangular.bufferedRadius_strictMono.monotone hkm)
  let incl := triangularBoxToBufferedAt k m hrad
  have hcomp :
      ocd_innerRestrict (triangularBoxToBuffered k)
          (triangular.bufferedRestrictLE hkm rho) =
        ocd_innerRestrict incl rho := by
    funext e
    have hv : ∀ x : TriangularBoxVertex (2 * k),
        triangular.bufferedVertexInclLE hkm
            (triangularBoxToBuffered k x) = incl x := by
      intro x
      apply Subtype.ext
      rfl
    induction e using Sym2.inductionOn with
    | _ x y =>
        change rho s(triangular.bufferedVertexInclLE hkm
              (triangularBoxToBuffered k x),
            triangular.bufferedVertexInclLE hkm
              (triangularBoxToBuffered k y)) =
          rho s(incl x, incl y)
        rw [hv x, hv y]
  unfold triangularBoxBufferedActiveRestrict
  rw [ocd_innerRestrictActive_restrictActive,
    ocd_innerRestrictActive_restrictActive]
  exact congrArg (restrictActive (triangularBoxGraph (2 * k))) hcomp

theorem triangularBufferedBoxEvent_preimage_restrictActive
    (k m : Nat) (hkm : 2 * k ≤ m)
    (A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)) :
    triangular.bufferedRestrictLE hkm ⁻¹'
        triangularBufferedBoxEvent k A =
      restrictActive (triangular.bufferedGraph m) ⁻¹'
        triangularBufferedBoxActiveEvent k m
          ((triangular.id_le_bufferedRadius (2 * k)).trans
            (triangular.bufferedRadius_strictMono.monotone hkm)) A := by
  ext rho
  change triangularBoxBufferedActiveRestrict k (2 * k)
      (triangular.id_le_bufferedRadius (2 * k))
      (restrictActive (triangular.bufferedGraph (2 * k))
        (triangular.bufferedRestrictLE hkm rho)) ∈ A ↔
    triangularBoxBufferedActiveRestrict k m
      ((triangular.id_le_bufferedRadius (2 * k)).trans
        (triangular.bufferedRadius_strictMono.monotone hkm))
      (restrictActive (triangular.bufferedGraph m) rho) ∈ A
  rw [triangularBoxBufferedActiveRestrict_bufferedRestrictLE]



theorem triangularBufferedBoxEvent_centeredShell_eq (k : Nat) :
    triangularBufferedBoxEvent k
        (triangularCenteredShellEvent (2 * k) k) =
      triangularBufferedInnerShellEvent k := by
  ext rho
  have hincl : triangularBoxToBufferedAt k (2 * k)
      (triangular.id_le_bufferedRadius (2 * k)) =
        triangularBoxToBuffered k := by
    funext x
    apply Subtype.ext
    rfl
  change triangularBoxBufferedActiveRestrict k (2 * k)
      (triangular.id_le_bufferedRadius (2 * k))
      (restrictActive (triangular.bufferedGraph (2 * k)) rho) ∈
        triangularCenteredShellEvent (2 * k) k ↔
    ocd_innerRestrict (triangularBoxToBuffered k) rho ∈
      triangularCenteredShellFullEvent (2 * k) k
  unfold triangularBoxBufferedActiveRestrict
  rw [ocd_innerRestrictActive_restrictActive, hincl]
  exact Set.ext_iff.mp
    (restrictActive_preimage_triangularCenteredShellEvent (2 * k) k) _




theorem triangularBoxRead_dualConfig_eq_triHexFaceDualInnerActive
    (k : Nat) (omega : ConfigSpace (Sym2 HexVertex)) :
    triangularBoxBufferedActiveRestrict k (2 * k)
        (triangular.id_le_bufferedRadius (2 * k))
        (restrictActive (triangular.bufferedGraph (2 * k))
          (triangular.bufferedRestrict (2 * k)
            ((dualConfigEquiv triHexFullDualEdgeEquiv).symm omega))) =
      triHexFaceDualInnerActive (2 * k) omega := by
  funext e
  unfold triangularBoxBufferedActiveRestrict
  unfold ocd_innerRestrictActive restrictActive ocd_innerEdge
  unfold PeriodicGraph.bufferedRestrict PeriodicGraph.edgeIncl
  unfold triHexFaceDualInnerActive
  simp only [dualConfigEquiv_symm_apply]
  apply congrArg (fun b : Bool => !b)
  apply congrArg omega
  apply congrArg triHexFullDualEdgeEquiv
  rw [Sym2.map_map]
  apply congrArg (fun f => Sym2.map f e.1)
  funext x
  rfl



theorem triHexFaceDualInnerShell_eq_dualConfig_preimage
    (k : Nat) :
    triHexFaceDualInnerEvent (2 * k)
        (triangularCenteredShellEvent (2 * k) k) =
      (dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹'
        triangular.bufferedCylinder (2 * k)
          (triangularBufferedInnerShellEvent k) := by
  ext omega
  rw [← triangularBufferedBoxEvent_centeredShell_eq k]
  change triHexFaceDualInnerActive (2 * k) omega ∈
      triangularCenteredShellEvent (2 * k) k ↔
    triangularBoxBufferedActiveRestrict k (2 * k)
      (triangular.id_le_bufferedRadius (2 * k))
      (restrictActive (triangular.bufferedGraph (2 * k))
        (triangular.bufferedRestrict (2 * k)
          ((dualConfigEquiv triHexFullDualEdgeEquiv).symm omega))) ∈
      triangularCenteredShellEvent (2 * k) k
  rw [triangularBoxRead_dualConfig_eq_triHexFaceDualInnerActive]



theorem triHex_dualPercolationEvent_subset_faceDualInnerShell
    (k : Nat) (hk : 1 ≤ k) :
    (dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹'
        triangular.percolationEvent ⊆
      triHexFaceDualInnerEvent (2 * k)
        (triangularCenteredShellEvent (2 * k) k) := by
  intro omega hperc
  have hshell := triangular_percolationEvent_subset_innerShell k hk hperc
  rw [← triangularBufferedBoxEvent_centeredShell_eq k] at hshell
  change triangularBoxBufferedActiveRestrict k (2 * k)
      (triangular.id_le_bufferedRadius (2 * k))
      (restrictActive (triangular.bufferedGraph (2 * k))
        (triangular.bufferedRestrict (2 * k)
          ((dualConfigEquiv triHexFullDualEdgeEquiv).symm omega))) ∈
    triangularCenteredShellEvent (2 * k) k at hshell
  rw [triangularBoxRead_dualConfig_eq_triHexFaceDualInnerActive] at hshell
  exact hshell




theorem triangularBufferedInnerShellCylinder_subset_rootBoundary
    (k n : Nat) (hnk : triangular.bufferedRadius n < k) :
    triangular.bufferedCylinder (2 * k)
        (triangularBufferedInnerShellEvent k) ⊆
      triangular.bufferedCylinder n
        (triangular.bufferedRootBoundaryEvent n) := by
  intro omega homega
  change triangular.bufferedRestrict (2 * k) omega ∈
    triangularBufferedInnerShellEvent k at homega
  change triangular.bufferedRestrict n omega ∈
    triangular.bufferedRootBoundaryEvent n
  change ocd_innerRestrict (triangularBoxToBuffered k)
      (triangular.bufferedRestrict (2 * k) omega) ∈
    triangularCenteredShellFullEvent (2 * k) k at homega
  obtain ⟨y, hyShell, hreach⟩ := homega
  let eta := ocd_innerRestrict (triangularBoxToBuffered k)
    (triangular.bufferedRestrict (2 * k) omega)
  let phi : FK.openSub (triangularBoxGraph (2 * k)) eta →g
      triangular.openSubgraph omega := {
    toFun := fun z => z.1
    map_rel' := by
      intro a b hab
      change triangularGraph.Adj a.1 b.1 ∧ eta s(a, b) = true at hab
      rw [PeriodicGraph.openSubgraph_adj]
      refine ⟨hab.1, ?_⟩
      simpa [eta, ocd_innerRestrict, ocd_innerEdge,
        triangularBoxToBuffered, PeriodicGraph.bufferedRestrict] using hab.2 }
  have hfull := hreach.map phi
  have hroot : phi (triangularBoxRoot (2 * k)) = triangular.root := by
    change (0 : Site 2) = triangular.root
    exact triangular_root_eq_zero.symm
  have hyOutside : y.1 ∉
      triangular.orbitBox (triangular.bufferedRadius n) := by
    rw [triangular_mem_orbitBox_iff_box]
    intro hy
    have hrad : triangular.bufferedRadius n ≤ k - 1 := by omega
    have hySmall : y.1 ∈ box 2 (k - 1) := box_mono 2 hrad hy
    have hyBoundary : y.1 ∈ vertexBoundary 2 k := by
      simpa only [triangularBoxShell, Finset.mem_filter, Finset.mem_univ,
        true_and] using hyShell
    have hyNotSmall : y.1 ∉ box 2 (k - 1) := by
      exact (mem_vertexBoundary.mp hyBoundary).2
    exact hyNotSmall hySmall
  obtain ⟨z, hzBoundary, hzReach⟩ :=
    triangular.bufferedBoundary_reachable_of_reachable_outside n omega
      (triangular.bufferedRoot n).2 hyOutside (by simpa [hroot] using hfull)
  exact ⟨z, hzBoundary, hzReach⟩



theorem triangularBoxBufferedActiveRestrict_comp_outerBox
    (k j M : Nat)
    (hkj : 2 * k ≤ triangular.bufferedRadius j)
    (hjM : triangular.bufferedRadius j ≤ 2 * M)
    (rho : ConfigSpace (triangularBoxGraph (2 * M)).edgeSet) :
    triangularBoxBufferedActiveRestrict k j hkj
        (ocd_innerRestrictActive (triangular.bufferedGraph j)
          (triangularBoxGraph (2 * M))
          (triangularBufferedToBox j M hjM)
          (triangularBufferedToBox_adjMatch j M hjM) rho) =
      triangularBoxActiveRestrictLE
        (hkj.trans hjM) rho := by
  funext e
  unfold triangularBoxBufferedActiveRestrict
  unfold triangularBoxActiveRestrictLE StatMech.OSSS.restrictConfig
  unfold ocd_innerRestrictActive ocd_innerEdge triangularBoxEdgeLE innerEdgeLE
  apply congrArg rho
  apply Subtype.ext
  change Sym2.map (triangularBufferedToBox j M hjM)
      (Sym2.map (triangularBoxToBufferedAt k j hkj) e.1) =
    Sym2.map (boxVertInclLE 2 (hkj.trans hjM)) e.1
  rw [Sym2.map_map]
  apply congrArg (fun f => Sym2.map f e.1)
  funext x
  apply Subtype.ext
  rfl




theorem hexagonalFreeInfinite_faceDual_le_triangularWiredBuffered
    (k j : Nat) (hkj : 2 * k ≤ j)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
    (hA : IsIncreasing A) :
    (hexagonal.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 HexVertex))).real
        (triHexFaceDualInnerEvent (2 * k) A) ≤
      (triangular.wiredBufferedMeasure j
          (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
          (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedBoxEvent k A)) := by
  classical
  let pd := dualParam p q
  let M := triangular.bufferedRadius j + 1
  have hrad : 2 * k ≤ triangular.bufferedRadius j :=
    hkj.trans (triangular.id_le_bufferedRadius j)
  have hjM : triangular.bufferedRadius j < M := by
    simp only [M, Nat.lt_add_one]
  have hj2M : triangular.bufferedRadius j ≤ 2 * M := by
    dsimp only [M]
    omega
  have hbox : 2 * k ≤ 2 * M := hrad.trans (by omega)
  have houter := hexagonalFreeInfinite_faceDual_le_wiredTriangularBox
    (N := 2 * M) (by omega) hp hp1 hq
    (triangularBoxLiftEvent_increasing hbox hA)
  rw [triHexFaceDualInnerEvent_lift hbox] at houter
  let incl := triangularBufferedToBox j M hj2M
  let Aj := triangularBufferedBoxActiveEvent k j hrad A
  have hAj : IsIncreasing Aj :=
    triangularBufferedBoxActiveEvent_increasing k j hrad hA
  have hdom := ocd_wired_inner_dominated_activeBCMean
    (triangular.bufferedGraph j) (triangularBoxGraph (2 * M)) incl
    (fun y => y ∈ triangularBoxShell (2 * M) (2 * M))
    (triangularBufferedToBox_injective j M hj2M)
    (triangularBufferedToBox_adjMatch j M hj2M)
    (triangular.bufferedBoundary j)
    (pfIn := fun _ => pd) (pfOut := fun _ => pd)
    (fun _ => rfl)
    (fun _ => dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
    (fun _ => dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
    (fun _ => dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
    (fun _ => dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
    hq (triangularBufferedToBox_inducedWiring_le j M hjM) hAj
  have houterToBuffer :
      activeBCMean (triangularBoxGraph (2 * M))
          (boundaryCliqueGraph
            (fun y => y ∈ triangularBoxShell (2 * M) (2 * M)))
          (fun _ => pd) q
          ((triangularBoxLiftEvent hbox A).indicator
            fun _ => (1 : Real)) ≤
        activeBCMean (triangular.bufferedGraph j)
          (boundaryCliqueGraph (triangular.bufferedBoundary j))
          (fun _ => pd) q (Aj.indicator fun _ => (1 : Real)) := by
    convert hdom using 1
    congr 1
    funext rho
    unfold Aj triangularBufferedBoxActiveEvent
    rw [Set.indicator_apply, Set.indicator_apply]
    have hcomp := triangularBoxBufferedActiveRestrict_comp_outerBox
      k j M hrad (by omega) rho
    simp only [Set.mem_preimage, triangularBoxLiftEvent]
    rw [hcomp]
  calc
    (hexagonal.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 HexVertex))).real
        (triHexFaceDualInnerEvent (2 * k) A) ≤
      activeBCMean (triangularBoxGraph (2 * M))
        (boundaryCliqueGraph
          (fun y => y ∈ triangularBoxShell (2 * M) (2 * M)))
        (fun _ => pd) q
        ((triangularBoxLiftEvent hbox A).indicator
          fun _ => (1 : Real)) := by
      simpa only [pd, triHexBrickInnerBoundary] using houter
    _ ≤ activeBCMean (triangular.bufferedGraph j)
        (boundaryCliqueGraph (triangular.bufferedBoundary j))
        (fun _ => pd) q (Aj.indicator fun _ => (1 : Real)) :=
      houterToBuffer
    _ = (triangular.wiredBufferedMeasure j
          (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
          (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedBoxEvent k A)) := by
      rw [triangular.wiredBufferedMeasure_real_cylinder hkj
        (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
        (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq)]
      rw [triangularBufferedBoxEvent_preimage_restrictActive]
      rw [activeBCMean_boundaryClique_eq_wired
        (triangular.bufferedGraph j) (triangular.bufferedBoundary j)
        (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
        (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq)]
      rfl




theorem triangularFreeBufferedBox_le_hexagonalFreeInfinite_faceDual
    (k j : Nat) (hkj : 2 * k ≤ j)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
    (hA : IsIncreasing A) :
    (triangular.freeBufferedMeasure j
        (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
        (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedBoxEvent k A)) ≤
      (hexagonal.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 HexVertex))).real
          (triHexFaceDualInnerEvent (2 * k) A) := by
  classical
  let pd := dualParam p q
  let M := triangular.bufferedRadius j + 1
  have hrad : 2 * k ≤ triangular.bufferedRadius j :=
    hkj.trans (triangular.id_le_bufferedRadius j)
  have hj2M : triangular.bufferedRadius j ≤ 2 * M := by
    dsimp only [M]
    omega
  have hbox : 2 * k ≤ 2 * M := hrad.trans (by omega)
  have houter := freeTriangularBox_le_hexagonalFreeInfinite_faceDual
    (N := 2 * M) hp hp1 hq
    (triangularBoxLiftEvent_increasing hbox hA)
  rw [triHexFaceDualInnerEvent_lift hbox] at houter
  let incl := triangularBufferedToBox j M hj2M
  let Aj := triangularBufferedBoxActiveEvent k j hrad A
  have hAj : IsIncreasing Aj :=
    triangularBufferedBoxActiveEvent_increasing k j hrad hA
  have hdom := ocd_free_inner_dominated_activeBCMean
    (triangular.bufferedGraph j) (triangularBoxGraph (2 * M)) incl
    (fun _ => False)
    (triangularBufferedToBox_injective j M hj2M)
    (triangularBufferedToBox_adjMatch j M hj2M)
    (pfIn := fun _ => pd) (pfOut := fun _ => pd)
    (fun _ => rfl)
    (fun _ => dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
    (fun _ => dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
    (fun _ => dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
    (fun _ => dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
    hq hAj
  have hbufferToOuter :
      activeBCMean (triangular.bufferedGraph j) ⊥
          (fun _ => pd) q (Aj.indicator fun _ => (1 : Real)) ≤
        activeBCMean (triangularBoxGraph (2 * M)) ⊥
          (fun _ => pd) q
          ((triangularBoxLiftEvent hbox A).indicator
            fun _ => (1 : Real)) := by
    have hfalse : boundaryCliqueGraph
        (fun _ : TriangularBoxVertex (2 * M) => False) = ⊥ := by
      ext x y
      simp [boundaryCliqueGraph_adj]
    have hdom' :
        activeBCMean (triangular.bufferedGraph j) ⊥
            (fun _ => pd) q (Aj.indicator fun _ => (1 : Real)) ≤
          activeBCMean (triangularBoxGraph (2 * M)) ⊥
            (fun _ => pd) q
            (fun rho => Aj.indicator (fun _ => (1 : Real))
              (ocd_innerRestrictActive
                (triangular.bufferedGraph j)
                (triangularBoxGraph (2 * M)) incl
                (triangularBufferedToBox_adjMatch j M hj2M) rho)) := by
      simpa only [hfalse] using hdom
    convert hdom' using 1
    congr 1
    funext rho
    unfold Aj triangularBufferedBoxActiveEvent
    rw [Set.indicator_apply, Set.indicator_apply]
    have hcomp := triangularBoxBufferedActiveRestrict_comp_outerBox
      k j M hrad hj2M rho
    simp only [Set.mem_preimage, triangularBoxLiftEvent]
    rw [hcomp]
  calc
    (triangular.freeBufferedMeasure j
        (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
        (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedBoxEvent k A)) =
      activeBCMean (triangular.bufferedGraph j) ⊥
        (fun _ => pd) q (Aj.indicator fun _ => (1 : Real)) := by
      rw [triangular.freeBufferedMeasure_real_cylinder hkj
        (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
        (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq)]
      rw [triangularBufferedBoxEvent_preimage_restrictActive]
      rw [activeBCMean_eq_bcProb_lift
        (triangular.bufferedGraph j) ⊥
        (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
        (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq)]
      simp only [bcProb_bot_eq_fkProb]
      rfl
    _ ≤ activeBCMean (triangularBoxGraph (2 * M)) ⊥
        (fun _ => pd) q
        ((triangularBoxLiftEvent hbox A).indicator
          fun _ => (1 : Real)) := hbufferToOuter
    _ ≤ (hexagonal.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 HexVertex))).real
          (triHexFaceDualInnerEvent (2 * k) A) := by
      simpa only [pd] using houter

set_option maxHeartbeats 800000 in



theorem triangularFreeInfinite_le_hexagonalFreeInfinite_faceDual
    (k : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
    (hA : IsIncreasing A) :
    (triangular.freeBufferedInfiniteVolume
        (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
        (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedBoxEvent k A)) ≤
      (hexagonal.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 HexVertex))).real
          (triHexFaceDualInnerEvent (2 * k) A) := by
  have htend := triangular.freeBufferedMeasure_tendsto_cylinder
    (2 * k)
    (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
    (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) hq
    (triangularBufferedBoxEvent_increasing k hA)
  apply le_of_tendsto htend
  filter_upwards [eventually_ge_atTop (2 * k)] with j hj
  exact triangularFreeBufferedBox_le_hexagonalFreeInfinite_faceDual
    k j hj hp hp1 hq hA

set_option maxHeartbeats 800000 in



theorem hexagonalFreeInfinite_faceDual_le_triangularWiredInfinite
    (k : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
    (hA : IsIncreasing A) :
    (hexagonal.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 HexVertex))).real
        (triHexFaceDualInnerEvent (2 * k) A) ≤
      (triangular.wiredBufferedInfiniteVolume
          (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
          (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedBoxEvent k A)) := by
  have htend := triangular.wiredBufferedMeasure_tendsto_cylinder
    (2 * k)
    (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
    (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) hq
    (triangularBufferedBoxEvent_increasing k hA)
  refine ge_of_tendsto htend ?_
  filter_upwards [eventually_ge_atTop (2 * k)] with j hj
  exact hexagonalFreeInfinite_faceDual_le_triangularWiredBuffered
    k j hj hp hp1 hq hA



theorem triangularFree_hexagonalFaceDual_triangularWired_sandwich
    (k : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph (2 * k)).edgeSet)}
    (hA : IsIncreasing A) :
    (triangular.freeBufferedInfiniteVolume
        (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
        (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * k)
          (triangularBufferedBoxEvent k A)) ≤
      (hexagonal.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 HexVertex))).real
          (triHexFaceDualInnerEvent (2 * k) A) ∧
    (hexagonal.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 HexVertex))).real
        (triHexFaceDualInnerEvent (2 * k) A) ≤
      (triangular.wiredBufferedInfiniteVolume
          (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
          (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (triangular.bufferedCylinder (2 * k)
            (triangularBufferedBoxEvent k A)) := by
  exact ⟨triangularFreeInfinite_le_hexagonalFreeInfinite_faceDual
      k hp hp1 hq hA,
    hexagonalFreeInfinite_faceDual_le_triangularWiredInfinite
      k hp hp1 hq hA⟩



theorem hexagonalFreeInfinite_faceDual_finiteEvent_le_triangularWiredInfinite
    (N : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    (hexagonal.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 HexVertex))).real
        (triHexFaceDualInnerEvent N A) ≤
      (triangular.wiredBufferedInfiniteVolume
          (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
          (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (2 * N)
          (triangularBufferedBoxEvent N
            (triangularBoxLiftEvent (by omega : N ≤ 2 * N) A))) := by
  have h := hexagonalFreeInfinite_faceDual_le_triangularWiredInfinite
    N hp hp1 hq
    (triangularBoxLiftEvent_increasing (by omega : N ≤ 2 * N) hA)
  rwa [triHexFaceDualInnerEvent_lift (by omega : N ≤ 2 * N)] at h




theorem hexagonalFreeInfinite_dualPercolation_le_triangularWiredPercolation
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (hexagonal.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 HexVertex))).real
        ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹'
          triangular.percolationEvent) ≤
      triangular.wiredPercolationProbability (dualParam p q) q := by
  have htend := triangular.bufferedRootBoundaryCylinder_real_tendsto
    (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
    (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
    (zero_lt_one.trans_le hq)
  apply ge_of_tendsto htend
  filter_upwards with n
  let k := triangular.bufferedRadius n + 1
  have hk : 1 ≤ k := by simp [k]
  have hnk : triangular.bufferedRadius n < k := by simp [k]
  calc
    (hexagonal.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 HexVertex))).real
        ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹'
          triangular.percolationEvent) ≤
      (hexagonal.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 HexVertex))).real
          (triHexFaceDualInnerEvent (2 * k)
            (triangularCenteredShellEvent (2 * k) k)) :=
      measureReal_mono
        (triHex_dualPercolationEvent_subset_faceDualInnerShell k hk)
        (measure_ne_top _ _)
    _ ≤ (triangular.wiredBufferedInfiniteVolume
          (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
          (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (triangular.bufferedCylinder (2 * k)
            (triangularBufferedInnerShellEvent k)) := by
      simpa only [triangularBufferedBoxEvent_centeredShell_eq] using
        hexagonalFreeInfinite_faceDual_le_triangularWiredInfinite
          k hp hp1 hq (triangularCenteredShellEvent_increasing (2 * k) k)
    _ ≤ (triangular.wiredBufferedInfiniteVolume
          (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
          (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (triangular.bufferedCylinder n
            (triangular.bufferedRootBoundaryEvent n)) :=
      measureReal_mono
        (triangularBufferedInnerShellCylinder_subset_rootBoundary k n hnk)
        (measure_ne_top _ _)




theorem triangularFreePercolation_le_hexagonalFreeDualPercolation
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (triangular.freeBufferedInfiniteVolume
        (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
        (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        triangular.percolationEvent ≤
      (hexagonal.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 HexVertex))).real
          ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹'
            triangular.percolationEvent) := by
  let muT : Measure (ConfigSpace (Sym2 (Site 2))) :=
    triangular.freeBufferedInfiniteVolume
      (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
      (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
      (zero_lt_one.trans_le hq)
  let muH : Measure (ConfigSpace (Sym2 HexVertex)) :=
    hexagonal.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq)
  let f := (dualConfigEquiv triHexFullDualEdgeEquiv).symm
  let nu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    Measure.map f muH
  letI : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv_symm
        triHexFullDualEdgeEquiv).measurable.aemeasurable
  have hnu (B : Set (ConfigSpace (Sym2 (Site 2))))
      (hB : MeasurableSet B) : nu.real B = muH.real (f ⁻¹' B) := by
    unfold nu Measure.real
    rw [Measure.map_apply
      (continuous_dualConfigEquiv_symm
        triHexFullDualEdgeEquiv).measurable hB]
  have htend :=
    triangular.bufferedRootBoundaryCylinder_real_tendsto_measure nu
  change muT.real triangular.percolationEvent ≤
    muH.real (f ⁻¹' triangular.percolationEvent)
  rw [← hnu triangular.percolationEvent
    (PeriodicPlanarDualPair.percolationEvent_measurableSet triangular)]
  apply ge_of_tendsto htend
  filter_upwards with n
  let k := triangular.bufferedRadius n + 1
  have hk : 1 ≤ k := by simp [k]
  have hnk : triangular.bufferedRadius n < k := by simp [k]
  calc
    muT.real triangular.percolationEvent ≤
      muT.real (triangular.bufferedCylinder (2 * k)
        (triangularBufferedInnerShellEvent k)) :=
      measureReal_mono
        (triangular_percolationEvent_subset_innerShell k hk)
        (measure_ne_top _ _)
    _ ≤ muH.real (triHexFaceDualInnerEvent (2 * k)
          (triangularCenteredShellEvent (2 * k) k)) := by
      simpa only [muT, muH,
        triangularBufferedBoxEvent_centeredShell_eq] using
        triangularFreeInfinite_le_hexagonalFreeInfinite_faceDual
          k hp hp1 hq
            (triangularCenteredShellEvent_increasing (2 * k) k)
    _ = muH.real (f ⁻¹'
          triangular.bufferedCylinder (2 * k)
            (triangularBufferedInnerShellEvent k)) := by
      rw [triHexFaceDualInnerShell_eq_dualConfig_preimage]
    _ ≤ muH.real (f ⁻¹'
          triangular.bufferedCylinder n
            (triangular.bufferedRootBoundaryEvent n)) :=
      measureReal_mono
        (Set.preimage_mono
          (triangularBufferedInnerShellCylinder_subset_rootBoundary
            k n hnk))
        (measure_ne_top _ _)
    _ = nu.real (triangular.bufferedCylinder n
          (triangular.bufferedRootBoundaryEvent n)) := by
      symm
      exact hnu _ (triangular.bufferedCylinder_measurableSet n
        (triangular.bufferedRootBoundaryEvent n))




theorem triangularFree_hexagonalFreeDual_triangularWired_percolation_sandwich
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (triangular.freeBufferedInfiniteVolume
        (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
        (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        triangular.percolationEvent ≤
      (hexagonal.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 HexVertex))).real
          ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹'
            triangular.percolationEvent) ∧
      (hexagonal.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 HexVertex))).real
          ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹'
            triangular.percolationEvent) ≤
      triangular.wiredPercolationProbability (dualParam p q) q := by
  exact ⟨triangularFreePercolation_le_hexagonalFreeDualPercolation hp hp1 hq,
    hexagonalFreeInfinite_dualPercolation_le_triangularWiredPercolation
      hp hp1 hq⟩




theorem hexagonalFreeDualPercolation_pos_of_triangularFreePercolation_pos
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (htri : 0 <
      (triangular.freeBufferedInfiniteVolume
          (dualParam_pos hp hp1 (zero_lt_one.trans_le hq))
          (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq))
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          triangular.percolationEvent) :
    0 < (hexagonal.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 HexVertex))).real
          ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹'
            triangular.percolationEvent) :=
  htri.trans_le
    (triangularFreePercolation_le_hexagonalFreeDualPercolation hp hp1 hq)



theorem triangularWiredPercolates_dualParam_of_hexagonalFreeDualPercolation
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hdual : 0 <
      (hexagonal.freeBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 HexVertex))).real
          ((dualConfigEquiv triHexFullDualEdgeEquiv).symm ⁻¹'
            triangular.percolationEvent)) :
    triangular.wiredPercolates (dualParam p q) q := by
  unfold PeriodicGraph.wiredPercolates
  exact hdual.trans_le
    (hexagonalFreeInfinite_dualPercolation_le_triangularWiredPercolation
      hp hp1 hq)

end

end StatMech.FK.PeriodicPlanar
