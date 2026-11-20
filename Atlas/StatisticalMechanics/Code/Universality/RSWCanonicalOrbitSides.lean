/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWEulerianWinding
import Code.Universality.RSWTraceSeparation
import Code.Ising.OuterContourWindingClose
import Code.Lattice.CanonicalContour
import Code.Lattice.OutsideCoveringClose
import Code.Walls.kc_orbitloopedges
















open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.Walls



theorem rlc_dartFace_step_sharedPrimalEdge (K : Set (Site 2)) (e : Dart) :
    sharedPrimalEdge (dartFace e) (dartFace (dartNext K e)) =
      s(e.tail, e.head) := by
  rcases dartDir_cases e with hd | hd | hd | hd
  · rw [dartFace_of_dir_right e hd, dartFace_next_of_dir_right K e hd,
      sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10
    rw [dart_head_eq e, hd]
    congr 1 <;> ext i <;> fin_cases i <;> simp
  · rw [dartFace_of_dir_left e hd, dartFace_next_of_dir_left K e hd]
    unfold sharedPrimalEdge
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [if_true]
    rw [show max (e.tail 1 - 1) (e.tail 1) = e.tail 1 by omega,
      dart_head_eq e, hd]
    rw [Sym2.eq_swap]
    congr 1
    all_goals
      ext i
      fin_cases i <;> simp <;> omega
  · rw [dartFace_of_dir_up e hd, dartFace_next_of_dir_up K e hd]
    unfold sharedPrimalEdge
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [if_neg (by omega), show max (e.tail 0 - 1) (e.tail 0) = e.tail 0 by omega,
      dart_head_eq e, hd]
    congr 1 <;> ext i <;> fin_cases i <;> simp
  · rw [dartFace_of_dir_down e hd, dartFace_next_of_dir_down K e hd,
      sharedPrimalEdge_left]
    unfold faceCorner00 faceCorner01
    rw [dart_head_eq e, hd]
    rw [Sym2.eq_swap]
    congr 1
    all_goals
      ext i
      fin_cases i <;> simp <;> omega


theorem rlc_dartFace_step_eq_flankFaces (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) :
    s(dartFace e, dartFace (dartNext K e)) = flankFaces e.tail e.head := by
  have hfaces := dartFace_step_adj K e he
  calc
    s(dartFace e, dartFace (dartNext K e))
        = flankFacesSym (symPrimal (dartFace e) (dartFace (dartNext K e))) := by
          rw [flankFacesSym_symPrimal hfaces.1]
    _ = flankFacesSym (sharedPrimalEdge (dartFace e) (dartFace (dartNext K e))) := by
          rw [symPrimal_eq_shared hfaces.1]
    _ = flankFacesSym s(e.tail, e.head) := by
          rw [rlc_dartFace_step_sharedPrimalEdge K e]
    _ = flankFaces e.tail e.head := rfl


theorem rlc_dartFace_step_injective_on_boundaryDarts
    (K : Set (Site 2)) {e f : Dart}
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f)
    (hstep : s(dartFace e, dartFace (dartNext K e)) =
      s(dartFace f, dartFace (dartNext K f))) :
    e = f := by
  apply dartPrimalEdge_injOn_boundaryDarts K he hf
  rw [dartPrimalEdge_eq, dartPrimalEdge_eq]
  rw [rlc_dartFace_step_eq_flankFaces K e he,
    rlc_dartFace_step_eq_flankFaces K f hf] at hstep
  have h := congrArg symPrimalSym hstep
  simpa [symPrimalSym_flankFaces e.adj,
    symPrimalSym_flankFaces f.adj] using h



theorem rlc_mpl_orbitFaceLoop_isTrail (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitFaceLoop K a).IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def, kc_orbitFaceLoop_edges]
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj hij
  simp only [List.mem_range] at hi hj
  have hei := iterate_isBoundaryDart' K a.1 a.2 i
  have hej := iterate_isBoundaryDart' K a.1 a.2 j
  have hdart : (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1 := by
    apply rlc_dartFace_step_injective_on_boundaryDarts K hei hej
    simpa only [Function.iterate_succ_apply'] using hij
  exact orbitDart_injOn K a (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj) hdart



theorem rlc_mpl_orbitLoop_base_bdEdge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    bdEdge (jec_leftRegion (mpl_orbitLoop K a))
      s(a.1.tail, a.1.head) := by
  let C := mpl_orbitLoop K a
  have hnd : C.edges.Nodup := by
    simpa [C, mpl_orbitLoop, SimpleGraph.Walk.edges_mapLe_eq_edges] using
      (rlc_mpl_orbitFaceLoop_isTrail K a).edges_nodup
  have hp : 0 < dartOrbitPeriod K a := dartOrbitPeriod_pos K hK a
  have hmemFace : flankFaces a.1.tail a.1.head ∈
      (mpl_orbitFaceLoop K a).edges := by
    rw [kc_orbitFaceLoop_edges]
    refine List.mem_map.mpr ⟨0, List.mem_range.mpr hp, ?_⟩
    simp [rlc_dartFace_step_eq_flankFaces K a.1 a.2]
  have hmem : rpc_crossEdge a.1.tail a.1.head ∈ C.edges := by
    rw [rlc_crossEdge_eq_flankFaces a.1.adj]
    simpa [C, mpl_orbitLoop, SimpleGraph.Walk.edges_mapLe_eq_edges] using hmemFace
  rw [rpc_crossFlip C a.1.adj,
    dow_walk_odd_count_iff_mem C hnd (rpc_crossEdge a.1.tail a.1.head)]
  exact hmem



theorem rlc_orbitLoop_sameSide_of_sameSide_K
    (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hsame : (u ∈ K ↔ v ∈ K)) :
    (u ∈ jec_leftRegion (mpl_orbitLoop K a) ↔
      v ∈ jec_leftRegion (mpl_orbitLoop K a)) := by
  let C := mpl_orbitLoop K a
  have hnotGraph : rpc_crossEdge u v ∉ (faceBoundaryGraph K).edgeSet := by
    rw [rlc_crossEdge_eq_flankFaces hadj,
      phb_flankFaces_mem_faceBoundaryGraph_iff hadj, bdEdge_mk]
    tauto
  have hnot : rpc_crossEdge u v ∉ C.edges := by
    intro hmem
    exact hnotGraph ((mpl_orbitFaceLoop K a).edges_subset_edgeSet (by
      simpa [C, mpl_orbitLoop, SimpleGraph.Walk.edges_mapLe_eq_edges] using hmem))
  have hnobd : ¬ bdEdge (jec_leftRegion C) s(u, v) := by
    rw [rpc_crossFlip C hadj]
    simp [List.count_eq_zero.mpr hnot]
  rw [bdEdge_mk] at hnobd
  tauto



theorem rlc_orbitLoop_const_on_barrierComponent
    (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {u v : Site 2} (hreach : (latticeMinusBarrier K).Reachable u v) :
    (u ∈ jec_leftRegion (mpl_orbitLoop K a) ↔
      v ∈ jec_leftRegion (mpl_orbitLoop K a)) := by
  obtain ⟨w⟩ := hreach
  induction w with
  | nil => exact Iff.rfl
  | @cons x y z hxy w ih =>
      have hsame : x ∈ K ↔ y ∈ K := by
        have hnobd := hxy.2
        rw [bdEdge_mk] at hnobd
        tauto
      exact (rlc_orbitLoop_sameSide_of_sameSide_K K a hxy.1 hsame).trans ih



theorem rlc_mpl_orbitLoop_contains_of_connected
    (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hhead : a.1.head ∉ jec_leftRegion (mpl_orbitLoop K a))
    (hconn : ∀ z ∈ K,
      (latticeMinusBarrier K).Reachable a.1.tail z) :
    K ⊆ jec_leftRegion (mpl_orbitLoop K a) := by
  have htail : a.1.tail ∈ jec_leftRegion (mpl_orbitLoop K a) := by
    have hflip := rlc_mpl_orbitLoop_base_bdEdge K hK a
    rw [bdEdge_mk] at hflip
    tauto
  intro z hz
  exact (rlc_orbitLoop_const_on_barrierComponent K a (hconn z hz)).mp htail



theorem rlc_mpl_orbitLoop_excludes_of_head_reachable
    (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hhead : a.1.head ∉ jec_leftRegion (mpl_orbitLoop K a))
    {z : Site 2} (hz : (latticeMinusBarrier K).Reachable a.1.head z) :
    z ∉ jec_leftRegion (mpl_orbitLoop K a) := by
  intro hzin
  exact hhead ((rlc_orbitLoop_const_on_barrierComponent K a hz).mpr hzin)



theorem rlc_faceBoundary_support_lower_bound
    (K : Set (Site 2)) (R : ℕ) (hbox : K ⊆ box 2 R)
    {f : Site 2} (hf : f ∈ (faceBoundaryGraph K).support) :
    -((R : ℤ)) - 1 ≤ f 0 := by
  have htouch := support_faceBoundaryGraph_subset K hf
  simp only [Set.mem_iUnion] at htouch
  obtain ⟨c, hcK, hfc⟩ := htouch
  have hcbox := hbox hcK
  rw [mem_box] at hcbox
  have hc0 := hcbox 0
  have hfc' : f ∈ cornerFaces c := hfc
  unfold cornerFaces at hfc'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfc'
  rcases hfc' with rfl | rfl | rfl | rfl <;>
    simp only [Matrix.cons_val_zero] <;> omega



theorem rlc_mpl_orbitLoop_head_outside_of_box
    (K : Set (Site 2)) (hK : K.Finite) (R : ℕ)
    (hbox : K ⊆ box 2 R)
    (a : {e : Dart // IsBoundaryDart K e})
    (hheadExt : a.1.head ∈ exterior 2 R) :
    a.1.head ∉ jec_leftRegion (mpl_orbitLoop K a) := by
  let q : Site 2 := ![-((R : ℤ)) - 1, 0]
  have hqExt : q ∈ exterior 2 R := by
    rw [mem_exterior]
    refine ⟨0, ?_⟩
    rw [show q 0 = -(((R + 1 : ℕ) : ℤ)) by simp [q]; omega,
      Int.natAbs_neg, Int.natAbs_natCast]
    omega
  have hcomp : exterior 2 R ⊆ Kᶜ := exterior_subset_compl K R hbox
  have hreachInduced :=
    exterior_reachable_compl K R (by norm_num) hcomp
      a.1.head q hheadExt hqExt
  let emb : ((hypercubicLattice 2).induce Kᶜ) →g Ising.latticeOn Kᶜ :=
    { toFun := Subtype.val
      map_rel' := fun {x y} hxy => ⟨hxy, x.2, y.2⟩ }
  have hreachComp : (Ising.latticeOn Kᶜ).Reachable a.1.head q :=
    hreachInduced.map emb
  have hreach : (latticeMinusBarrier K).Reachable a.1.head q :=
    hreachComp.mono (Ising.latticeOn_compl_le_latticeMinusBarrier K)
  have hqOut : q ∉ jec_leftRegion (mpl_orbitLoop K a) := by
    rw [jec_mem_leftRegion, not_not,
      jec_rayCount_eq_zero_of_right q (mpl_orbitLoop K a)]
    · exact Nat.even_iff.mpr rfl
    · intro f hf
      have hnonNil : ¬ (mpl_orbitFaceLoop K a).Nil := by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length]
        exact mpl_orbitFaceLoop_length_pos K hK a
      have hfGraph : f ∈ (faceBoundaryGraph K).support :=
        SimpleGraph.mem_support_of_mem_walk_support
          (mpl_orbitFaceLoop K a) hnonNil (by
            simpa [mpl_orbitLoop, SimpleGraph.Walk.support_mapLe_eq_support] using hf)
      simpa [q] using rlc_faceBoundary_support_lower_bound K R hbox hfGraph
  intro hheadIn
  exact hqOut ((rlc_orbitLoop_const_on_barrierComponent K a hreach).mp hheadIn)



theorem rlc_latticeOn_reachable_of_walk_support
    (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (hsupp : ∀ z ∈ w.support, z ∈ S) :
    (Ising.latticeOn S).Reachable x y := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v z huv w ih =>
      have hu : u ∈ S := hsupp u (by simp)
      have hv : v ∈ S := hsupp v (by simp)
      have htail : ∀ q ∈ w.support, q ∈ S := by
        intro q hq
        exact hsupp q (by simp [hq])
      exact (show (Ising.latticeOn S).Adj u v from ⟨huv, hu, hv⟩).reachable.trans
        (ih htail)



theorem rlc_mixedWiredReachSet_latticeOn_reachable_lower
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {z : Site 2}
    (hz : z ∈ rlc_mixedWiredReachSet G omega) :
    (Ising.latticeOn (rlc_mixedWiredReachSet G omega)).Reachable
      G.lowerVertex z := by
  let B := rect (-2 * n) (2 * n) (-n) n
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  obtain ⟨hzB, hzConn⟩ := hz
  obtain ⟨p⟩ := hzConn
  have aux : ∀ {x y : B},
      (openSubgraphInduce 2 eta B).Walk x y →
      ConnectedWithin 2 eta B
        ⟨G.lowerVertex,
          rlc_rightPathVertex_mem_connectorBox gamma
            G.lowerVertex_mem_right⟩ x →
      (Ising.latticeOn (rlc_mixedWiredReachSet G omega)).Reachable
        (x : Site 2) (y : Site 2) := by
    intro x y w
    induction w with
    | nil => intro _; exact SimpleGraph.Reachable.refl _
    | @cons u v q huv w ih =>
        intro huConn
        have hvConn : ConnectedWithin 2 eta B
            ⟨G.lowerVertex,
              rlc_rightPathVertex_mem_connectorBox gamma
                G.lowerVertex_mem_right⟩ v :=
          huConn.trans huv.reachable
        have huK : (u : Site 2) ∈ rlc_mixedWiredReachSet G omega :=
          ⟨u.2, huConn⟩
        have hvK : (v : Site 2) ∈ rlc_mixedWiredReachSet G omega :=
          ⟨v.2, hvConn⟩
        have huvLat : (hypercubicLattice 2).Adj (u : Site 2) (v : Site 2) :=
          huv.1
        exact (show (Ising.latticeOn (rlc_mixedWiredReachSet G omega)).Adj
            (u : Site 2) (v : Site 2) from ⟨huvLat, huK, hvK⟩).reachable.trans
          (ih hvConn)
  exact aux p (connectedWithin_refl eta B _)



theorem rlc_mixedWiredReachSet_subset_natBox
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_mixedWiredReachSet G omega ⊆ box 2 (2 * n).toNat := by
  intro z hz
  have hzR := rlc_mixedWiredReachSet_subset_box G omega hz
  rw [mem_rect] at hzR
  rw [mem_box]
  intro i
  have hRcast : (((2 * n).toNat : ℕ) : ℤ) = 2 * n :=
    Int.toNat_of_nonneg (by omega)
  fin_cases i
  · change (z 0).natAbs ≤ (2 * n).toNat
    by_cases hz0 : 0 ≤ z 0
    · have hzcast : (((z 0).natAbs : ℕ) : ℤ) = z 0 :=
        Int.natAbs_of_nonneg hz0
      omega
    · have hzcast : (((z 0).natAbs : ℕ) : ℤ) = -z 0 := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      omega
  · change (z 1).natAbs ≤ (2 * n).toNat
    by_cases hz1 : 0 ≤ z 1
    · have hzcast : (((z 1).natAbs : ℕ) : ℤ) = z 1 :=
        Int.natAbs_of_nonneg hz1
      omega
    · have hzcast : (((z 1).natAbs : ℕ) : ℤ) = -z 1 := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      omega



theorem rlc_outerExitDart_head_mem_exterior
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (rlc_outerExitDart G omega).head ∈ exterior 2 (2 * n).toNat := by
  have hvx : (gamma.1.2.1 : Site 2) 0 = 2 * n := by
    simpa using gamma.1.2.1.2.2
  rw [mem_exterior]
  refine ⟨0, ?_⟩
  have hhead : (rlc_outerExitDart G omega).head 0 = 2 * n + 1 := by
    simp [rlc_outerExitDart, hvx]
  rw [hhead]
  have hRcast : (((2 * n).toNat : ℕ) : ℤ) = 2 * n :=
    Int.toNat_of_nonneg (by omega)
  have hheadCast : ((((2 * n + 1).natAbs : ℕ)) : ℤ) = 2 * n + 1 :=
    Int.natAbs_of_nonneg (by omega)
  omega


theorem rlc_outerExitAnchor_head_not_mem_windingRegion
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (rlc_outerExitAnchor G omega).1.head ∉
      rlc_outerExitWindingRegion G omega := by
  exact rlc_mpl_orbitLoop_head_outside_of_box
    (rlc_mixedWiredReachSet G omega)
    (rlc_mixedWiredReachSet_finite G omega) (2 * n).toNat
    (rlc_mixedWiredReachSet_subset_natBox G hn omega)
    (rlc_outerExitAnchor G omega)
    (rlc_outerExitDart_head_mem_exterior G hn omega)



theorem rlc_mixedWiredReachSet_subset_outerExitWindingRegion
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_mixedWiredReachSet G omega ⊆
      rlc_outerExitWindingRegion G omega := by
  let K := rlc_mixedWiredReachSet G omega
  let a := rlc_outerExitAnchor G omega
  have hhead : a.1.head ∉ jec_leftRegion (mpl_orbitLoop K a) := by
    simpa [K, a, rlc_outerExitWindingRegion, mpl_orbitLoop] using
      rlc_outerExitAnchor_head_not_mem_windingRegion G hn omega
  have hconn : ∀ z ∈ K,
      (latticeMinusBarrier K).Reachable a.1.tail z := by
    intro z hz
    have hLowerZ :=
      rlc_mixedWiredReachSet_latticeOn_reachable_lower G omega hz
    have htailK : a.1.tail ∈ K := a.2.1
    have hLowerTail :=
      rlc_mixedWiredReachSet_latticeOn_reachable_lower G omega htailK
    exact (hLowerTail.symm.trans hLowerZ).mono
      (Ising.latticeOn_le_latticeMinusBarrier K)
  simpa [K, a, rlc_outerExitWindingRegion, mpl_orbitLoop] using
    rlc_mpl_orbitLoop_contains_of_connected K
      (rlc_mixedWiredReachSet_finite G omega) a hhead hconn



theorem rlc_latticeOn_compl_reachable_of_exterior
    (K : Set (Site 2)) (R : ℕ) (hbox : K ⊆ box 2 R)
    {x y : Site 2} (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    (Ising.latticeOn Kᶜ).Reachable x y := by
  have hcomp : exterior 2 R ⊆ Kᶜ := exterior_subset_compl K R hbox
  have hreach := exterior_reachable_compl K R (by norm_num) hcomp x y hx hy
  let emb : ((hypercubicLattice 2).induce Kᶜ) →g Ising.latticeOn Kᶜ :=
    { toFun := Subtype.val
      map_rel' := fun {u v} huv => ⟨huv, u.2, v.2⟩ }
  exact hreach.map emb



theorem rlc_leftPathVertex_reachable_leftStart_in_compl_of_failure
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    {z : Site 2} (hz : z ∈ rlc_pathVertices gamma'.1) :
    (Ising.latticeOn (rlc_mixedWiredReachSet G omega)ᶜ).Reachable
      z (gamma'.1.1 : Site 2) := by
  let W := rlc_ambientCrossingWalk gamma'.1
  have hzW : z ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).2 hz
  let q := W.takeUntil z hzW
  have hsupp : ∀ y ∈ q.support,
      y ∈ (rlc_mixedWiredReachSet G omega)ᶜ := by
    intro y hy
    have hyW : y ∈ W.support := W.support_takeUntil_subset_support hzW hy
    have hyPath : y ∈ rlc_pathVertices gamma'.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 y).1 hyW
    exact rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno hyPath
  exact (rlc_latticeOn_reachable_of_walk_support
    (rlc_mixedWiredReachSet G omega)ᶜ q hsupp).symm



theorem rlc_outerExitHead_reachable_leftPathVertex_of_failure
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    {z : Site 2} (hz : z ∈ rlc_pathVertices gamma'.1) :
    (Ising.latticeOn (rlc_mixedWiredReachSet G omega)ᶜ).Reachable
      (rlc_outerExitAnchor G omega).1.head z := by
  let K := rlc_mixedWiredReachSet G omega
  let start : Site 2 := gamma'.1.1
  let west : Site 2 := ![start 0 - 1, start 1]
  let R : ℕ := (2 * n).toNat
  have hstartx : start 0 = -2 * n := by
    simpa [start] using (show (gamma'.1.1 : Site 2) 0 = -2 * n from
      (mem_leftSide.mp gamma'.1.1.2).2)
  have hstartPath : start ∈ rlc_pathVertices gamma'.1 := by
    exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 start).1
      (rlc_ambientCrossingWalk gamma'.1).start_mem_support
  have hstartNot : start ∉ K :=
    rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno hstartPath
  have hwestNot : west ∉ K := by
    intro hwest
    have hrect := rlc_mixedWiredReachSet_subset_box G omega hwest
    rw [mem_rect] at hrect
    have hwestx : west 0 = -2 * n - 1 := by simp [west, hstartx]
    omega
  have hstepAdj : (hypercubicLattice 2).Adj start west := by
    simp [west, hypercubicLattice_adj]
  have hstep : (Ising.latticeOn Kᶜ).Reachable start west :=
    (show (Ising.latticeOn Kᶜ).Adj start west from
      ⟨hstepAdj, hstartNot, hwestNot⟩).reachable
  have hwestExt : west ∈ exterior 2 R := by
    rw [mem_exterior]
    refine ⟨0, ?_⟩
    have hwestx : west 0 = -2 * n - 1 := by simp [west, hstartx]
    rw [hwestx]
    have hRcast : ((R : ℕ) : ℤ) = 2 * n := by
      exact Int.toNat_of_nonneg (by omega)
    have hwestCast : ((((-2 * n - 1).natAbs : ℕ)) : ℤ) = 2 * n + 1 := by
      rw [show -2 * n - 1 = -(2 * n + 1) by ring,
        Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    omega
  have hheadExt : (rlc_outerExitAnchor G omega).1.head ∈ exterior 2 R :=
    rlc_outerExitDart_head_mem_exterior G hn omega
  have hext : (Ising.latticeOn Kᶜ).Reachable
      west (rlc_outerExitAnchor G omega).1.head :=
    rlc_latticeOn_compl_reachable_of_exterior K R
      (rlc_mixedWiredReachSet_subset_natBox G hn omega) hwestExt hheadExt
  have hzStart : (Ising.latticeOn Kᶜ).Reachable z start :=
    rlc_leftPathVertex_reachable_leftStart_in_compl_of_failure
      G omega hno hz
  exact (hzStart.trans (hstep.trans hext)).symm



theorem rlc_outerExitJordanTraceSides_of_failure
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    RlcOuterExitJordanTraceSides G omega := by
  constructor
  · exact rlc_mixedWiredReachSet_subset_outerExitWindingRegion G hn omega
  · intro z hzPath _hzNot
    let K := rlc_mixedWiredReachSet G omega
    let a := rlc_outerExitAnchor G omega
    have hhead : a.1.head ∉ jec_leftRegion (mpl_orbitLoop K a) := by
      simpa [K, a, rlc_outerExitWindingRegion, mpl_orbitLoop] using
        rlc_outerExitAnchor_head_not_mem_windingRegion G hn omega
    have hreachComp : (Ising.latticeOn Kᶜ).Reachable a.1.head z := by
      simpa [K, a] using
        rlc_outerExitHead_reachable_leftPathVertex_of_failure
          G hn omega hno hzPath
    have hreach : (latticeMinusBarrier K).Reachable a.1.head z :=
      hreachComp.mono (Ising.latticeOn_compl_le_latticeMinusBarrier K)
    simpa [K, a, rlc_outerExitWindingRegion, mpl_orbitLoop] using
      rlc_mpl_orbitLoop_excludes_of_head_reachable K a hhead hreach



theorem rlc_outerExitTraceSeparation_of_failure_of_preimageSplit_closedJordan
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (htrace : RlcLowestHighestTracePreimageSplit gamma gamma') :
    RlcOuterExitTraceSeparation G hn hlt omega :=
  rlc_outerExitTraceSeparation_of_failure_of_preimageSplit
    G hn hlt omega hno htrace
      (rlc_outerExitJordanTraceSides_of_failure G hn omega hno)



theorem rlc_mixedWiredConnectorEvent_dualReflect_of_failure_closedJordan
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (htrace : RlcLowestHighestTracePreimageSplit gamma gamma')
    (horder : RlcOuterExitContactArcOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G :=
  rlc_mixedWiredConnectorEvent_dualReflect_of_failure_of_preimageSplit
    G hn hlt omega hno htrace
      (rlc_outerExitJordanTraceSides_of_failure G hn omega hno) horder

end Universality
end StatMech

