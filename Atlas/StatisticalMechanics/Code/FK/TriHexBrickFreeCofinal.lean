/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexBrickDualCoordinates
import Code.FK.FreeNestedDecreasing





open Filter Finset Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC
open StatMech.FrontierD

noncomputable section



def triHexHexBufferedFaceDualInnerEvent (N n : Nat)
    (A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)) :
    Set (ConfigSpace (Sym2 (hexagonal.BufferedVertex n))) :=
  {rho | triHexFaceDualInnerActive N
    (hexagonal.extendEdge (hexagonal.bufferedRadius n) rho) ∈ A}


def triHexStarFaceDualInnerEvent
    {N m : Nat} (hNm : N < m)
    (A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)) :
    Set (ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex m))) :=
  {omega | triHexBrickDualInnerActiveRestrict hNm
    (triHexBrickPfdSupport m omega) ∈ A}

theorem triHexPlanarFiniteStarToHexBuffered_edgeIncl
    (m : Nat) (e : Sym2 (triHexPlanarFiniteStarPlanar m).V) :
    triHexPlanarFiniteStarEdgeIncl m e =
      hexagonal.edgeIncl (hexagonal.bufferedRadius (m + 2))
        (ocd_innerEdge (triHexPlanarFiniteStarToHexBuffered m) e) := by
  induction e using Sym2.inductionOn with
  | _ x y => rfl



theorem triHexFaceDualInnerActive_starRestrict_buffered
    {N m : Nat} (hNm : N < m)
    (rho : ConfigSpace (Sym2 (hexagonal.BufferedVertex (m + 2)))) :
    triHexFaceDualInnerActive N
        (triHexPlanarFiniteStarExtendEdge m
          (ocd_innerRestrict
            (triHexPlanarFiniteStarToHexBuffered m) rho)) =
      triHexFaceDualInnerActive N
        (hexagonal.extendEdge (hexagonal.bufferedRadius (m + 2)) rho) := by
  funext a
  rcases a with ⟨a, ha⟩
  induction a using Sym2.inductionOn with
  | _ x y =>
      have hxy : (triangularBoxGraph N).Adj x y :=
        (SimpleGraph.mem_edgeSet _).1 ha
      have hfull : (triHexBrickFullDualGraph m).Adj
          (triHexBrickInnerFaceMap N m x)
          (triHexBrickInnerFaceMap N m y) :=
        (triHexBrickInnerFaceMap_adj hNm x y).mp hxy
      obtain ⟨e, heBundle⟩ := pfdEdgeBundle_nonempty_of_fullDualEdge
        (triHexPlanarFiniteStarPlanar m)
        ((SimpleGraph.mem_edgeSet _).2 hfull)
      rw [mem_pfdEdgeBundle] at heBundle
      have heIncl :=
        triHexPlanarFiniteStar_edgeIncl_eq_fullDual_of_dualEnds_eq_inner
          hNm heBundle
      unfold triHexFaceDualInnerActive
      simp only [Sym2.map_mk]
      rw [← heIncl,
        triHexPlanarFiniteStarExtendEdge_edgeIncl,
        triHexPlanarFiniteStarToHexBuffered_edgeIncl,
        hexagonal.extendEdge_edgeIncl]
      rfl

theorem triHexStarFaceDualInnerEvent_preimage_outerBuffered
    {N m : Nat} (hNm : N < m)
    (A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)) :
    ocd_innerRestrict (triHexPlanarFiniteStarToHexBuffered m) ⁻¹'
        triHexStarFaceDualInnerEvent hNm A =
      triHexHexBufferedFaceDualInnerEvent N (m + 2) A := by
  ext rho
  change (triHexBrickDualInnerActiveRestrict hNm
      (triHexBrickPfdSupport m
        (ocd_innerRestrict
          (triHexPlanarFiniteStarToHexBuffered m) rho)) ∈ A ↔
    triHexFaceDualInnerActive N
      (hexagonal.extendEdge (hexagonal.bufferedRadius (m + 2)) rho) ∈ A)
  rw [triHexBrickDualInnerActiveRestrict_pfdSupport_eq_faceDual,
    triHexFaceDualInnerActive_starRestrict_buffered hNm]
  rfl

theorem triHexStarFaceDualInnerEvent_isDecreasing
    {N m : Nat} (hNm : N < m)
    {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    IsDecreasing (triHexStarFaceDualInnerEvent hNm A) := by
  rw [show triHexStarFaceDualInnerEvent hNm A =
      triHexPlanarFiniteStarExtendEdge m ⁻¹'
        triHexFaceDualInnerEvent N A by
    ext omega
    simp only [triHexStarFaceDualInnerEvent,
      triHexFaceDualInnerEvent, Set.mem_setOf_eq, Set.mem_preimage]
    rw [triHexBrickDualInnerActiveRestrict_pfdSupport_eq_faceDual]
    rfl]
  intro eta omega home hmem
  apply (triHexFaceDualInnerEvent_isDecreasing N hA)
  · exact monotone_triHexPlanarFiniteStarExtendEdge m home
  · exact hmem



theorem triHexHexBufferedFaceDualInnerEvent_le_freeStar
    {N m : Nat} (hNm : N < m)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    (∑ rho,
        (triHexHexBufferedFaceDualInnerEvent N (m + 2) A).indicator
          (fun _ => (1 : Real)) rho *
        fkProb (hexagonal.bufferedGraph (m + 2)) p q rho) ≤
      ∑ omega : ConfigSpace
          (Sym2 (TriHexPlanarFiniteStarVertex m)),
        (triHexStarFaceDualInnerEvent hNm A).indicator
          (fun _ => (1 : Real)) omega *
        fkProb (triHexPlanarFiniteStarGraph m) p q omega := by
  have hdom := bdp_free_outer_dominated_inner_decreasing
    (triHexPlanarFiniteStarToHexBuffered m).injective
    (triHexPlanarFiniteStarToHexBuffered_adjMatch m)
    hp hp1 hq (triHexStarFaceDualInnerEvent_isDecreasing hNm hA)
  rw [triHexStarFaceDualInnerEvent_preimage_outerBuffered hNm] at hdom
  exact hdom


def triHexPlanarFiniteStarToHexBufferedLE
    {r n : Nat} (hrn : r + 2 ≤ n) :
    TriHexPlanarFiniteStarVertex r ↪ hexagonal.BufferedVertex n :=
  (triHexPlanarFiniteStarToHexBuffered r).trans
    (hexagonal.bufferedVertexInclLE hrn)

@[simp] theorem triHexPlanarFiniteStarToHexBufferedLE_val
    {r n : Nat} (hrn : r + 2 ≤ n)
    (v : TriHexPlanarFiniteStarVertex r) :
    (triHexPlanarFiniteStarToHexBufferedLE hrn v : HexVertex) =
      triHexPlanarFiniteStarVertexEmbedding r v := rfl

theorem triHexPlanarFiniteStarToHexBufferedLE_edgeIncl
    {r n : Nat} (hrn : r + 2 ≤ n)
    (e : Sym2 (TriHexPlanarFiniteStarVertex r)) :
    triHexPlanarFiniteStarEdgeIncl r e =
      hexagonal.edgeIncl (hexagonal.bufferedRadius n)
        (ocd_innerEdge
          (triHexPlanarFiniteStarToHexBufferedLE hrn) e) := by
  induction e using Sym2.inductionOn with
  | _ x y => rfl

theorem triHexPlanarHexBufferedToFiniteStar_edgeIncl
    (n : Nat) (e : Sym2 (hexagonal.BufferedVertex n)) :
    triHexPlanarFiniteStarEdgeIncl
        (triHexPlanarHexBufferedOuterStarLevel n)
        (ocd_innerEdge (triHexPlanarHexBufferedToFiniteStar n) e) =
      hexagonal.edgeIncl (hexagonal.bufferedRadius n) e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      apply Sym2.eq_iff.mpr
      left
      exact ⟨triHexPlanarHexBufferedToFiniteStar_embedding_eq n x,
        triHexPlanarHexBufferedToFiniteStar_embedding_eq n y⟩




theorem triHexFaceDualInnerActive_bufferedRestrict_outerStar
    {N n : Nat} (hNn : N + 3 ≤ n)
    (rho : ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex
      (triHexPlanarHexBufferedOuterStarLevel n)))) :
    triHexFaceDualInnerActive N
        (hexagonal.extendEdge (hexagonal.bufferedRadius n)
          (ocd_innerRestrict
            (triHexPlanarHexBufferedToFiniteStar n) rho)) =
      triHexFaceDualInnerActive N
        (triHexPlanarFiniteStarExtendEdge
          (triHexPlanarHexBufferedOuterStarLevel n) rho) := by
  have hNouter : N < triHexPlanarHexBufferedOuterStarLevel n := by
    unfold triHexPlanarHexBufferedOuterStarLevel
    have hn : n ≤ hexagonal.bufferedRadius (n + 1) :=
      (Nat.le_succ n).trans (hexagonal.id_le_bufferedRadius (n + 1))
    omega
  funext a
  rcases a with ⟨a, ha⟩
  induction a using Sym2.inductionOn with
  | _ x y =>
      let r := N + 1
      have hNr : N < r := by omega
      have hrn : r + 2 ≤ n := by simpa [r, Nat.add_assoc] using hNn
      have hxy : (triangularBoxGraph N).Adj x y :=
        (SimpleGraph.mem_edgeSet _).1 ha
      have hfull : (triHexBrickFullDualGraph r).Adj
          (triHexBrickInnerFaceMap N r x)
          (triHexBrickInnerFaceMap N r y) :=
        (triHexBrickInnerFaceMap_adj hNr x y).mp hxy
      obtain ⟨e, heBundle⟩ := pfdEdgeBundle_nonempty_of_fullDualEdge
        (triHexPlanarFiniteStarPlanar r)
        ((SimpleGraph.mem_edgeSet _).2 hfull)
      rw [mem_pfdEdgeBundle] at heBundle
      have heIncl :=
        triHexPlanarFiniteStar_edgeIncl_eq_fullDual_of_dualEnds_eq_inner
          hNr heBundle
      let b : Sym2 (hexagonal.BufferedVertex n) :=
        ocd_innerEdge (triHexPlanarFiniteStarToHexBufferedLE hrn) e.1
      have hbIncl :
          hexagonal.edgeIncl (hexagonal.bufferedRadius n) b =
            triHexFullDualEdgeEquiv s(x.1, y.1) := by
        rw [← heIncl]
        exact (triHexPlanarFiniteStarToHexBufferedLE_edgeIncl hrn e.1).symm
      unfold triHexFaceDualInnerActive
      simp only [Sym2.map_mk]
      rw [← hbIncl, hexagonal.extendEdge_edgeIncl]
      rw [← triHexPlanarHexBufferedToFiniteStar_edgeIncl,
        triHexPlanarFiniteStarExtendEdge_edgeIncl]
      rfl

theorem triHexHexBufferedFaceDualInnerEvent_preimage_outerStar
    {N n : Nat} (hNn : N + 3 ≤ n)
    (A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)) :
    ocd_innerRestrict (triHexPlanarHexBufferedToFiniteStar n) ⁻¹'
        triHexHexBufferedFaceDualInnerEvent N n A =
      triHexStarFaceDualInnerEvent
        (show N < triHexPlanarHexBufferedOuterStarLevel n by
          unfold triHexPlanarHexBufferedOuterStarLevel
          have hn : n ≤ hexagonal.bufferedRadius (n + 1) :=
            (Nat.le_succ n).trans
              (hexagonal.id_le_bufferedRadius (n + 1))
          omega)
        A := by
  ext rho
  change (triHexFaceDualInnerActive N
      (hexagonal.extendEdge (hexagonal.bufferedRadius n)
        (ocd_innerRestrict
          (triHexPlanarHexBufferedToFiniteStar n) rho)) ∈ A ↔
    triHexBrickDualInnerActiveRestrict _
      (triHexBrickPfdSupport
        (triHexPlanarHexBufferedOuterStarLevel n) rho) ∈ A)
  rw [triHexBrickDualInnerActiveRestrict_pfdSupport_eq_faceDual,
    triHexFaceDualInnerActive_bufferedRestrict_outerStar hNn]
  rfl



theorem freeOuterStar_le_triHexHexBufferedFaceDualInnerEvent
    {N n : Nat} (hNn : N + 3 ≤ n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    (∑ rho : ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex
          (triHexPlanarHexBufferedOuterStarLevel n))),
        (triHexStarFaceDualInnerEvent
          (show N < triHexPlanarHexBufferedOuterStarLevel n by
            unfold triHexPlanarHexBufferedOuterStarLevel
            have hn : n ≤ hexagonal.bufferedRadius (n + 1) :=
              (Nat.le_succ n).trans
                (hexagonal.id_le_bufferedRadius (n + 1))
            omega) A).indicator (fun _ => (1 : Real)) rho *
          fkProb (triHexPlanarFiniteStarGraph
            (triHexPlanarHexBufferedOuterStarLevel n)) p q rho) ≤
      ∑ omega,
        (triHexHexBufferedFaceDualInnerEvent N n A).indicator
          (fun _ => (1 : Real)) omega *
        fkProb (hexagonal.bufferedGraph n) p q omega := by
  have hdom := bdp_free_outer_dominated_inner_decreasing
    (triHexPlanarHexBufferedToFiniteStar n).injective
    (triHexPlanarHexBufferedToFiniteStar_adjMatch n)
    hp hp1 hq
    (show IsDecreasing (triHexHexBufferedFaceDualInnerEvent N n A) by
      intro omega eta home hmem
      apply hA
        (antitone_triHexFaceDualInnerActive N
          (hexagonal.monotone_extendEdge
            (hexagonal.bufferedRadius n) home))
        hmem)
  rw [triHexHexBufferedFaceDualInnerEvent_preimage_outerStar hNn] at hdom
  exact hdom



theorem triHexFaceDualInnerActive_extend_bufferedRestrict
    {N n : Nat} (hNn : N + 3 ≤ n)
    (omega : ConfigSpace (Sym2 HexVertex)) :
    triHexFaceDualInnerActive N
        (hexagonal.extendEdge (hexagonal.bufferedRadius n)
          (hexagonal.bufferedRestrict n omega)) =
      triHexFaceDualInnerActive N omega := by
  funext a
  rcases a with ⟨a, ha⟩
  induction a using Sym2.inductionOn with
  | _ x y =>
      let r := N + 1
      have hNr : N < r := by omega
      have hrn : r + 2 ≤ n := by simpa [r, Nat.add_assoc] using hNn
      have hxy : (triangularBoxGraph N).Adj x y :=
        (SimpleGraph.mem_edgeSet _).1 ha
      have hfull : (triHexBrickFullDualGraph r).Adj
          (triHexBrickInnerFaceMap N r x)
          (triHexBrickInnerFaceMap N r y) :=
        (triHexBrickInnerFaceMap_adj hNr x y).mp hxy
      obtain ⟨e, heBundle⟩ := pfdEdgeBundle_nonempty_of_fullDualEdge
        (triHexPlanarFiniteStarPlanar r)
        ((SimpleGraph.mem_edgeSet _).2 hfull)
      rw [mem_pfdEdgeBundle] at heBundle
      have heIncl :=
        triHexPlanarFiniteStar_edgeIncl_eq_fullDual_of_dualEnds_eq_inner
          hNr heBundle
      let b : Sym2 (hexagonal.BufferedVertex n) :=
        ocd_innerEdge (triHexPlanarFiniteStarToHexBufferedLE hrn) e.1
      have hbIncl :
          hexagonal.edgeIncl (hexagonal.bufferedRadius n) b =
            triHexFullDualEdgeEquiv s(x.1, y.1) := by
        rw [← heIncl]
        exact (triHexPlanarFiniteStarToHexBufferedLE_edgeIncl hrn e.1).symm
      unfold triHexFaceDualInnerActive
      simp only [Sym2.map_mk]
      rw [← hbIncl, hexagonal.extendEdge_edgeIncl]
      rfl


theorem triHexFaceDualInnerEvent_eq_bufferedCylinder
    (N : Nat)
    (A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)) :
    triHexFaceDualInnerEvent N A =
      hexagonal.bufferedCylinder (N + 3)
        (triHexHexBufferedFaceDualInnerEvent N (N + 3) A) := by
  ext omega
  simp only [triHexFaceDualInnerEvent,
    triHexHexBufferedFaceDualInnerEvent,
    PeriodicGraph.bufferedCylinder, Set.mem_preimage, Set.mem_setOf_eq]
  rw [triHexFaceDualInnerActive_extend_bufferedRestrict (le_refl (N + 3))]



theorem freeBufferedMeasure_real_triHexFaceDualInnerEvent
    {N n : Nat} (hNn : N + 3 ≤ n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)) :
    (hexagonal.freeBufferedMeasure n hp hp1 hq :
        MeasureTheory.Measure (ConfigSpace (Sym2 HexVertex))).real
        (triHexFaceDualInnerEvent N A) =
      ∑ rho,
        (triHexHexBufferedFaceDualInnerEvent N n A).indicator
          (fun _ => (1 : Real)) rho *
        fkProb (hexagonal.bufferedGraph n) p q rho := by
  rw [triHexFaceDualInnerEvent_eq_bufferedCylinder]
  rw [hexagonal.freeBufferedMeasure_real_cylinder hNn hp hp1 hq]
  have hevent :
      hexagonal.bufferedRestrictLE hNn ⁻¹'
          triHexHexBufferedFaceDualInnerEvent N (N + 3) A =
        triHexHexBufferedFaceDualInnerEvent N n A := by
    ext rho
    change (triHexFaceDualInnerActive N
        (hexagonal.extendEdge (hexagonal.bufferedRadius (N + 3))
          (hexagonal.bufferedRestrictLE hNn rho)) ∈ A ↔
      triHexFaceDualInnerActive N
        (hexagonal.extendEdge (hexagonal.bufferedRadius n) rho) ∈ A)
    have h := triHexFaceDualInnerActive_extend_bufferedRestrict
      (le_refl (N + 3))
      (hexagonal.extendEdge (hexagonal.bufferedRadius n) rho)
    rw [hexagonal.bufferedRestrict_extendEdge_le hNn] at h
    rw [h]
  rw [hevent]



theorem triHexFreeOuterStarFaceDualInnerEvent_tendsto
    (N : Nat) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (A : Set (ConfigSpace (triangularBoxGraph N).edgeSet))
    (hA : IsIncreasing A) :
    Filter.Tendsto
      (fun j =>
        let n := N + 3 + j
        let m := triHexPlanarHexBufferedOuterStarLevel n
        ∑ rho : ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex m)),
          (triHexStarFaceDualInnerEvent
            (show N < m by
              dsimp only [m, n]
              unfold triHexPlanarHexBufferedOuterStarLevel
              have hn : N + 3 + j ≤
                  hexagonal.bufferedRadius (N + 3 + j + 1) :=
                (Nat.le_succ (N + 3 + j)).trans
                  (hexagonal.id_le_bufferedRadius (N + 3 + j + 1))
              omega) A).indicator (fun _ => (1 : Real)) rho *
            fkProb (triHexPlanarFiniteStarGraph m) p q rho)
      Filter.atTop
      (nhds ((hexagonal.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) :
          MeasureTheory.Measure (ConfigSpace (Sym2 HexVertex))).real
        (triHexFaceDualInnerEvent N A))) := by
  let k : Nat → Nat := fun j => N + 3 + j
  let L : Nat → Nat := fun j =>
    triHexPlanarHexBufferedOuterStarLevel (k j)
  let target :=
    (hexagonal.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace (Sym2 HexVertex))).real
      (triHexFaceDualInnerEvent N A)
  let b : Nat → Real := fun n =>
    (hexagonal.freeBufferedMeasure n hp hp1
      (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace (Sym2 HexVertex))).real
      (triHexFaceDualInnerEvent N A)
  let s : Nat → Real := fun j =>
    ∑ rho : ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex (L j))),
      (triHexStarFaceDualInnerEvent
        (show N < L j by
          dsimp only [L, k]
          unfold triHexPlanarHexBufferedOuterStarLevel
          have hn : N + 3 + j ≤
              hexagonal.bufferedRadius (N + 3 + j + 1) :=
            (Nat.le_succ (N + 3 + j)).trans
              (hexagonal.id_le_bufferedRadius (N + 3 + j + 1))
          omega) A).indicator (fun _ => (1 : Real)) rho *
        fkProb (triHexPlanarFiniteStarGraph (L j)) p q rho
  have hb : Filter.Tendsto b Filter.atTop (nhds target) := by
    simpa only [b, target] using
      (hexagonal.freeBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
        (isClopen_triHexFaceDualInnerEvent N A)
  have hk : Filter.Tendsto k Filter.atTop Filter.atTop := by
    simpa only [k, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      tendsto_add_atTop_nat (N + 3)
  have hLindex : Filter.Tendsto (fun j => L j + 2)
      Filter.atTop Filter.atTop := by
    apply tendsto_atTop_mono (f := k)
    · intro j
      dsimp only [L, k]
      unfold triHexPlanarHexBufferedOuterStarLevel
      have hj : N + 3 + j ≤
          hexagonal.bufferedRadius (N + 3 + j + 1) :=
        (Nat.le_succ (N + 3 + j)).trans
          (hexagonal.id_le_bufferedRadius (N + 3 + j + 1))
      omega
    · exact hk
  have hlower : ∀ j, b (L j + 2) ≤ s j := by
    intro j
    have hNL : N < L j := by
      dsimp only [L, k]
      unfold triHexPlanarHexBufferedOuterStarLevel
      have hj : N + 3 + j ≤
          hexagonal.bufferedRadius (N + 3 + j + 1) :=
        (Nat.le_succ (N + 3 + j)).trans
          (hexagonal.id_le_bufferedRadius (N + 3 + j + 1))
      omega
    have hdom := triHexHexBufferedFaceDualInnerEvent_le_freeStar
      hNL hp hp1 hq hA
    rw [← freeBufferedMeasure_real_triHexFaceDualInnerEvent
      (show N + 3 ≤ L j + 2 by omega)
      hp hp1 (zero_lt_one.trans_le hq) A] at hdom
    simpa only [b, s] using hdom
  have hupper : ∀ j, s j ≤ b (k j) := by
    intro j
    have hkN : N + 3 ≤ k j := by dsimp only [k]; omega
    have hdom := freeOuterStar_le_triHexHexBufferedFaceDualInnerEvent
      hkN hp hp1 hq hA
    rw [← freeBufferedMeasure_real_triHexFaceDualInnerEvent
      hkN hp hp1 (zero_lt_one.trans_le hq) A] at hdom
    simpa only [L, k, s, b] using hdom
  have hs : Filter.Tendsto s Filter.atTop (nhds target) :=
    Filter.Tendsto.squeeze (hb.comp hLindex) (hb.comp hk) hlower hupper
  simpa only [s, L, k, target] using hs

end

end StatMech.FK.PeriodicPlanar
