/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierD.FKQgt4SquarePeriodicCoverageShells
import Code.FrontierD.FKQgt4SquareFiniteDuality
import Code.Lattice.EulerFaces

open Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK.PeriodicPlanar
open StatMech.Universality

noncomputable section


theorem sharedPrimalEdge_add (z f g : Site 2) :
    sharedPrimalEdge (f + z) (g + z) =
      Sym2.map (siteTranslate z) (sharedPrimalEdge f g) := by
  classical
  unfold sharedPrimalEdge
  simp only [Pi.add_apply, siteTranslate]
  by_cases h0 : f 0 = g 0
  · rw [if_pos h0, if_pos (by omega)]
    congr 1 <;> funext i <;> fin_cases i <;> simp <;> omega
  · rw [if_neg h0, if_neg (by omega)]
    congr 1 <;> funext i <;> fin_cases i <;> simp <;> omega


theorem fci_faceEdgeEquiv_mem_edgeSet (e : Sym2 (Site 2)) :
    e ∈ (hypercubicLattice 2).edgeSet ↔
      fci_faceEdgeEquiv e ∈ (hypercubicLattice 2).edgeSet := by
  constructor
  · intro he
    change (if _he : e ∈ (hypercubicLattice 2).edgeSet then
      (fci_latticeEdgeEquiv ⟨e, _he⟩ : Sym2 (Site 2)) else e) ∈
        (hypercubicLattice 2).edgeSet
    rw [dif_pos he]
    exact (fci_latticeEdgeEquiv ⟨e, he⟩).2
  · intro he
    by_contra hnot
    change (if _he : e ∈ (hypercubicLattice 2).edgeSet then
      (fci_latticeEdgeEquiv ⟨e, _he⟩ : Sym2 (Site 2)) else e) ∈
        (hypercubicLattice 2).edgeSet at he
    rw [dif_neg hnot] at he
    exact hnot he


theorem fci_faceEdgeEquiv_shift (z : Site 2) (e : Sym2 (Site 2)) :
    fci_faceEdgeEquiv (Sym2.map (siteTranslate z) e) =
      Sym2.map (siteTranslate z) (fci_faceEdgeEquiv e) := by
  induction e using Sym2.inductionOn with
  | _ f g =>
      by_cases hfg : (hypercubicLattice 2).Adj f g
      · have hshift : (hypercubicLattice 2).Adj
            (siteTranslate z f) (siteTranslate z g) :=
          (square.shift_adj z f g).2 hfg
        simp only [Sym2.map_mk]
        rw [fci_faceEdgeEquiv_mk_of_adj hshift,
          fci_faceEdgeEquiv_mk_of_adj hfg]
        exact sharedPrimalEdge_add z f g
      · have hnot : s(f, g) ∉ (hypercubicLattice 2).edgeSet := by
          simpa only [SimpleGraph.mem_edgeSet] using hfg
        have hshiftNot :
            s(siteTranslate z f, siteTranslate z g) ∉
              (hypercubicLattice 2).edgeSet := by
          rw [SimpleGraph.mem_edgeSet]
          exact fun h => hfg ((square.shift_adj z f g).1 h)
        change (if _h : s(siteTranslate z f, siteTranslate z g) ∈
            (hypercubicLattice 2).edgeSet then _ else _) = _
        rw [dif_neg hshiftNot]
        change s(siteTranslate z f, siteTranslate z g) =
          Sym2.map (siteTranslate z)
            (if _h : s(f, g) ∈ (hypercubicLattice 2).edgeSet then _ else _)
        rw [dif_neg hnot, Sym2.map_mk]



theorem dualConfigEquiv_fci_faceEdgeEquiv_eq_inverseFaceDualConfig :
    (dualConfigEquiv fci_faceEdgeEquiv :
      ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) =
      inverseFaceDualConfig := by
  ext omega e
  rfl

@[simp] theorem dualConfigEquiv_fci_faceEdgeEquiv_apply
    (omega : ConfigSpace (Sym2 (Site 2))) :
    dualConfigEquiv fci_faceEdgeEquiv omega = inverseFaceDualConfig omega := by
  rfl



theorem fkSquareBoxPlanar_dualVertex_card (n : Nat) :
    Nat.card (StatMech.Ising.kwg_Face (fkSquareBoxPlanar n)) =
      (2 * n) ^ 2 + 1 := by
  rw [StatMech.Ising.kwg_card_face_eq_faceCount]
  change faceCount (StatMech.FK.boxGraph 2 n) = (2 * n) ^ 2 + 1
  have hconn : (StatMech.FK.boxGraph 2 n).Connected := by
    simpa only [StatMech.FK.boxGraph, boxInduce, SimpleGraph.induce] using
      boxInduce_connected n
  rw [faceCount_eq_cyclomaticNumber_add_one hconn]
  have hge := connected_card_edges_ge hconn
  rw [StatMech.FK.EdgeCount.boxGraph_edgeCard 2 n (by omega),
    StatMech.FK.ecz_boxVerts_card] at hge
  unfold cyclomaticNumber
  rw [StatMech.FK.EdgeCount.boxGraph_edgeCard 2 n (by omega),
    StatMech.FK.ecz_boxVerts_card]
  ring_nf at hge ⊢
  omega



theorem not_nonempty_faithfulDual_equiv_centeredSquareBox
    {n : Nat} (hn : 0 < n) (m : Nat) :
    IsEmpty
      (StatMech.Ising.kwg_Face (fkSquareBoxPlanar n) ≃
        StatMech.FK.boxVerts 2 m) := by
  constructor
  intro e
  have hcard := Nat.card_congr e
  rw [fkSquareBoxPlanar_dualVertex_card,
    Nat.card_eq_fintype_card, StatMech.FK.ecz_boxVerts_card] at hcard
  have hlt : 2 * n < 2 * m + 1 := by
    by_contra hnot
    have hle : 2 * m + 1 ≤ 2 * n := by omega
    have hp := Nat.pow_le_pow_left hle 2
    omega
  have hupper : 2 * m + 1 ≤ 2 * n + 1 := by
    by_contra hnot
    have hle : 2 * n + 2 ≤ 2 * m + 1 := by omega
    have hp := Nat.pow_le_pow_left hle 2
    nlinarith
  have heq : 2 * m + 1 = 2 * n + 1 := by omega
  rw [heq] at hcard
  nlinarith

end

end StatMech.FrontierD
