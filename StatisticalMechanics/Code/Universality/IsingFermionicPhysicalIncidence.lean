/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalLocalClosed










namespace StatMech.Universality

open Finset Complex SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWired_incidence_infix_explorationOrder
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (h : (.dart d : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn omega) :
    [(.dart d : FKIsingSquareWiredCarrier n), .bond d] <:+:
        fkIsingSquareWiredExplorationOrder n hn omega ∨
      [(.bond d : FKIsingSquareWiredCarrier n), .dart d] <:+:
        fkIsingSquareWiredExplorationOrder n hn omega := by
  have hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj
      (.dart d) (.bond d) := by
    exact Or.inl ⟨by simp, by simp, rfl⟩
  apply Walk.infix_support_iff_mem_edges.mpr
  exact fkIsingSquareWiredExplorationPath_mem_edges_of_adj n hn omega h hadj


theorem fkIsingSquareWiredRawTurnCount_incidence
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (h : (.dart d : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn omega) :
    fkIsingSquareWiredRawTurnCount n hn omega (.bond d) =
      fkIsingSquareWiredRawTurnCount n hn omega (.dart d) := by
  let p := fkIsingSquareWiredExplorationOrder n hn omega
  let x : FKIsingSquareWiredCarrier n := .dart d
  let y : FKIsingSquareWiredCarrier n := .bond d
  have hxy := fkIsingSquareWired_incidence_infix_explorationOrder
    n hn omega d h
  have hx : x ∈ p := by simpa [x, p] using h
  have hy : y ∈ p := hxy.elim
    (fun hf ↦ hf.mem (by simp [y]))
    (fun hb ↦ hb.mem (by simp [y]))
  have hix : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : p.idxOf y < p.length := List.idxOf_lt_length_iff.mpr hy
  rcases hxy with hf | hb
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hf
    have hs := fkIsingSquareWiredRawTurnCount_succ n hn omega (p.idxOf x)
      (by rw [← hi]; exact hiy)
    simpa only [p, x, y, List.getElem_idxOf hix, ← hi,
      List.getElem_idxOf hiy, fkIsingSquareWiredTransitionTurn,
      add_zero] using hs
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hb
    have hs := fkIsingSquareWiredRawTurnCount_succ n hn omega (p.idxOf y)
      (by rw [← hi]; exact hix)
    have hs' : fkIsingSquareWiredRawTurnCount n hn omega (.dart d) =
        fkIsingSquareWiredRawTurnCount n hn omega (.bond d) := by
      simpa only [p, x, y, List.getElem_idxOf hiy, ← hi,
        List.getElem_idxOf hix, fkIsingSquareWiredTransitionTurn,
        add_zero] using hs
    exact hs'.symm

theorem fkIsingSquareWiredLiftedWinding_incidence
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (h : (.dart d : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn omega) :
    fkIsingSquareWiredLiftedWinding n hn omega (.bond d) =
      fkIsingSquareWiredLiftedWinding n hn omega (.dart d) := by
  simp only [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount,
    fkIsingSquareWiredRawTurnCount_incidence n hn omega d h]

theorem fkIsingSquareWired_incidence_mem_trace_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (.bond d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn omega ↔
      (.dart d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn omega := by
  rw [mem_fkIsingSquareWiredExplorationTrace_iff,
    mem_fkIsingSquareWiredExplorationTrace_iff]
  have hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj
      (.dart d) (.bond d) := Or.inl ⟨by simp, by simp, rfl⟩
  exact ⟨fun h ↦ h.trans hadj.symm.reachable,
    fun h ↦ h.trans hadj.reachable⟩

theorem fkIsingSquareWired_fermionicSummand_incidence
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega (.bond d) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
        (.dart d) := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  have hmem := fkIsingSquareWired_incidence_mem_trace_iff n hn omega d
  by_cases hd : (.dart d : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn omega
  · have hb := hmem.mpr hd
    have horder : (.dart d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationOrder n hn omega := by
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact hd
    have hwind := fkIsingSquareWiredLiftedWinding_incidence
      n hn omega d horder
    simp only [FKIsingDobrushinDomain.fermionicSummand, D,
      fkIsingSquareWiredDobrushinDomain, hb, hd, if_true,
      FKIsingDobrushinDomain.windingPhase]
    rw [hwind]
  · have hb : (.bond d : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn omega := by
      exact fun h ↦ hd (hmem.mp h)
    simp [FKIsingDobrushinDomain.fermionicSummand, D,
      fkIsingSquareWiredDobrushinDomain, hb, hd]


theorem fkIsingSquareWired_fermionicObservable_incidence
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.bond d) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart d) := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  apply Finset.sum_congr rfl
  intro omega _
  exact fkIsingSquareWired_fermionicSummand_incidence n hn omega d

theorem fkIsingSquareWiredPrimitiveIncrement_incidence
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredPrimitiveIncrement n hn (.bond d) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart d) := by
  unfold fkIsingSquareWiredPrimitiveIncrement
  rw [fkIsingSquareWired_fermionicObservable_incidence]

end

end StatMech.Universality
