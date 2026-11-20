/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierD.FKMedialLoopTurningFiber
import Code.FrontierD.FKMedialBoundaryPermutation
import Code.FrontierD.FKMedialBoundaryToggleParity
import Code.Onsager.PeriodicTurnClosure

open Equiv
namespace StatMech.FrontierD
open StatMech.Onsager
open FKMedialTurningFiber

variable {T : EvenTorus}

def fkMedialStrandDirection (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) : Fin 4 :=
  match pairing d.1, d.2 with
  | false, .west | false, .south => 0
  | false, .east | false, .north => 2
  | true, .west | true, .north => 1
  | true, .east | true, .south => 3

theorem two_mul_turnPow_strandDirection
    (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) :
    2 * ons_turnPow (fkMedialStrandDirection pairing d.1)
        (fkMedialStrandDirection pairing
          (fkMedialBlackBoundaryPerm pairing d).1) =
      -(turnSign (pairing d.1.1) (fkMedialVertexParity d.1.1) +
        turnSign (pairing (fkMedialBlackBoundaryPerm pairing d).1.1)
          (fkMedialVertexParity
            (fkMedialBlackBoundaryPerm pairing d).1.1)) := by
  rcases d with ⟨⟨⟨i, j⟩, side⟩, hd⟩
  cases hp : pairing (i, j) <;> cases side
  all_goals simp [fkMedialCheckerColor, fkMedialSideVertical] at hd
  all_goals simp only [fkMedialBlackBoundaryPerm_val, fkMedialLocalMate,
    fkMedialBondMate, hp, fkMedialStrandDirection]
  all_goals generalize hq : pairing _ = q
  all_goals cases q
  all_goals simp_all [ons_turnPow, turnSign]

noncomputable def blackComponentTurn
    (pairing : FKMedialLoopPairing T) (C : FKMedialLoop T pairing) : Int := by
  classical
  exact ∑ d : FKMedialBlackDart T,
    if (fkMedialLoopGraph T pairing).connectedComponentMk d.1 = C then
      turnSign (pairing d.1.1) (fkMedialVertexParity d.1.1)
    else 0

theorem connectedComponentMk_localMate
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialLocalMate pairing d) =
      (fkMedialLoopGraph T pairing).connectedComponentMk d := by
  apply SimpleGraph.ConnectedComponent.sound
  exact (show (fkMedialLoopGraph T pairing).Adj
    (fkMedialLocalMate pairing d) d by
      rw [fkMedialLoopGraph_adj_iff]
      left
      rw [fkMedialLocalMate_involutive]).reachable

theorem canonicalComponentTurn_eq_blackComponentTurn
    (pairing : FKMedialLoopPairing T) (C : FKMedialLoop T pairing) :
    canonicalComponentTurn pairing C = blackComponentTurn pairing C := by
  classical
  unfold canonicalComponentTurn componentTurn blackComponentTurn
  simp_rw [incoming_arrowsOfMode]
  simp only [modeIncoming, Bool.false_eq_true, if_false]
  let f : FKMedialBlackDart T → Int := fun d =>
    if (fkMedialLoopGraph T pairing).connectedComponentMk d.1 = C then
      turnSign (pairing d.1.1) (fkMedialVertexParity d.1.1)
    else 0
  let g : T.Vertex × Bool → Int := fun vb =>
    if (fkMedialLoopGraph T pairing).connectedComponentMk
        ((fkMedialBlackDartEquivVertexBool T).symm vb).1 = C then
      turnSign (pairing vb.1) (fkMedialVertexParity vb.1)
    else 0
  have hequiv : (∑ d : FKMedialBlackDart T, f d) =
      ∑ vb : T.Vertex × Bool, g vb := by
    apply Fintype.sum_equiv (fkMedialBlackDartEquivVertexBool T)
    intro d
    change f d = g ((fkMedialBlackDartEquivVertexBool T) d)
    unfold g
    rw [(fkMedialBlackDartEquivVertexBool T).symm_apply_apply]
    rfl
  have hprod : (∑ vb : T.Vertex × Bool, g vb) =
      ∑ v : T.Vertex, ∑ b : Bool, g (v, b) :=
    Fintype.sum_prod_type g
  change _ = ∑ d : FKMedialBlackDart T, f d
  rw [hequiv, hprod]
  apply Finset.sum_congr rfl
  intro v hv
  have hwest := connectedComponentMk_localMate pairing (v, .west)
  have heast := connectedComponentMk_localMate pairing (v, .east)
  cases hp : pairing v <;> cases hvp : fkMedialVertexParity v
  all_goals
    have hwest' := hwest
    have heast' := heast
    simp only [fkMedialLocalMate, hp] at hwest' heast'
    rw [Fintype.sum_bool]
    simp [g, fkMedialBlackDartEquivVertexBool,
      fkMedialBlackDart0, fkMedialBlackDart1, hvp,
      turnSign, hp, fkMedialCheckerColor, fkMedialSideVertical,
      hwest', heast', add_comm]

theorem fkMedialBlackBoundaryPerm_apply_ne
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    fkMedialBlackBoundaryPerm pairing d ≠ d := by
  intro h
  have hs := congrArg (fun e : FKMedialBlackDart T => e.1.2) h
  rcases d with ⟨⟨v, side⟩, hd⟩
  cases hp : pairing v <;> cases side <;>
    simp [fkMedialBlackBoundaryPerm_val, fkMedialLocalMate,
      fkMedialBondMate, hp] at hs

private theorem list_sum_map_eq_sum_toFinset
    {α : Type*} [DecidableEq α] (l : List α) (f : α → Int)
    (hl : l.Nodup) :
    (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.nodup_cons] at hl
      simp [hl.1, ih hl.2]

theorem canonicalComponentTurn_eq_toList_sum
    (pairing : FKMedialLoopPairing T) (C : FKMedialLoop T pairing)
    (d : FKMedialBlackDart T)
    (hdC : (fkMedialLoopGraph T pairing).connectedComponentMk d.1 = C) :
    canonicalComponentTurn pairing C =
      (((fkMedialBlackBoundaryPerm pairing).toList d).map
        (fun e : FKMedialBlackDart T => turnSign (pairing e.1.1)
          (fkMedialVertexParity e.1.1))).sum := by
  classical
  rw [canonicalComponentTurn_eq_blackComponentTurn]
  unfold blackComponentTurn
  let p := fkMedialBlackBoundaryPerm pairing
  let l := p.toList d
  let f : FKMedialBlackDart T → Int := fun e =>
    turnSign (pairing e.1.1) (fkMedialVertexParity e.1.1)
  have hsupport : d ∈ p.support := by
    rw [Equiv.Perm.mem_support]
    exact fkMedialBlackBoundaryPerm_apply_ne pairing d
  have hmem (e : FKMedialBlackDart T) :
      e ∈ l ↔
        (fkMedialLoopGraph T pairing).connectedComponentMk e.1 = C := by
    rw [show e ∈ l ↔ p.SameCycle d e ∧ d ∈ p.support by
      exact Equiv.Perm.mem_toList_iff]
    rw [and_iff_left hsupport,
      fkMedial_blackBoundary_sameCycle_iff_reachable]
    constructor
    · intro h
      rw [← hdC]
      exact SimpleGraph.ConnectedComponent.sound h.symm
    · intro h
      apply SimpleGraph.ConnectedComponent.exact
      rw [hdC]
      exact h.symm
  have hfin : l.toFinset = Finset.univ.filter (fun e =>
      (fkMedialLoopGraph T pairing).connectedComponentMk e.1 = C) := by
    ext e
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hmem e
  have hsum := list_sum_map_eq_sum_toFinset l f
    (Equiv.Perm.nodup_toList p d)
  rw [hfin] at hsum
  change (∑ e : FKMedialBlackDart T,
      if (fkMedialLoopGraph T pairing).connectedComponentMk e.1 = C
      then f e else 0) = (l.map f).sum
  rw [← Finset.sum_filter]
  exact hsum.symm

set_option maxHeartbeats 800000 in

theorem cyclicTurnSum_toList_strandDirections
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    ons_cyclicTurnSum
        (((fkMedialBlackBoundaryPerm pairing).toList d).map
          (fun e : FKMedialBlackDart T =>
            fkMedialStrandDirection pairing e.1)) =
      -(((fkMedialBlackBoundaryPerm pairing).toList d).map
          (fun e : FKMedialBlackDart T => turnSign (pairing e.1.1)
            (fkMedialVertexParity e.1.1)) |>.sum) := by
  classical
  let p := fkMedialBlackBoundaryPerm pairing
  let l := p.toList d
  have hsupport : d ∈ p.support := by
    rw [Equiv.Perm.mem_support]
    exact fkMedialBlackBoundaryPerm_apply_ne pairing d
  have hdmem : d ∈ l := by
    rw [Equiv.Perm.mem_toList_iff]
    exact ⟨Equiv.Perm.SameCycle.refl p d, hsupport⟩
  have hlen : 0 < l.length := by
    by_contra h
    have hlzero : l.length = 0 := by omega
    have hlnil : l = [] := List.eq_nil_of_length_eq_zero hlzero
    rw [hlnil] at hdmem
    simp at hdmem
  letI : NeZero l.length := ⟨hlen.ne'⟩
  let dir : Fin l.length → Fin 4 := fun i =>
    fkMedialStrandDirection pairing (l.get i).1
  let c : Fin l.length → Int := fun i =>
    turnSign (pairing (l.get i).1.1)
      (fkMedialVertexParity (l.get i).1.1)
  have hl : l.Nodup := Equiv.Perm.nodup_toList p d
  have hnext (i : Fin l.length) : l.get (i + 1) = p (l.get i) := by
    have hnextList := List.next_getElem l hl i.val i.isLt
    have happly := Equiv.Perm.next_toList_eq_apply p d (l.get i)
      (List.get_mem l i)
    have happly' : l.next l[i.val] (by
        exact List.getElem_mem (l := l) i.isLt) = p l[i.val] := by
      simpa [List.get_eq_getElem] using happly
    rw [happly'] at hnextList
    have hiv : (i + 1).val = (i.val + 1) % l.length := by
      simp [Fin.val_add, Nat.add_mod]
    simpa only [List.get_eq_getElem, hiv] using hnextList.symm
  have hlocal (i : Fin l.length) :
      2 * ons_turnPow (dir i) (dir (i + 1)) = -(c i + c (i + 1)) := by
    unfold dir c
    rw [hnext]
    exact two_mul_turnPow_strandDirection pairing (l.get i)
  have hcyc : ons_cyclicTurnSum (List.ofFn dir) =
      ∑ i, ons_turnPow (dir i) (dir (i + 1)) :=
    ons_cyclicTurnSum_ofFn' dir
  have hshift : (∑ i, c (i + 1)) = ∑ i, c i :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin l.length)) c
  have hdouble : 2 * ons_cyclicTurnSum (List.ofFn dir) =
      -2 * ∑ i, c i := by
    rw [hcyc, Finset.mul_sum]
    simp_rw [hlocal]
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, hshift]
    ring
  have hdirs : List.ofFn dir = l.map (fun e : FKMedialBlackDart T =>
      fkMedialStrandDirection pairing e.1) := by
    simpa [dir, List.get_eq_getElem] using
      (List.ofFn_getElem_eq_map l (fun e : FKMedialBlackDart T =>
        fkMedialStrandDirection pairing e.1))
  have hcsum : (∑ i, c i) =
      (l.map (fun e => turnSign (pairing e.1.1)
        (fkMedialVertexParity e.1.1))).sum := by
    rw [← List.sum_ofFn]
    exact congrArg List.sum (by
      simpa [c, List.get_eq_getElem] using
        (List.ofFn_getElem_eq_map l (fun e : FKMedialBlackDart T =>
          turnSign (pairing e.1.1) (fkMedialVertexParity e.1.1))))
  rw [hdirs, hcsum] at hdouble
  change ons_cyclicTurnSum
      (l.map (fun e : FKMedialBlackDart T =>
        fkMedialStrandDirection pairing e.1)) =
    -(l.map (fun e : FKMedialBlackDart T =>
      turnSign (pairing e.1.1) (fkMedialVertexParity e.1.1))).sum
  omega

end StatMech.FrontierD
