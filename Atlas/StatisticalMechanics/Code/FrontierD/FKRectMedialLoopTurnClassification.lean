/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierD.FKRectMedialLoopTurnGeometry

open Equiv Finset
namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase
open FKMedialTurningFiber

noncomputable section

variable {T : EvenTorus}

theorem fkMedialBlackBoundaryPerm_iterate_val
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    (n : Nat) :
    (((fkMedialBlackBoundaryPerm pairing)^[n] d).1) =
      (fkMedialBoundaryStep pairing)^[n] d.1 := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply]
      rw [ih, fkMedialBlackBoundaryPerm_val_step]

theorem fkRectRefinedBoundaryCenterAfter_succ_right
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T)
    (c : Int × Int) (n : Nat) :
    fkRectRefinedBoundaryCenterAfter pairing d c (n + 1) =
      fkRectRefinedBondCenter
        (fkRectRefinedBoundaryCenterAfter pairing d c n)
        (fkMedialLocalMate pairing
          ((fkMedialBoundaryStep pairing)^[n] d)).2 := by
  induction n generalizing d c with
  | zero => rfl
  | succ n ih =>
      simp only [fkRectRefinedBoundaryCenterAfter,
        Function.iterate_succ_apply]
      exact ih (fkMedialBoundaryStep pairing d)
        (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2)

def fkRectBlackBoundaryPointAfter
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) (n : Nat) : Int × Int :=
  fkRectRefinedDartPoint
    (fkRectRefinedBoundaryCenterAfter pairing d.1
      (fkRectRefinedBoundaryCanonicalCenter R d.1) n)
    (((fkMedialBlackBoundaryPerm pairing)^[n] d).1.2)

theorem fkRectBlackBoundaryPointAfter_succ
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) (n : Nat) :
    fkRectBlackBoundaryPointAfter R pairing d (n + 1) =
      ((fkRectBlackBoundaryPointAfter R pairing d n).1 +
          2 * ons_dirExponentX
            (fkMedialStrandDirection pairing
              ((fkMedialBlackBoundaryPerm pairing)^[n] d).1),
        (fkRectBlackBoundaryPointAfter R pairing d n).2 +
          2 * ons_dirExponentY
            (fkMedialStrandDirection pairing
              ((fkMedialBlackBoundaryPerm pairing)^[n] d).1)) := by
  unfold fkRectBlackBoundaryPointAfter
  rw [fkRectRefinedBoundaryCenterAfter_succ_right]
  rw [fkMedialBlackBoundaryPerm_iterate_val pairing d n,
    fkMedialBlackBoundaryPerm_iterate_val pairing d (n + 1)]
  rw [Function.iterate_succ_apply']
  exact fkRectRefinedBoundaryStep_point pairing
    ((fkMedialBoundaryStep pairing)^[n] d.1)
    (fkRectRefinedBoundaryCenterAfter pairing d.1
      (fkRectRefinedBoundaryCanonicalCenter R d.1) n)

def fkRectBlackOrbitList
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    List (FKMedialBlackDart T) :=
  (fkMedialBlackBoundaryPerm pairing).toList d

theorem fkRectBlackOrbitList_mem_self
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    d ∈ fkRectBlackOrbitList pairing d := by
  rw [fkRectBlackOrbitList, Equiv.Perm.mem_toList_iff]
  exact ⟨Equiv.Perm.SameCycle.refl _ _, by
    rw [Equiv.Perm.mem_support]
    exact fkMedialBlackBoundaryPerm_apply_ne pairing d⟩

theorem fkRectBlackOrbitList_length_pos
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    0 < (fkRectBlackOrbitList pairing d).length := by
  by_contra h
  have hzero : (fkRectBlackOrbitList pairing d).length = 0 := by omega
  have hnil : fkRectBlackOrbitList pairing d = [] :=
    List.eq_nil_of_length_eq_zero hzero
  have hmem := fkRectBlackOrbitList_mem_self pairing d
  rw [hnil] at hmem
  simp at hmem

theorem fkRectBlackOrbitList_get
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    (i : Fin (fkRectBlackOrbitList pairing d).length) :
    (fkRectBlackOrbitList pairing d).get i =
      (fkMedialBlackBoundaryPerm pairing)^[i.val] d := by
  change (fkRectBlackOrbitList pairing d).get i =
    ((fkMedialBlackBoundaryPerm pairing) ^ i.val) d
  simpa [fkRectBlackOrbitList, List.get_eq_getElem] using
    Equiv.Perm.getElem_toList (fkMedialBlackBoundaryPerm pairing)
      d i.val i.isLt

def fkRectBlackOrbitDirection
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    (i : Fin (fkRectBlackOrbitList pairing d).length) : Fin 4 :=
  fkMedialStrandDirection pairing
    ((fkRectBlackOrbitList pairing d).get i).1

def fkRectBlackOrbitPrefix
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    (n : Nat) : Int × Int :=
  ∑ k ∈ Finset.range n,
    stepOf (fkMedialStrandDirection pairing
      ((fkMedialBlackBoundaryPerm pairing)^[k] d).1)

@[simp] theorem fkRectBlackOrbitPrefix_zero
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    fkRectBlackOrbitPrefix pairing d 0 = 0 := by
  simp [fkRectBlackOrbitPrefix]

theorem fkRectBlackOrbitPrefix_succ
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    (n : Nat) :
    fkRectBlackOrbitPrefix pairing d (n + 1) =
      fkRectBlackOrbitPrefix pairing d n +
        stepOf (fkMedialStrandDirection pairing
          ((fkMedialBlackBoundaryPerm pairing)^[n] d).1) := by
  rw [fkRectBlackOrbitPrefix, fkRectBlackOrbitPrefix,
    Finset.sum_range_succ]

theorem fkRectBlackBoundaryPointAfter_eq_prefix
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) (n : Nat) :
    fkRectBlackBoundaryPointAfter R pairing d n =
      fkRectBlackBoundaryPointAfter R pairing d 0 +
        2 • fkRectBlackOrbitPrefix pairing d n := by
  induction n with
  | zero => simp
  | succ n ih =>
      let e := fkMedialStrandDirection pairing
        ((fkMedialBlackBoundaryPerm pairing)^[n] d).1
      calc
        fkRectBlackBoundaryPointAfter R pairing d (Nat.succ n) =
            fkRectBlackBoundaryPointAfter R pairing d n +
              2 • stepOf e := by
          rw [show Nat.succ n = n + 1 by omega,
            fkRectBlackBoundaryPointAfter_succ,
            ons_stepOf_eq_exponents]
          apply Prod.ext <;> simp [e]
        _ = (fkRectBlackBoundaryPointAfter R pairing d 0 +
              2 • fkRectBlackOrbitPrefix pairing d n) +
              2 • stepOf e := by rw [ih]
        _ = fkRectBlackBoundaryPointAfter R pairing d 0 +
              2 • fkRectBlackOrbitPrefix pairing d (Nat.succ n) := by
          rw [show Nat.succ n = n + 1 by omega,
            fkRectBlackOrbitPrefix_succ, nsmul_add]
          abel

theorem fkRectBlackOrbitPrefix_eq_pos
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    [NeZero (fkRectBlackOrbitList pairing d).length]
    (i : Fin (fkRectBlackOrbitList pairing d).length) :
    fkRectBlackOrbitPrefix pairing d i.val =
      pos (fkRectBlackOrbitDirection pairing d) i := by
  unfold fkRectBlackOrbitPrefix pos
  apply Finset.sum_bij (fun k hk =>
    ⟨k, (Finset.mem_range.mp hk).trans i.isLt⟩)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    exact Finset.mem_range.mp hk
  · intro a ha b hb hab
    exact congrArg Fin.val hab
  · intro j hj
    have hji : j.val < i.val := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
        using hj
    refine ⟨j.val, Finset.mem_range.mpr hji, ?_⟩
    exact Fin.ext rfl
  · intro k hk
    simp only [fkRectBlackOrbitDirection, fkRectBlackOrbitList_get]

theorem fkRectBlackOrbitPrefix_length_eq_displacement
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    fkRectBlackOrbitPrefix pairing d
        (fkRectBlackOrbitList pairing d).length =
      ons_pathDisplacement
        (List.ofFn (fkRectBlackOrbitDirection pairing d)) := by
  rw [ons_pathDisplacement_ofFn, fkRectBlackOrbitPrefix]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp only [fkRectBlackOrbitDirection, fkRectBlackOrbitList_get]

theorem fkRectBlackBoundaryPerm_pow_length_apply
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    (fkMedialBlackBoundaryPerm pairing)^[
        (fkRectBlackOrbitList pairing d).length] d = d := by
  let p := fkMedialBlackBoundaryPerm pairing
  have hd : p d ≠ d := fkMedialBlackBoundaryPerm_apply_ne pairing d
  change (p ^ (p.toList d).length) d = d
  rw [Equiv.Perm.length_toList,
    ← (Equiv.Perm.isCycle_cycleOf p hd).orderOf,
    ← Equiv.Perm.cycleOf_pow_apply_self,
    pow_orderOf_eq_one, Equiv.Perm.one_apply]

@[simp] theorem fkRectBlackBoundaryPointAfter_zero
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackBoundaryPointAfter R pairing d 0 =
      fkRectBlackDartShiftedPoint R (0, 0) d := by
  simp [fkRectBlackBoundaryPointAfter, fkRectBlackDartShiftedPoint,
    fkRectRefinedBoundaryCenterAfter, fkRectSquareDeckTranslation]

def fkRectBlackDeckPointShift (R : FKRectTorus) (u : Int × Int) :
    Int × Int :=
  (4 * (fkRectSquareDeckTranslation R u).1,
    4 * (fkRectSquareDeckTranslation R u).2)

theorem fkRectBlackDeckPointShift_nsmul
    (R : FKRectTorus) (r : Nat) (u : Int × Int) :
    fkRectBlackDeckPointShift R (r • u) =
      r • fkRectBlackDeckPointShift R u := by
  apply Prod.ext <;>
    simp [fkRectBlackDeckPointShift, fkRectSquareDeckTranslation] <;> ring

theorem fkRectBlackDartShiftedPoint_add
    (R : FKRectTorus) (u v : Int × Int)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackDartShiftedPoint R (u + v) d =
      fkRectBlackDartShiftedPoint R u d +
        fkRectBlackDeckPointShift R v := by
  apply Prod.ext <;>
    simp [fkRectBlackDartShiftedPoint, fkRectRefinedDartPoint,
      fkRectBlackDeckPointShift, fkRectSquareDeckTranslation] <;> ring

theorem fkRectBlackBoundaryPointAfter_exists_shiftedPoint
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) (n : Nat) :
    ∃ u : Int × Int,
      fkRectBlackBoundaryPointAfter R pairing d n =
        fkRectBlackDartShiftedPoint R u
          ((fkMedialBlackBoundaryPerm pairing)^[n] d) := by
  obtain ⟨u, hu⟩ := fkRectRefinedBoundaryCenterAfter_exists_deck
    R pairing d.1 n
  refine ⟨u, ?_⟩
  unfold fkRectBlackBoundaryPointAfter fkRectBlackDartShiftedPoint
  rw [hu, fkMedialBlackBoundaryPerm_iterate_val pairing d n]

theorem fkRectBlackOrbit_pos_injective
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus)
    [NeZero (fkRectBlackOrbitList pairing d).length] :
    Function.Injective (pos (fkRectBlackOrbitDirection pairing d)) := by
  intro i j hij
  have hi := fkRectBlackBoundaryPointAfter_eq_prefix R pairing d i.val
  have hj := fkRectBlackBoundaryPointAfter_eq_prefix R pairing d j.val
  rw [fkRectBlackOrbitPrefix_eq_pos pairing d i, hij] at hi
  rw [fkRectBlackOrbitPrefix_eq_pos pairing d j] at hj
  have hpoint : fkRectBlackBoundaryPointAfter R pairing d i.val =
      fkRectBlackBoundaryPointAfter R pairing d j.val := hi.trans hj.symm
  obtain ⟨u, hu⟩ :=
    fkRectBlackBoundaryPointAfter_exists_shiftedPoint R pairing d i.val
  obtain ⟨v, hv⟩ :=
    fkRectBlackBoundaryPointAfter_exists_shiftedPoint R pairing d j.val
  have huv : (u, (fkMedialBlackBoundaryPerm pairing)^[i.val] d) =
      (v, (fkMedialBlackBoundaryPerm pairing)^[j.val] d) := by
    apply fkRectBlackDartShiftedPoint_injective R
    change fkRectBlackDartShiftedPoint R u
        ((fkMedialBlackBoundaryPerm pairing)^[i.val] d) =
      fkRectBlackDartShiftedPoint R v
        ((fkMedialBlackBoundaryPerm pairing)^[j.val] d)
    rw [← hu, ← hv]
    exact hpoint
  have hdart : (fkMedialBlackBoundaryPerm pairing)^[i.val] d =
      (fkMedialBlackBoundaryPerm pairing)^[j.val] d :=
    congrArg Prod.snd huv
  apply (Equiv.Perm.nodup_toList
    (fkMedialBlackBoundaryPerm pairing) d).get_inj_iff.mp
  change (fkRectBlackOrbitList pairing d).get i =
    (fkRectBlackOrbitList pairing d).get j
  rw [fkRectBlackOrbitList_get pairing d i,
    fkRectBlackOrbitList_get pairing d j]
  exact hdart

theorem fkMedialStrandDirection_blackBoundaryPerm_ne_add_two
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    fkMedialStrandDirection pairing
        (fkMedialBlackBoundaryPerm pairing d).1 ≠
      fkMedialStrandDirection pairing d.1 + 2 := by
  rcases d with ⟨⟨⟨i, j⟩, side⟩, hd⟩
  cases hp : pairing (i, j) <;> cases side
  all_goals simp [fkMedialCheckerColor, fkMedialSideVertical] at hd
  all_goals simp only [fkMedialBlackBoundaryPerm_val,
    fkMedialLocalMate, fkMedialBondMate, hp,
    fkMedialStrandDirection]
  all_goals generalize hq : pairing _ = q
  all_goals cases q <;> decide

theorem fkRectBlackOrbitDirection_nonUturn
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    [NeZero (fkRectBlackOrbitList pairing d).length]
    (i : Fin (fkRectBlackOrbitList pairing d).length) :
    fkRectBlackOrbitDirection pairing d (i + 1) ≠
      fkRectBlackOrbitDirection pairing d i + 2 := by
  let l := fkRectBlackOrbitList pairing d
  let p := fkMedialBlackBoundaryPerm pairing
  have hl : l.Nodup := Equiv.Perm.nodup_toList p d
  have hnext (k : Fin l.length) : l.get (k + 1) = p (l.get k) := by
    have hnextList := List.next_getElem l hl k.val k.isLt
    have happly := Equiv.Perm.next_toList_eq_apply p d (l.get k)
      (List.get_mem l k)
    have happly' : l.next l[k.val] (by
        exact List.getElem_mem (l := l) k.isLt) = p l[k.val] := by
      simpa [l, p, List.get_eq_getElem] using happly
    rw [happly'] at hnextList
    have hkv : (k + 1).val = (k.val + 1) % l.length := by
      simp [Fin.val_add, Nat.add_mod]
    simpa only [List.get_eq_getElem, hkv] using hnextList.symm
  change fkMedialStrandDirection pairing
      (((fkRectBlackOrbitList pairing d).get (i + 1)).1) ≠ _
  rw [hnext i]
  exact fkMedialStrandDirection_blackBoundaryPerm_ne_add_two
    pairing ((fkRectBlackOrbitList pairing d).get i)

private theorem two_direction_closed_opposite
    (dir : Fin 2 → Fin 4)
    (hclosed : ∑ i, stepOf (dir i) = 0) :
    dir 1 = dir 0 + 2 := by
  generalize h0 : dir 0 = a at hclosed ⊢
  generalize h1 : dir 1 = b at hclosed ⊢
  fin_cases a <;> fin_cases b <;>
    simp [h0, h1, stepOf] at hclosed ⊢

theorem ons_three_le_of_two_le_of_closed_of_nonUturn
    {n : Nat} [NeZero n] (dir : Fin n → Fin 4)
    (htwo : 2 ≤ n)
    (hclosed : ons_pathDisplacement (List.ofFn dir) = 0)
    (hnu : ∀ i : Fin n, dir (i + 1) ≠ dir i + 2) :
    3 ≤ n := by
  by_contra hthree
  have hn : n = 2 := by omega
  subst n
  have hsum : ∑ i, stepOf (dir i) = 0 := by
    rw [← ons_pathDisplacement_ofFn]
    exact hclosed
  exact hnu 0 (two_direction_closed_opposite dir hsum)

theorem fkRectBlackOrbit_contractible_cyclicTurnSum
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus)
    (hclosed : ons_pathDisplacement
      (List.ofFn (fkRectBlackOrbitDirection pairing d)) = 0) :
    ons_cyclicTurnSum
          (List.ofFn (fkRectBlackOrbitDirection pairing d)) = 4 ∨
      ons_cyclicTurnSum
          (List.ofFn (fkRectBlackOrbitDirection pairing d)) = -4 := by
  let l := fkRectBlackOrbitList pairing d
  have hsupport : d ∈ (fkMedialBlackBoundaryPerm pairing).support := by
    rw [Equiv.Perm.mem_support]
    exact fkMedialBlackBoundaryPerm_apply_ne pairing d
  have htwo : 2 ≤ l.length := by
    exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hsupport
  letI : NeZero l.length := ⟨by omega⟩
  let dir := fkRectBlackOrbitDirection pairing d
  have hnu : ∀ i : Fin l.length, dir (i + 1) ≠ dir i + 2 :=
    fkRectBlackOrbitDirection_nonUturn pairing d
  have hlen : 3 ≤ l.length :=
    ons_three_le_of_two_le_of_closed_of_nonUturn dir htwo hclosed hnu
  have hsum : ∑ i, stepOf (dir i) = 0 := by
    rw [← ons_pathDisplacement_ofFn]
    exact hclosed
  have hturn := GeneralUmlaufsatz.turnSum_eq_four_or_neg_four
    dir hsum (fkRectBlackOrbit_pos_injective R pairing d) hlen hnu
  rw [← ons_cyclicTurnSum_ofFn'] at hturn
  exact hturn

theorem fkRectBlackOrbit_periodState_exists_shiftedPoint
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus)
    [NeZero (fkRectBlackOrbitList pairing d).length]
    (z : Nat × Fin (fkRectBlackOrbitList pairing d).length) :
    ∃ u : Int × Int,
      fkRectBlackDartShiftedPoint R u
          ((fkMedialBlackBoundaryPerm pairing)^[z.2.val] d) =
        fkRectBlackBoundaryPointAfter R pairing d 0 +
          2 • ons_periodStateCoord
            (fkRectBlackOrbitDirection pairing d) z := by
  let l := fkRectBlackOrbitList pairing d
  let dir := fkRectBlackOrbitDirection pairing d
  let D := ons_pathDisplacement (List.ofFn dir)
  obtain ⟨w, hw⟩ := fkRectBlackBoundaryPointAfter_exists_shiftedPoint
    R pairing d l.length
  have hp := fkRectBlackBoundaryPerm_pow_length_apply pairing d
  change (fkMedialBlackBoundaryPerm pairing)^[l.length] d = d at hp
  rw [hp] at hw
  have hend := fkRectBlackBoundaryPointAfter_eq_prefix
    R pairing d l.length
  have hprefix := fkRectBlackOrbitPrefix_length_eq_displacement pairing d
  change fkRectBlackOrbitPrefix pairing d l.length = D at hprefix
  rw [hprefix] at hend
  have hw' : fkRectBlackDartShiftedPoint R w d =
      fkRectBlackBoundaryPointAfter R pairing d 0 + 2 • D :=
    hw.symm.trans hend
  have hadd0 := fkRectBlackDartShiftedPoint_add R (0, 0) w d
  have hzero : ((0, 0) : Int × Int) = 0 := rfl
  rw [hzero, zero_add] at hadd0
  have hadd0' : fkRectBlackDartShiftedPoint R w d =
      fkRectBlackBoundaryPointAfter R pairing d 0 +
        fkRectBlackDeckPointShift R w := by
    simpa only [fkRectBlackBoundaryPointAfter_zero] using hadd0
  have hshift : fkRectBlackDeckPointShift R w = 2 • D := by
    apply add_left_cancel
    exact hadd0'.symm.trans hw'
  obtain ⟨u, hu⟩ := fkRectBlackBoundaryPointAfter_exists_shiftedPoint
    R pairing d z.2.val
  have hi := fkRectBlackBoundaryPointAfter_eq_prefix
    R pairing d z.2.val
  rw [fkRectBlackOrbitPrefix_eq_pos pairing d z.2] at hi
  have hui : fkRectBlackDartShiftedPoint R u
        ((fkMedialBlackBoundaryPerm pairing)^[z.2.val] d) =
      fkRectBlackBoundaryPointAfter R pairing d 0 +
        2 • pos dir z.2 := hu.symm.trans hi
  refine ⟨u + z.1 • w, ?_⟩
  rw [fkRectBlackDartShiftedPoint_add,
    fkRectBlackDeckPointShift_nsmul, hui, hshift]
  apply Prod.ext <;>
    simp [dir, D, ons_periodStateCoord] <;> ring

theorem fkRectBlackOrbit_iterate_index_injective
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    Function.Injective (fun i : Fin (fkRectBlackOrbitList pairing d).length =>
      (fkMedialBlackBoundaryPerm pairing)^[i.val] d) := by
  intro i j hij
  apply (Equiv.Perm.nodup_toList
    (fkMedialBlackBoundaryPerm pairing) d).get_inj_iff.mp
  change (fkRectBlackOrbitList pairing d).get i =
    (fkRectBlackOrbitList pairing d).get j
  rw [fkRectBlackOrbitList_get pairing d i,
    fkRectBlackOrbitList_get pairing d j]
  exact hij

theorem fkRectBlackOrbit_periodStateCoord_injective
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus)
    [NeZero (fkRectBlackOrbitList pairing d).length]
    (hne : (ons_pathDisplacement
          (List.ofFn (fkRectBlackOrbitDirection pairing d))).1 ≠ 0 ∨
      (ons_pathDisplacement
          (List.ofFn (fkRectBlackOrbitDirection pairing d))).2 ≠ 0) :
    Function.Injective
      (ons_periodStateCoord (fkRectBlackOrbitDirection pairing d)) := by
  intro z w hzw
  obtain ⟨u, hu⟩ := fkRectBlackOrbit_periodState_exists_shiftedPoint
    R pairing d z
  obtain ⟨v, hv⟩ := fkRectBlackOrbit_periodState_exists_shiftedPoint
    R pairing d w
  have huv :
      (u, (fkMedialBlackBoundaryPerm pairing)^[z.2.val] d) =
        (v, (fkMedialBlackBoundaryPerm pairing)^[w.2.val] d) := by
    apply fkRectBlackDartShiftedPoint_injective R
    change fkRectBlackDartShiftedPoint R u
        ((fkMedialBlackBoundaryPerm pairing)^[z.2.val] d) =
      fkRectBlackDartShiftedPoint R v
        ((fkMedialBlackBoundaryPerm pairing)^[w.2.val] d)
    rw [hu, hv, hzw]
  have hindex : z.2 = w.2 :=
    fkRectBlackOrbit_iterate_index_injective pairing d
      (congrArg Prod.snd huv)
  rcases z with ⟨r, i⟩
  rcases w with ⟨s, j⟩
  dsimp only at hindex
  subst j
  apply Prod.ext
  · dsimp only
    let dir := fkRectBlackOrbitDirection pairing d
    let D := ons_pathDisplacement (List.ofFn dir)
    change pos dir i + r • D = pos dir i + s • D at hzw
    have hrsD : r • D = s • D := add_left_cancel hzw
    rcases hne with hx | hy
    · have hrsx := congrArg Prod.fst hrsD
      change r • D.1 = s • D.1 at hrsx
      have hrsInt : (r : Int) = (s : Int) := by
        apply mul_right_cancel₀ hx
        simpa [nsmul_eq_mul] using hrsx
      exact_mod_cast hrsInt
    · have hrsy := congrArg Prod.snd hrsD
      change r • D.2 = s • D.2 at hrsy
      have hrsInt : (r : Int) = (s : Int) := by
        apply mul_right_cancel₀ hy
        simpa [nsmul_eq_mul] using hrsy
      exact_mod_cast hrsInt
  · rfl

theorem fkRectBlackOrbit_cyclicTurnSum_classification
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) :
    ons_cyclicTurnSum
          (List.ofFn (fkRectBlackOrbitDirection pairing d)) = 0 ∨
      ons_cyclicTurnSum
          (List.ofFn (fkRectBlackOrbitDirection pairing d)) = 4 ∨
      ons_cyclicTurnSum
          (List.ofFn (fkRectBlackOrbitDirection pairing d)) = -4 := by
  let l := fkRectBlackOrbitList pairing d
  have hlen : 0 < l.length := fkRectBlackOrbitList_length_pos pairing d
  letI : NeZero l.length := ⟨hlen.ne'⟩
  let dir := fkRectBlackOrbitDirection pairing d
  let D := ons_pathDisplacement (List.ofFn dir)
  by_cases hD : D = 0
  · right
    exact fkRectBlackOrbit_contractible_cyclicTurnSum R pairing d hD
  · left
    have hne : D.1 ≠ 0 ∨ D.2 ≠ 0 := by
      by_cases hx : D.1 = 0
      · right
        intro hy
        exact hD (Prod.ext hx hy)
      · exact Or.inl hx
    exact ons_periodicSimple_cyclicTurnSum_eq_zero_of_nonzero dir
      (fkRectBlackOrbit_periodStateCoord_injective R pairing d hne) hne

theorem fkRectBlackOrbitDirection_ofFn
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    List.ofFn (fkRectBlackOrbitDirection pairing d) =
      (fkRectBlackOrbitList pairing d).map
        (fun e : FKMedialBlackDart T =>
          fkMedialStrandDirection pairing e.1) := by
  simpa [fkRectBlackOrbitDirection, List.get_eq_getElem] using
    (List.ofFn_getElem_eq_map (fkRectBlackOrbitList pairing d)
      (fun e : FKMedialBlackDart T =>
        fkMedialStrandDirection pairing e.1))

theorem fkRectBlackOrbit_cyclicTurnSum_classification_toList
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) :
    ons_cyclicTurnSum
          ((fkMedialBlackBoundaryPerm pairing).toList d |>.map
            (fun e : FKMedialBlackDart R.medialTorus =>
              fkMedialStrandDirection pairing e.1)) = 0 ∨
      ons_cyclicTurnSum
          ((fkMedialBlackBoundaryPerm pairing).toList d |>.map
            (fun e : FKMedialBlackDart R.medialTorus =>
              fkMedialStrandDirection pairing e.1)) = 4 ∨
      ons_cyclicTurnSum
          ((fkMedialBlackBoundaryPerm pairing).toList d |>.map
            (fun e : FKMedialBlackDart R.medialTorus =>
              fkMedialStrandDirection pairing e.1)) = -4 := by
  rw [← fkRectBlackOrbitList]
  rw [← fkRectBlackOrbitDirection_ofFn]
  exact fkRectBlackOrbit_cyclicTurnSum_classification R pairing d



theorem fkRectCanonicalComponentTurn_classification
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (C : FKMedialLoop R.medialTorus pairing) :
    canonicalComponentTurn pairing C = 0 ∨
      canonicalComponentTurn pairing C = 4 ∨
      canonicalComponentTurn pairing C = -4 := by
  obtain ⟨A, hA⟩ :=
    (fkMedialBlackBoundaryCycleToLoop_bijective pairing).2 C
  induction A using Quot.ind with
  | _ d =>
      change (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
        d.1 = C at hA
      have hcanon := canonicalComponentTurn_eq_toList_sum pairing C d hA
      have hcyc := cyclicTurnSum_toList_strandDirections pairing d
      have hturn :
          ons_cyclicTurnSum
              ((fkMedialBlackBoundaryPerm pairing).toList d |>.map
                (fun e : FKMedialBlackDart R.medialTorus =>
                  fkMedialStrandDirection pairing e.1)) =
            -canonicalComponentTurn pairing C := by
        rw [hcanon]
        exact hcyc
      rcases fkRectBlackOrbit_cyclicTurnSum_classification_toList
        R pairing d with hzero | hfour | hnegfour
      · left
        omega
      · right
        right
        omega
      · right
        left
        omega

end
end StatMech.FrontierD
