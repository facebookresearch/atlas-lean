/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectZeroTurnEssential
import Code.Onsager.RectangularAxisSubdivision














namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section


def fkRectMedialSideDirection : FKMedialSide → Fin 4
  | .west => 2
  | .east => 0
  | .south => 3
  | .north => 1



def fkRectMedialSidePotential : FKMedialSide → Int × Int
  | .west => (0, 0)
  | .east => (1, 1)
  | .south => (0, 1)
  | .north => (1, 0)



def fkRectBlackBoundaryMedialDirection
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) : Fin 4 :=
  fkRectMedialSideDirection (fkMedialLocalMate pairing d.1).2



theorem fkRectBlackBoundary_strandStep_eq_medialStep_add_potential
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) :
    let a := stepOf (fkRectBlackBoundaryMedialDirection pairing d)
    let p := fkRectMedialSidePotential d.1.2
    let q := fkRectMedialSidePotential
      ((fkMedialBlackBoundaryPerm pairing d).1.2)
    stepOf (fkMedialStrandDirection pairing d.1) =
      (a.1 + a.2 + q.1 - p.1, a.1 - a.2 + q.2 - p.2) := by
  rcases d with ⟨⟨v, side⟩, hd⟩
  cases hp : pairing v <;> cases side <;>
    simp [fkRectBlackBoundaryMedialDirection, fkRectMedialSideDirection,
      fkRectMedialSidePotential, fkMedialBlackBoundaryPerm_val,
      fkMedialBoundaryStep_apply, fkMedialLocalMate, fkMedialBondMate,
      fkMedialStrandDirection, hp, stepOf]

theorem fkRectBlackOrbitList_get_add_one
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    [NeZero (fkRectBlackOrbitList pairing d).length]
    (i : Fin (fkRectBlackOrbitList pairing d).length) :
    (fkRectBlackOrbitList pairing d).get (i + 1) =
      fkMedialBlackBoundaryPerm pairing
        ((fkRectBlackOrbitList pairing d).get i) := by
  let p := fkMedialBlackBoundaryPerm pairing
  let l := fkRectBlackOrbitList pairing d
  have hl : (fkRectBlackOrbitList pairing d).Nodup :=
    Equiv.Perm.nodup_toList p d
  have hnextList := List.next_getElem
    (fkRectBlackOrbitList pairing d) hl i.val i.isLt
  have happly := Equiv.Perm.next_toList_eq_apply p d
    ((fkRectBlackOrbitList pairing d).get i)
    (List.get_mem (fkRectBlackOrbitList pairing d) i)
  have happly' : (fkRectBlackOrbitList pairing d).next
      (fkRectBlackOrbitList pairing d)[i.val] (by
        exact List.getElem_mem (l := fkRectBlackOrbitList pairing d) i.isLt) =
      p (fkRectBlackOrbitList pairing d)[i.val] := by
    simpa [l, p, List.get_eq_getElem] using happly
  rw [happly'] at hnextList
  have hiv : (i + 1).val =
      (i.val + 1) % (fkRectBlackOrbitList pairing d).length := by
    simp [Fin.val_add, Nat.add_mod]
  simpa only [p, List.get_eq_getElem, hiv] using hnextList.symm



theorem fkRectBlackOrbitDisplacement_eq_diagonal_medialDisplacement
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    let medial := ons_pathDisplacement (List.ofFn fun i =>
      fkRectBlackBoundaryMedialDirection pairing
        ((fkRectBlackOrbitList pairing d).get i))
    ons_pathDisplacement
        (List.ofFn (fkRectBlackOrbitDirection pairing d)) =
      (medial.1 + medial.2, medial.1 - medial.2) := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  have hn : 0 < l.length := fkRectBlackOrbitList_length_pos pairing d
  letI : NeZero l.length := ⟨hn.ne'⟩
  let e : Fin l.length → FKMedialBlackDart R.medialTorus := l.get
  let a : Fin l.length → Int × Int := fun i =>
    stepOf (fkRectBlackBoundaryMedialDirection pairing (e i))
  let p : Fin l.length → Int × Int := fun i =>
    fkRectMedialSidePotential (e i).1.2
  have hnext (i : Fin l.length) :
      e (i + 1) = fkMedialBlackBoundaryPerm pairing (e i) := by
    exact fkRectBlackOrbitList_get_add_one pairing d i
  have hpoint (i : Fin l.length) :
      stepOf (fkRectBlackOrbitDirection pairing d i) =
        ((a i).1 + (a i).2 + (p (i + 1)).1 - (p i).1,
          (a i).1 - (a i).2 + (p (i + 1)).2 - (p i).2) := by
    have h := fkRectBlackBoundary_strandStep_eq_medialStep_add_potential
      pairing (e i)
    rw [← hnext i] at h
    exact h
  have hpot (coord : (Int × Int) → Int) :
      (∑ i, coord (p (i + 1))) = ∑ i, coord (p i) := by
    change (∑ i, (fun j => coord (p j))
      ((Equiv.addRight (1 : Fin l.length)) i)) = _
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin l.length))
      (fun i => coord (p i))
  rw [ons_pathDisplacement_ofFn, ons_pathDisplacement_ofFn]
  change (∑ i, stepOf (fkRectBlackOrbitDirection pairing d i)) =
    ((∑ i, a i).1 + (∑ i, a i).2,
      (∑ i, a i).1 - (∑ i, a i).2)
  rw [show (∑ i, stepOf (fkRectBlackOrbitDirection pairing d i)) =
      ∑ i, ((a i).1 + (a i).2 + (p (i + 1)).1 - (p i).1,
        (a i).1 - (a i).2 + (p (i + 1)).2 - (p i).2) by
    apply Finset.sum_congr rfl
    intro i hi
    exact hpoint i]
  apply Prod.ext
  · simp only [Prod.fst_sum, Prod.snd_sum]
    dsimp only [a]
    simp only [Prod.fst, Prod.snd, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [hpot Prod.fst]
    ring
  · simp only [Prod.fst_sum, Prod.snd_sum]
    dsimp only [a]
    simp only [Prod.fst, Prod.snd, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [hpot Prod.snd]
    ring




theorem fkRectBlackOrbitDisplacement_eq_two_deck_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    ons_pathDisplacement
        (List.ofFn (fkRectBlackOrbitDirection
          (fkRectConfigurationToMedialPairing R omega) d)) =
      2 • fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := (fkRectBlackOrbitList pairing d).length
  let D := ons_pathDisplacement
    (List.ofFn (fkRectBlackOrbitDirection pairing d))
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hblack : (fkMedialBlackBoundaryPerm pairing)^[n] d = d :=
    fkRectBlackBoundaryPerm_pow_length_apply pairing d
  have hdart : (fkMedialBoundaryStep pairing)^[n] d.1 = d.1 := by
    rw [← fkMedialBlackBoundaryPerm_iterate_val pairing d n, hblack]
  have htrace : fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 n = w := by
    simpa [pairing, n, w] using
      (fkRectBlackBoundaryPrimalCycleWalk_winding R omega d).symm
  have hcenter := fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    R pairing d.1 (0, 0) n
  rw [hdart, htrace] at hcenter
  have hcenter' : fkRectRefinedBoundaryCenterAfter pairing d.1
      (fkRectRefinedBoundaryCanonicalCenter R d.1) n =
        ((fkRectRefinedBoundaryCanonicalCenter R d.1).1 +
            4 * (fkRectSquareDeckTranslation R w).1,
          (fkRectRefinedBoundaryCanonicalCenter R d.1).2 +
            4 * (fkRectSquareDeckTranslation R w).2) := by
    simpa only [Prod.fst, Prod.snd, add_zero, add_sub_cancel_right] using hcenter
  have hpointShift :
      fkRectBlackBoundaryPointAfter R pairing d n =
        fkRectBlackDartShiftedPoint R w d := by
    unfold fkRectBlackBoundaryPointAfter fkRectBlackDartShiftedPoint
    rw [hblack, hcenter']
  have hpointPrefix := fkRectBlackBoundaryPointAfter_eq_prefix
    R pairing d n
  have hprefix := fkRectBlackOrbitPrefix_length_eq_displacement pairing d
  change fkRectBlackOrbitPrefix pairing d n = D at hprefix
  rw [hprefix] at hpointPrefix
  have hshift := fkRectBlackDartShiftedPoint_add R (0, 0) w d
  have hstart : fkRectBlackDartShiftedPoint R (0, 0) d =
      fkRectBlackBoundaryPointAfter R pairing d 0 := by
    rw [fkRectBlackBoundaryPointAfter_zero]
  have hzeroAdd : ((0, 0) : Int × Int) + w = w := by
    apply Prod.ext <;> simp
  rw [hzeroAdd, hstart] at hshift
  have heq : 2 • D = fkRectBlackDeckPointShift R w := by
    apply add_left_cancel
    calc
      fkRectBlackBoundaryPointAfter R pairing d 0 + 2 • D =
          fkRectBlackBoundaryPointAfter R pairing d n := hpointPrefix.symm
      _ = fkRectBlackDartShiftedPoint R w d := hpointShift
      _ = fkRectBlackBoundaryPointAfter R pairing d 0 +
          fkRectBlackDeckPointShift R w := hshift
  change D = 2 • fkRectSquareDeckTranslation R w
  apply Prod.ext
  · have hx := congrArg Prod.fst heq
    unfold fkRectBlackDeckPointShift at hx
    change 2 * D.1 = 4 * (fkRectSquareDeckTranslation R w).1 at hx
    change D.1 = 2 * (fkRectSquareDeckTranslation R w).1
    omega
  · have hy := congrArg Prod.snd heq
    unfold fkRectBlackDeckPointShift at hy
    change 2 * D.2 = 4 * (fkRectSquareDeckTranslation R w).2 at hy
    change D.2 = 2 * (fkRectSquareDeckTranslation R w).2
    omega



theorem fkRectBlackOrbitMedialDisplacement_eq_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    ons_pathDisplacement (List.ofFn fun i =>
      fkRectBlackBoundaryMedialDirection pairing
        ((fkRectBlackOrbitList pairing d).get i)) =
      (((2 * R.width : ℕ) : ℤ) * w.1, (R.height : ℤ) * w.2) := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let medial := ons_pathDisplacement (List.ofFn fun i =>
    fkRectBlackBoundaryMedialDirection pairing
      ((fkRectBlackOrbitList pairing d).get i))
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hdiag :=
    fkRectBlackOrbitDisplacement_eq_diagonal_medialDisplacement R omega d
  have hdeck := fkRectBlackOrbitDisplacement_eq_two_deck_winding R omega d
  change ons_pathDisplacement
      (List.ofFn (fkRectBlackOrbitDirection pairing d)) =
        (medial.1 + medial.2, medial.1 - medial.2) at hdiag
  change ons_pathDisplacement
      (List.ofFn (fkRectBlackOrbitDirection pairing d)) =
        2 • fkRectSquareDeckTranslation R w at hdeck
  have heq : (medial.1 + medial.2, medial.1 - medial.2) =
      2 • fkRectSquareDeckTranslation R w := hdiag.symm.trans hdeck
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  have hheight : (2 : ℤ) * (R.height / 2 : ℕ) = R.height := by
    exact_mod_cast Nat.two_mul_div_two_of_even R.height_even
  unfold fkRectSquareDeckTranslation at hx hy
  change medial.1 + medial.2 =
    2 * ((R.width : ℤ) * w.1 + (R.height / 2 : ℕ) * w.2) at hx
  change medial.1 - medial.2 =
    2 * ((R.width : ℤ) * w.1 - (R.height / 2 : ℕ) * w.2) at hy
  change medial = _
  apply Prod.ext
  · change medial.1 = ((2 * R.width : ℕ) : ℤ) * w.1
    rw [Nat.cast_mul, Nat.cast_ofNat]
    have htwo : 2 * medial.1 = 4 * (R.width : ℤ) * w.1 := by
      linear_combination hx + hy
    have htarget : 2 * medial.1 =
        2 * (2 * (R.width : ℤ) * w.1) := by
      calc
        _ = 4 * (R.width : ℤ) * w.1 := htwo
        _ = _ := by ring
    omega
  · change medial.2 = (R.height : ℤ) * w.2
    have htwo : 2 * medial.2 = 4 * (R.height / 2 : ℕ) * w.2 := by
      linear_combination hx - hy
    have htarget : 2 * medial.2 = 2 * (R.height : ℤ) * w.2 := by
      calc
        _ = 4 * (R.height / 2 : ℕ) * w.2 := htwo
        _ = 2 * (R.height : ℤ) * w.2 := by
          linear_combination 2 * w.2 * hheight
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
      (by simpa [mul_assoc] using htarget)


def fkRectMedialRibbonPortOffset : FKMedialSide → Int × Int
  | .west => (2, 4)
  | .east => (6, 4)
  | .south => (4, 2)
  | .north => (4, 6)

def fkRectMedialOppositeSide : FKMedialSide → FKMedialSide
  | .west => .east
  | .east => .west
  | .south => .north
  | .north => .south


def fkRectMedialRibbonLocalBlock
    (pairing : Bool) (side : FKMedialSide) : List (Fin 4) :=
  match pairing, side with
  | false, .west => [1, 1, 0, 0]
  | false, .north => [2, 2, 3, 3]
  | false, .east => [3, 3, 2, 2]
  | false, .south => [0, 0, 1, 1]
  | true, .west => [3, 3, 0, 0]
  | true, .south => [2, 2, 1, 1]
  | true, .east => [1, 1, 2, 2]
  | true, .north => [0, 0, 3, 3]



def fkRectMedialRibbonBlock
    (pairing : Bool) (side : FKMedialSide) : List (Fin 4) :=
  fkRectMedialRibbonLocalBlock pairing side ++
    List.replicate 4 (fkRectMedialSideDirection
      (fkRectMedialLocalMateSide pairing side))

@[simp] theorem fkRectMedialRibbonBlock_length
    (pairing : Bool) (side : FKMedialSide) :
    (fkRectMedialRibbonBlock pairing side).length = 8 := by
  cases pairing <;> cases side <;>
    simp [fkRectMedialRibbonBlock, fkRectMedialRibbonLocalBlock]



theorem fkRectMedialRibbonBlock_step_sum
    (pairing : Bool) (side : FKMedialSide) :
    let medialDir := fkRectMedialSideDirection
      (fkRectMedialLocalMateSide pairing side)
    let nextSide := fkRectMedialOppositeSide
      (fkRectMedialLocalMateSide pairing side)
    ((fkRectMedialRibbonBlock pairing side).map stepOf).sum =
      (8 * (stepOf medialDir).1 +
          (fkRectMedialRibbonPortOffset nextSide).1 -
          (fkRectMedialRibbonPortOffset side).1,
        8 * (stepOf medialDir).2 +
          (fkRectMedialRibbonPortOffset nextSide).2 -
          (fkRectMedialRibbonPortOffset side).2) := by
  cases pairing <;> cases side <;>
    decide

theorem fkRectMedialOppositeSide_localMate_eq_boundaryPerm_side
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) :
    fkRectMedialOppositeSide (fkMedialLocalMate pairing d.1).2 =
      (fkMedialBlackBoundaryPerm pairing d).1.2 := by
  rcases d with ⟨⟨v, side⟩, hd⟩
  cases hp : pairing v <;> cases side <;>
    simp [fkRectMedialOppositeSide, fkMedialBlackBoundaryPerm_val,
      fkMedialLocalMate, fkMedialBondMate, hp]




def fkRectBlackOrbitMedialRibbonWord
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) : List (Fin 4) :=
  let pairing := fkRectConfigurationToMedialPairing R omega
  (fkRectBlackOrbitList pairing d).flatMap fun e =>
    fkRectMedialRibbonBlock (pairing e.1.1) e.1.2

@[simp] theorem fkRectBlackOrbitMedialRibbonWord_length
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    (fkRectBlackOrbitMedialRibbonWord R omega d).length =
      8 * (fkRectBlackOrbitList
        (fkRectConfigurationToMedialPairing R omega) d).length := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  change (l.flatMap fun e =>
    fkRectMedialRibbonBlock (pairing e.1.1) e.1.2).length = 8 * l.length
  induction l with
  | nil => simp
  | cons e tail ih =>
      simp [ih, Nat.mul_add, Nat.add_comm]

theorem fkRectBlackOrbitMedialRibbonWord_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackOrbitMedialRibbonWord R omega d ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  rw [fkRectBlackOrbitMedialRibbonWord_length] at hlen
  simp only [List.length_nil] at hlen
  have hpos := fkRectBlackOrbitList_length_pos
    (fkRectConfigurationToMedialPairing R omega) d
  omega



theorem fkRectBlackOrbitMedialRibbonWord_step_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    ((fkRectBlackOrbitMedialRibbonWord R omega d).map stepOf).sum =
      (8 * ((2 * R.width : ℕ) : ℤ) * w.1,
        8 * (R.height : ℤ) * w.2) := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  have hn : 0 < l.length := fkRectBlackOrbitList_length_pos pairing d
  letI : NeZero l.length := ⟨hn.ne'⟩
  let e : Fin l.length → FKMedialBlackDart R.medialTorus := l.get
  let a : Fin l.length → Int × Int := fun i =>
    stepOf (fkRectBlackBoundaryMedialDirection pairing (e i))
  let p : Fin l.length → Int × Int := fun i =>
    fkRectMedialRibbonPortOffset (e i).1.2
  have hnext (i : Fin l.length) :
      e (i + 1) = fkMedialBlackBoundaryPerm pairing (e i) :=
    fkRectBlackOrbitList_get_add_one pairing d i
  have hblock (i : Fin l.length) :
      ((fkRectMedialRibbonBlock (pairing (e i).1.1) (e i).1.2).map
          stepOf).sum =
        (8 * (a i).1 + (p (i + 1)).1 - (p i).1,
          8 * (a i).2 + (p (i + 1)).2 - (p i).2) := by
    dsimp only [a, p]
    rw [hnext i]
    rcases hdi : e i with ⟨⟨v, side⟩, hd⟩
    cases hp : pairing v <;> cases side <;>
      simp [fkRectMedialRibbonBlock, fkRectMedialRibbonLocalBlock,
        fkRectBlackBoundaryMedialDirection, fkRectMedialSideDirection,
        fkRectMedialRibbonPortOffset, fkMedialBlackBoundaryPerm_val,
        fkRectMedialLocalMateSide, fkMedialLocalMate,
        fkMedialBondMate, hp, stepOf]
  have hpot (coord : (Int × Int) → Int) :
      (∑ i, coord (p (i + 1))) = ∑ i, coord (p i) := by
    change (∑ i, (fun j => coord (p j))
      ((Equiv.addRight (1 : Fin l.length)) i)) = _
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin l.length))
      (fun i => coord (p i))
  have hflat (xs : List (FKMedialBlackDart R.medialTorus)) :
      (((xs.flatMap fun z =>
          fkRectMedialRibbonBlock (pairing z.1.1) z.1.2).map stepOf).sum) =
        (xs.map fun z => ((fkRectMedialRibbonBlock
          (pairing z.1.1) z.1.2).map stepOf).sum).sum := by
    induction xs with
    | nil => simp
    | cons z tail ih =>
        simp [List.sum_append, ih]
  have hsum :
      ((fkRectBlackOrbitMedialRibbonWord R omega d).map stepOf).sum =
        ∑ i, ((fkRectMedialRibbonBlock
          (pairing (e i).1.1) (e i).1.2).map stepOf).sum := by
    rw [show fkRectBlackOrbitMedialRibbonWord R omega d =
      l.flatMap fun z => fkRectMedialRibbonBlock
        (pairing z.1.1) z.1.2 by rfl]
    rw [hflat]
    rw [← List.sum_ofFn]
    let F : FKMedialBlackDart R.medialTorus → Int × Int := fun z =>
      ((fkRectMedialRibbonBlock (pairing z.1.1) z.1.2).map stepOf).sum
    change (l.map F).sum = (List.ofFn fun i => F (l.get i)).sum
    congr 1
    calc
      l.map F = (List.ofFn l.get).map F := by rw [List.ofFn_get]
      _ = List.ofFn (fun i => F (l.get i)) := by
        simp [List.map_ofFn, Function.comp_apply]
  rw [hsum]
  simp_rw [hblock]
  have hmedial := fkRectBlackOrbitMedialDisplacement_eq_winding R omega d
  change ons_pathDisplacement (List.ofFn fun i =>
      fkRectBlackBoundaryMedialDirection pairing (e i)) = _ at hmedial
  rw [ons_pathDisplacement_ofFn] at hmedial
  apply Prod.ext
  · simp only [Prod.fst_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [hpot Prod.fst]
    have hx := congrArg Prod.fst hmedial
    simp only [Prod.fst_sum] at hx
    change (∑ i, (a i).1) = _ at hx
    rw [← Finset.mul_sum, hx]
    ring
  · simp only [Prod.snd_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [hpot Prod.snd]
    have hy := congrArg Prod.snd hmedial
    simp only [Prod.snd_sum] at hy
    change (∑ i, (a i).2) = _ at hy
    rw [← Finset.mul_sum, hy]
    ring



def fkRectBlackOrbitRibbonSubdivisionWord
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) : List (Fin 4) :=
  onsAnisotropicDirectionWord (16 * R.width) (8 * R.height)
    (fkRectBlackOrbitMedialRibbonWord R omega d)

def fkRectBlackOrbitRibbonSubdivisionSide (R : FKRectTorus) : ℕ :=
  (16 * R.width) * (8 * R.height)

theorem fkRectBlackOrbitRibbonSubdivisionSide_gt_two (R : FKRectTorus) :
    2 < fkRectBlackOrbitRibbonSubdivisionSide R := by
  unfold fkRectBlackOrbitRibbonSubdivisionSide
  nlinarith [R.width_pos, R.height_pos]

theorem fkRectBlackOrbitRibbonSubdivisionWord_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackOrbitRibbonSubdivisionWord R omega d ≠ [] := by
  let word := fkRectBlackOrbitMedialRibbonWord R omega d
  have hword : word ≠ [] :=
    fkRectBlackOrbitMedialRibbonWord_nonempty R omega d
  intro hnil
  change onsAnisotropicDirectionWord
      (16 * R.width) (8 * R.height) word = [] at hnil
  rw [onsAnisotropicDirectionWord, List.flatMap_eq_nil_iff] at hnil
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil word hword
  have hzero := (List.replicate_eq_nil_iff a).mp (hnil a ha)
  have hpos : 0 < onsAnisotropicStepScale
      (16 * R.width) (8 * R.height) a := by
    fin_cases a <;>
      simp [onsAnisotropicStepScale, R.width_pos, R.height_pos]
  omega

instance fkRectBlackOrbitRibbonSubdivisionWord_length_neZero
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    NeZero (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length :=
  ⟨(List.length_pos_iff_ne_nil.mpr
    (fkRectBlackOrbitRibbonSubdivisionWord_nonempty R omega d)).ne'⟩

theorem fkRectBlackOrbitRibbonSubdivisionWord_preserves_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    ((fkRectBlackOrbitRibbonSubdivisionWord R omega d).map
        ons_dirExponentX).sum =
          (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.1 ∧
      ((fkRectBlackOrbitRibbonSubdivisionWord R omega d).map
        ons_dirExponentY).sum =
          (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.2 := by
  dsimp only
  let word := fkRectBlackOrbitMedialRibbonWord R omega d
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hstep := fkRectBlackOrbitMedialRibbonWord_step_sum R omega d
  change (word.map stepOf).sum =
    (8 * ((2 * R.width : ℕ) : ℤ) * w.1,
      8 * (R.height : ℤ) * w.2) at hstep
  have hx : (word.map ons_dirExponentX).sum =
      ((16 * R.width : ℕ) : ℤ) * w.1 := by
    have h := congrArg Prod.fst hstep
    rw [onsDirectionWord_stepOf_fst_sum] at h
    calc
      _ = 8 * ((2 * R.width : ℕ) : ℤ) * w.1 := by
        simpa only [Prod.fst] using h
      _ = ((16 * R.width : ℕ) : ℤ) * w.1 := by
        push_cast
        ring
  have hy : (word.map ons_dirExponentY).sum =
      ((8 * R.height : ℕ) : ℤ) * w.2 := by
    have h := congrArg Prod.snd hstep
    rw [onsDirectionWord_stepOf_snd_sum] at h
    simpa only [Prod.snd, Nat.cast_mul, Nat.cast_ofNat] using h
  have h := onsAnisotropicDirectionWord_preserves_winding
    (16 * R.width) (8 * R.height) word w.1 w.2 hx hy
  simpa [fkRectBlackOrbitRibbonSubdivisionWord,
    fkRectBlackOrbitRibbonSubdivisionSide, word, w] using h


noncomputable def fkRectBlackOrbitRibbonSubdivisionDart
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Fin (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length →
      ons_Dart (fkRectBlackOrbitRibbonSubdivisionSide R) :=
  onsDirectionWordTorusDart
    (fkRectBlackOrbitRibbonSubdivisionSide R)
    (fkRectBlackOrbitRibbonSubdivisionWord R omega d)

theorem fkRectBlackOrbitRibbonSubdivisionDart_valid
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    ∀ k,
      (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).1 =
        ons_dirStep (fkRectBlackOrbitRibbonSubdivisionSide R)
          (fkRectBlackOrbitRibbonSubdivisionDart R omega d (k + 1)).2
          (fkRectBlackOrbitRibbonSubdivisionDart R omega d (k + 1)).1 := by
  let word := fkRectBlackOrbitRibbonSubdivisionWord R omega d
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hw :=
    fkRectBlackOrbitRibbonSubdivisionWord_preserves_winding R omega d
  have hdisp : (word.map stepOf).sum =
      ((fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.1,
        (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.2) := by
    apply Prod.ext
    · rw [onsDirectionWord_stepOf_fst_sum]
      exact hw.1
    · rw [onsDirectionWord_stepOf_snd_sum]
      exact hw.2
  simpa only [fkRectBlackOrbitRibbonSubdivisionDart, word] using
    (onsDirectionWordTorusDart_valid
      (fkRectBlackOrbitRibbonSubdivisionSide R) word w.1 w.2 hdisp)

theorem fkRectBlackOrbitRibbonSubdivisionDart_exponentX_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    (∑ k, ons_dirExponentX
      (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).2) =
        (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.1 := by
  dsimp only
  rw [show (∑ k, ons_dirExponentX
      (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).2) =
      ((fkRectBlackOrbitRibbonSubdivisionWord R omega d).map
        ons_dirExponentX).sum by
    simpa only [fkRectBlackOrbitRibbonSubdivisionDart] using
      (onsDirectionWordTorusDart_exponentX_sum
        (fkRectBlackOrbitRibbonSubdivisionSide R)
        (fkRectBlackOrbitRibbonSubdivisionWord R omega d))]
  exact (fkRectBlackOrbitRibbonSubdivisionWord_preserves_winding
    R omega d).1

theorem fkRectBlackOrbitRibbonSubdivisionDart_exponentY_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    (∑ k, ons_dirExponentY
      (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).2) =
        (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.2 := by
  dsimp only
  rw [show (∑ k, ons_dirExponentY
      (fkRectBlackOrbitRibbonSubdivisionDart R omega d k).2) =
      ((fkRectBlackOrbitRibbonSubdivisionWord R omega d).map
        ons_dirExponentY).sum by
    simpa only [fkRectBlackOrbitRibbonSubdivisionDart] using
      (onsDirectionWordTorusDart_exponentY_sum
        (fkRectBlackOrbitRibbonSubdivisionSide R)
        (fkRectBlackOrbitRibbonSubdivisionWord R omega d))]
  exact (fkRectBlackOrbitRibbonSubdivisionWord_preserves_winding
    R omega d).2




def fkRectBlackOrbitShearSubdivisionWord
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) : List (Fin 4) :=
  onsRectangularShearSubdivisionWord R.width R.height
    (List.ofFn (fkRectBlackOrbitDirection
      (fkRectConfigurationToMedialPairing R omega) d))

theorem fkRectBlackOrbitShearSubdivisionWord_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackOrbitShearSubdivisionWord R omega d ≠ [] := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dir := fkRectBlackOrbitDirection pairing d
  let original := List.ofFn dir
  have hn : 0 < (fkRectBlackOrbitList pairing d).length :=
    fkRectBlackOrbitList_length_pos pairing d
  letI : NeZero (fkRectBlackOrbitList pairing d).length := ⟨hn.ne'⟩
  have horiginal : original ≠ [] := by simp [original, NeZero.ne _]
  have hshear : onsDiagonalShearDirectionWord original ≠ [] := by
    intro hnil
    rw [onsDiagonalShearDirectionWord, List.flatMap_eq_nil_iff] at hnil
    have hmem : dir 0 ∈ original := by
      rw [List.mem_ofFn]
      exact ⟨0, rfl⟩
    have := hnil (dir 0) hmem
    generalize hdir : dir 0 = a at this
    fin_cases a <;>
      simp [onsDiagonalShearDirectionBlock] at this
  intro hnil
  change onsAnisotropicDirectionWord (4 * R.width) (2 * R.height)
      (onsDiagonalShearDirectionWord original) = [] at hnil
  rw [onsAnisotropicDirectionWord, List.flatMap_eq_nil_iff] at hnil
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil
    (onsDiagonalShearDirectionWord original) hshear
  have hzero := (List.replicate_eq_nil_iff a).mp (hnil a ha)
  have hpos : 0 < onsAnisotropicStepScale
      (4 * R.width) (2 * R.height) a := by
    fin_cases a <;>
      simp [onsAnisotropicStepScale, R.width_pos, R.height_pos]
  omega

instance fkRectBlackOrbitShearSubdivisionWord_length_neZero
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    NeZero (fkRectBlackOrbitShearSubdivisionWord R omega d).length :=
  ⟨(List.length_pos_iff_ne_nil.mpr
    (fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d)).ne'⟩


theorem fkRectBlackOrbitShearSubdivisionWord_cyclicNonUturn
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    onsCyclicDirectionNonUturn
      (fkRectBlackOrbitShearSubdivisionWord R omega d) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  have hn : 0 < (fkRectBlackOrbitList pairing d).length :=
    fkRectBlackOrbitList_length_pos pairing d
  letI : NeZero (fkRectBlackOrbitList pairing d).length := ⟨hn.ne'⟩
  unfold fkRectBlackOrbitShearSubdivisionWord
  apply onsRectangularShearSubdivisionWord_cyclicNonUturn
    R.width R.height R.width_pos R.height_pos
  apply onsCyclicDirectionNonUturn_ofFn
  intro k
  exact fkRectBlackOrbitDirection_nonUturn pairing d k


def fkRectBlackOrbitSubdivisionSide (R : FKRectTorus) : ℕ :=
  8 * R.width * R.height



theorem fkRectBlackOrbitShearSubdivisionWord_preserves_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    ((fkRectBlackOrbitShearSubdivisionWord R omega d).map
        ons_dirExponentX).sum =
          (fkRectBlackOrbitSubdivisionSide R : ℕ) * w.1 ∧
      ((fkRectBlackOrbitShearSubdivisionWord R omega d).map
        ons_dirExponentY).sum =
          (fkRectBlackOrbitSubdivisionSide R : ℕ) * w.2 := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let word := List.ofFn (fkRectBlackOrbitDirection pairing d)
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hdisp := fkRectBlackOrbitDisplacement_eq_two_deck_winding R omega d
  change ons_pathDisplacement word = 2 • fkRectSquareDeckTranslation R w at hdisp
  have hrect : ons_pathDisplacement word =
      ((2 * R.width : ℕ) * w.1 + (R.height : ℤ) * w.2,
        (2 * R.width : ℕ) * w.1 - (R.height : ℤ) * w.2) := by
    have hheight : (2 : ℤ) * (R.height / 2 : ℕ) = R.height := by
      exact_mod_cast Nat.two_mul_div_two_of_even R.height_even
    rw [hdisp]
    apply Prod.ext
    · change 2 * ((R.width : ℤ) * w.1 +
          ((R.height / 2 : ℕ) : ℤ) * w.2) =
        ((2 * R.width : ℕ) : ℤ) * w.1 + (R.height : ℤ) * w.2
      rw [Nat.cast_mul, Nat.cast_ofNat]
      linear_combination w.2 * hheight
    · change 2 * ((R.width : ℤ) * w.1 -
          ((R.height / 2 : ℕ) : ℤ) * w.2) =
        ((2 * R.width : ℕ) : ℤ) * w.1 - (R.height : ℤ) * w.2
      rw [Nat.cast_mul, Nat.cast_ofNat]
      linear_combination -(w.2 * hheight)
  have hrect' : (word.map stepOf).sum =
      ((2 * R.width : ℕ) * w.1 + (R.height : ℤ) * w.2,
        (2 * R.width : ℕ) * w.1 - (R.height : ℤ) * w.2) := by
    rw [← ons_pathDisplacement_eq_sum_map]
    exact hrect
  have h := onsRectangularShearSubdivisionWord_preserves_deck_winding
    R.width R.height word w.1 w.2 hrect'
  simpa [fkRectBlackOrbitShearSubdivisionWord,
    fkRectBlackOrbitSubdivisionSide, pairing, word, w] using h



noncomputable def fkRectBlackOrbitSubdivisionDart
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Fin (fkRectBlackOrbitShearSubdivisionWord R omega d).length →
      ons_Dart (fkRectBlackOrbitSubdivisionSide R) := by
  let word := fkRectBlackOrbitShearSubdivisionWord R omega d
  have hword : word ≠ [] :=
    fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d
  letI : NeZero word.length :=
    ⟨(List.length_pos_iff_ne_nil.mpr hword).ne'⟩
  exact onsDirectionWordTorusDart
    (fkRectBlackOrbitSubdivisionSide R) word

theorem fkRectBlackOrbitSubdivisionSide_gt_two (R : FKRectTorus) :
    2 < fkRectBlackOrbitSubdivisionSide R := by
  unfold fkRectBlackOrbitSubdivisionSide
  nlinarith [R.width_pos, R.height_pos]


theorem fkRectBlackOrbitSubdivisionDart_valid
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    ∀ k,
      (fkRectBlackOrbitSubdivisionDart R omega d k).1 =
        ons_dirStep (fkRectBlackOrbitSubdivisionSide R)
          (fkRectBlackOrbitSubdivisionDart R omega d (k + 1)).2
          (fkRectBlackOrbitSubdivisionDart R omega d (k + 1)).1 := by
  let word := fkRectBlackOrbitShearSubdivisionWord R omega d
  have hword : word ≠ [] :=
    fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d
  letI : NeZero word.length :=
    ⟨(List.length_pos_iff_ne_nil.mpr hword).ne'⟩
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  have hw := fkRectBlackOrbitShearSubdivisionWord_preserves_winding R omega d
  have hdisp : (word.map stepOf).sum =
      ((fkRectBlackOrbitSubdivisionSide R : ℤ) * w.1,
        (fkRectBlackOrbitSubdivisionSide R : ℤ) * w.2) := by
    apply Prod.ext
    · rw [onsDirectionWord_stepOf_fst_sum]
      exact hw.1
    · rw [onsDirectionWord_stepOf_snd_sum]
      exact hw.2
  simpa only [fkRectBlackOrbitSubdivisionDart, word] using
    (onsDirectionWordTorusDart_valid
      (fkRectBlackOrbitSubdivisionSide R) word w.1 w.2 hdisp)


theorem fkRectBlackOrbitSubdivisionDart_nonUturn
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    ∀ k,
      (fkRectBlackOrbitSubdivisionDart R omega d k).2 ≠
        (fkRectBlackOrbitSubdivisionDart R omega d (k + 1)).2 + 2 := by
  let word := fkRectBlackOrbitShearSubdivisionWord R omega d
  have hword : word ≠ [] :=
    fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d
  letI : NeZero word.length :=
    ⟨(List.length_pos_iff_ne_nil.mpr hword).ne'⟩
  have hcyclic :=
    fkRectBlackOrbitShearSubdivisionWord_cyclicNonUturn R omega d
  simpa only [fkRectBlackOrbitSubdivisionDart, word] using
    (onsDirectionWordTorusDart_nonUturn
      (fkRectBlackOrbitSubdivisionSide R) word hcyclic)

theorem fkRectBlackOrbitSubdivisionDart_exponentX_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    (∑ k, ons_dirExponentX
      (fkRectBlackOrbitSubdivisionDart R omega d k).2) =
        (fkRectBlackOrbitSubdivisionSide R : ℤ) * w.1 := by
  dsimp only
  let word := fkRectBlackOrbitShearSubdivisionWord R omega d
  have hword : word ≠ [] :=
    fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d
  letI : NeZero word.length :=
    ⟨(List.length_pos_iff_ne_nil.mpr hword).ne'⟩
  rw [show (∑ k, ons_dirExponentX
      (fkRectBlackOrbitSubdivisionDart R omega d k).2) =
      (word.map ons_dirExponentX).sum by
        simpa only [fkRectBlackOrbitSubdivisionDart, word] using
          (onsDirectionWordTorusDart_exponentX_sum
            (fkRectBlackOrbitSubdivisionSide R) word)]
  exact (fkRectBlackOrbitShearSubdivisionWord_preserves_winding
    R omega d).1

theorem fkRectBlackOrbitSubdivisionDart_exponentY_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    (∑ k, ons_dirExponentY
      (fkRectBlackOrbitSubdivisionDart R omega d k).2) =
        (fkRectBlackOrbitSubdivisionSide R : ℤ) * w.2 := by
  dsimp only
  let word := fkRectBlackOrbitShearSubdivisionWord R omega d
  have hword : word ≠ [] :=
    fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d
  letI : NeZero word.length :=
    ⟨(List.length_pos_iff_ne_nil.mpr hword).ne'⟩
  rw [show (∑ k, ons_dirExponentY
      (fkRectBlackOrbitSubdivisionDart R omega d k).2) =
      (word.map ons_dirExponentY).sum by
        simpa only [fkRectBlackOrbitSubdivisionDart, word] using
          (onsDirectionWordTorusDart_exponentY_sum
            (fkRectBlackOrbitSubdivisionSide R) word)]
  exact (fkRectBlackOrbitShearSubdivisionWord_preserves_winding
    R omega d).2




theorem fkRectBlackBoundaryPrimalCycleWinding_fst_odd_of_site_injective
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hsite : Function.Injective (fun k ↦
      (fkRectBlackOrbitSubdivisionDart R omega d k).1))
    (hy : (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0)
    (hx : (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 ≠ 0) :
    Odd (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 := by
  letI : Fact (2 < fkRectBlackOrbitSubdivisionSide R) :=
    ⟨fkRectBlackOrbitSubdivisionSide_gt_two R⟩
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  apply ons_simpleLoop_horizontal_winding_odd_of_ne_zero
    (fkRectBlackOrbitSubdivisionDart R omega d)
    (fkRectBlackOrbitSubdivisionDart_valid R omega d)
    hsite
    (fkRectBlackOrbitSubdivisionDart_nonUturn R omega d)
    w.1
    (fkRectBlackOrbitSubdivisionDart_exponentX_sum R omega d)
  · rw [fkRectBlackOrbitSubdivisionDart_exponentY_sum]
    simp [w, hy]
  · exact hx

end

end StatMech.FrontierD
