/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Mathlib
import Code.Onsager.GeneralUmlaufsatz
import Code.Universality.HexAllWidthStripGeometry

namespace StatMech.Universality

open Finset
open StatMech.Onsager.BaseCase
open StatMech.Onsager





def hexBrickDir : Fin 6 → Fin 4 := ![2, 2, 1, 0, 0, 3]




def hexBrickPos (c : HexAWCoord) : ℤ × ℤ :=
  match c.color with
  | .black => (2 * c.i + c.j, -c.j)
  | .white => (2 * c.i + c.j + 1, -c.j)


def hexAWHeadingMod (c : HexAWCoord) (e : Fin 3) : Fin 6 :=
  match c.color, e with
  | .black, 0 => 4
  | .black, 1 => 0
  | .black, 2 => 2
  | .white, 0 => 1
  | .white, 1 => 3
  | .white, 2 => 5



theorem hexBrickPos_neighbor (c : HexAWCoord) (e : Fin 3) :
    hexBrickPos (hexAWNeighbor c e) =
      hexBrickPos c + stepOf (hexBrickDir (hexAWHeadingMod c e)) := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;>
    simp [hexBrickPos, hexAWNeighbor, hexAWHeadingMod, hexBrickDir, stepOf,
      Prod.ext_iff] <;> omega



theorem hexBrickPos_injective : Function.Injective hexBrickPos := by
  intro c d h
  rcases c with ⟨i, j, color⟩
  rcases d with ⟨i', j', color'⟩
  cases color <;> cases color' <;>
    simp [hexBrickPos, Prod.ext_iff] at h ⊢ <;> omega



structure HexAWBrickCycle (n : ℕ) [NeZero n] where
  coord : Fin n → HexAWCoord
  edge : Fin n → Fin 3
  adjacent : ∀ i, hexAWNeighbor (coord i) (edge i) = coord (i + 1)
  coord_injective : Function.Injective coord

namespace HexAWBrickCycle


def heading {n : ℕ} [NeZero n] (C : HexAWBrickCycle n) : Fin n → Fin 6 :=
  fun i => hexAWHeadingMod (C.coord i) (C.edge i)


def direction {n : ℕ} [NeZero n] (C : HexAWBrickCycle n) : Fin n → Fin 4 :=
  fun i => hexBrickDir (C.heading i)

theorem step_eq_sub {n : ℕ} [NeZero n]
    (C : HexAWBrickCycle n) (i : Fin n) :
    stepOf (C.direction i) =
      hexBrickPos (C.coord (i + 1)) - hexBrickPos (C.coord i) := by
  have h := hexBrickPos_neighbor (C.coord i) (C.edge i)
  rw [C.adjacent i] at h
  change hexBrickPos (C.coord (i + 1)) =
      hexBrickPos (C.coord i) + stepOf (C.direction i) at h
  rw [Prod.ext_iff] at h ⊢
  constructor <;>
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at h ⊢ <;>
    omega



theorem closed {n : ℕ} [NeZero n] (C : HexAWBrickCycle n) :
    ∑ i, stepOf (C.direction i) = 0 := by
  rw [Finset.sum_congr rfl (fun i _ => C.step_eq_sub i),
    Finset.sum_sub_distrib]
  have hreindex :
      (∑ i : Fin n, hexBrickPos (C.coord (i + 1))) =
        ∑ i : Fin n, hexBrickPos (C.coord i) :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin n))
      (fun i => hexBrickPos (C.coord i))
  rw [hreindex, sub_self]



theorem pos_eq {n : ℕ} [NeZero n] (C : HexAWBrickCycle n) (k : Fin n) :
    pos C.direction k =
      hexBrickPos (C.coord k) - hexBrickPos (C.coord 0) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  induction k using Fin.induction with
  | zero =>
      rw [StatMech.Onsager.NoDoubleWind.pos_zero]
      simp
  | succ i ih =>
      have hisucc : i.succ = i.castSucc + 1 := by
        apply Fin.ext
        simp
      rw [hisucc,
        StatMech.Onsager.NoDoubleWind.pos_succ C.direction C.closed i.castSucc,
        ← hisucc, ih]
      have hs := C.step_eq_sub i.castSucc
      rw [← hisucc] at hs
      rw [Prod.ext_iff] at hs ⊢
      constructor <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hs ⊢ <;>
        omega


theorem pos_injective {n : ℕ} [NeZero n] (C : HexAWBrickCycle n) :
    Function.Injective (pos C.direction) := by
  intro i j hij
  rw [C.pos_eq i, C.pos_eq j] at hij
  have hbrick : hexBrickPos (C.coord i) = hexBrickPos (C.coord j) := by
    rw [Prod.ext_iff] at hij ⊢
    constructor <;>
      simp only [Prod.fst_sub, Prod.snd_sub] at hij ⊢ <;>
      omega
  exact C.coord_injective (hexBrickPos_injective hbrick)




noncomputable def ofList (coords : List HexAWCoord)
    [NeZero coords.length] (hnodup : coords.Nodup)
    (hadjacent : ∀ i : Fin coords.length, ∃ e : Fin 3,
      hexAWNeighbor (coords.get i) e = coords.get (i + 1)) :
    HexAWBrickCycle coords.length where
  coord := coords.get
  edge i := (hadjacent i).choose
  adjacent i := (hadjacent i).choose_spec
  coord_injective := hnodup.injective_get

end HexAWBrickCycle



def hexBrickTurnPotential : Fin 6 → ℤ := ![0, 2, 1, 0, 2, 1]


def hexHeadingTurn (h : Fin 6) (t : ℤ) : Fin 6 :=
  if t = 1 then h + 1 else h - 1


theorem hexBrickDir_turn_ne_opposite (h : Fin 6) (t : ℤ)
    (ht : t = 1 ∨ t = -1) :
    hexBrickDir (hexHeadingTurn h t) ≠ hexBrickDir h + 2 := by
  rcases ht with rfl | rfl <;> fin_cases h <;>
    decide



theorem hexBrick_local_turn_identity (h : Fin 6) (t : ℤ)
    (ht : t = 1 ∨ t = -1) :
    2 * t + 3 * ons_turnPow (hexBrickDir h)
        (hexBrickDir (hexHeadingTurn h t)) =
      hexBrickTurnPotential (hexHeadingTurn h t) -
        hexBrickTurnPotential h := by
  rcases ht with rfl | rfl <;> fin_cases h <;>
    decide





theorem hexBrick_turn_telescope {n : ℕ} [NeZero n]
    (heading : Fin n → Fin 6) (turn : Fin n → ℤ)
    (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
    (hstep : ∀ i, heading (i + 1) = hexHeadingTurn (heading i) (turn i)) :
    2 * (∑ i, turn i) +
        3 * (∑ i, ons_turnPow (hexBrickDir (heading i))
          (hexBrickDir (heading (i + 1)))) = 0 := by
  have hlocal : ∀ i,
      2 * turn i +
          3 * ons_turnPow (hexBrickDir (heading i))
            (hexBrickDir (heading (i + 1))) =
        hexBrickTurnPotential (heading (i + 1)) -
          hexBrickTurnPotential (heading i) := by
    intro i
    rw [hstep i]
    exact hexBrick_local_turn_identity (heading i) (turn i) (hlegal i)
  calc
    2 * (∑ i, turn i) +
          3 * (∑ i, ons_turnPow (hexBrickDir (heading i))
            (hexBrickDir (heading (i + 1)))) =
        ∑ i, (2 * turn i +
          3 * ons_turnPow (hexBrickDir (heading i))
            (hexBrickDir (heading (i + 1)))) := by
              rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
    _ = ∑ i, (hexBrickTurnPotential (heading (i + 1)) -
          hexBrickTurnPotential (heading i)) := by
            exact Finset.sum_congr rfl (fun i _ => hlocal i)
    _ = 0 := by
      rw [Finset.sum_sub_distrib]
      have hreindex :
          (∑ i : Fin n, hexBrickTurnPotential (heading (i + 1))) =
            ∑ i : Fin n, hexBrickTurnPotential (heading i) :=
        Equiv.sum_comp (Equiv.addRight (1 : Fin n))
          (fun i => hexBrickTurnPotential (heading i))
      rw [hreindex, sub_self]




def HexBrickInteriorOnLeft {n : ℕ} [NeZero n]
    (heading : Fin n → Fin 6) : Prop :=
  StatMech.Onsager.Orientation.leftParity
    (fun i => hexBrickDir (heading i)) 0 = 1



theorem hex_turnSum_eq_neg_six_of_interiorOnLeft {n : ℕ} [NeZero n]
    (heading : Fin n → Fin 6) (turn : Fin n → ℤ)
    (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
    (hstep : ∀ i, heading (i + 1) = hexHeadingTurn (heading i) (turn i))
    (hclosed : ∑ i, stepOf (hexBrickDir (heading i)) = 0)
    (hsimple : Function.Injective
      (pos (fun i => hexBrickDir (heading i))))
    (hn : 3 ≤ n) (horient : HexBrickInteriorOnLeft heading) :
    (∑ i, turn i) = -6 := by
  let d : Fin n → Fin 4 := fun i => hexBrickDir (heading i)
  have hnu : ∀ i, d (i + 1) ≠ d i + 2 := by
    intro i
    rw [show d (i + 1) = hexBrickDir (heading (i + 1)) by rfl,
      hstep i]
    exact hexBrickDir_turn_ne_opposite (heading i) (turn i) (hlegal i)
  have hwalk :=
    StatMech.Onsager.GeneralUmlaufsatz.cornerDiff_eq_sign_mul_turnSum
      d hclosed hsimple hn hnu
  have hpinch :=
    StatMech.Onsager.PinchFree.pinchCount_eq_zero d hclosed hsimple hn
  have hchi : StatMech.Onsager.CellEuler.eulerChar
      (StatMech.Onsager.InteriorCells.interiorCells d hclosed) = 1 := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    subst n
    exact
      StatMech.Onsager.GeneralInterior.eulerChar_interiorCells_eq_one
        d hclosed hsimple
  have hgb :=
    StatMech.Onsager.CellGaussBonnetGlobal.cornerDiff_eq
      (StatMech.Onsager.InteriorCells.interiorCells d hclosed)
  rw [hchi, hpinch] at hgb
  norm_num at hgb
  change StatMech.Onsager.Orientation.leftParity d 0 = 1 at horient
  rw [if_pos horient, one_mul] at hwalk
  have hrect :
      (∑ i, ons_turnPow (d i) (d (i + 1))) = 4 :=
    hwalk.symm.trans hgb
  have htel := hexBrick_turn_telescope heading turn hlegal hstep
  change 2 * (∑ i, turn i) +
      3 * (∑ i, ons_turnPow (d i) (d (i + 1))) = 0 at htel
  omega




theorem hex_turnSum_eq_six_or_neg_six {n : ℕ} [NeZero n]
    (heading : Fin n → Fin 6) (turn : Fin n → ℤ)
    (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
    (hstep : ∀ i, heading (i + 1) = hexHeadingTurn (heading i) (turn i))
    (hclosed : ∑ i, stepOf (hexBrickDir (heading i)) = 0)
    (hsimple : Function.Injective
      (pos (fun i => hexBrickDir (heading i))))
    (hn : 3 ≤ n) :
    (∑ i, turn i) = 6 ∨ (∑ i, turn i) = -6 := by
  let d : Fin n → Fin 4 := fun i => hexBrickDir (heading i)
  have hnu : ∀ i, d (i + 1) ≠ d i + 2 := by
    intro i
    rw [show d (i + 1) = hexBrickDir (heading (i + 1)) by rfl,
      hstep i]
    exact hexBrickDir_turn_ne_opposite (heading i) (turn i) (hlegal i)
  have hrect :=
    StatMech.Onsager.GeneralUmlaufsatz.turnSum_eq_four_or_neg_four
      d hclosed hsimple hn hnu
  have htel := hexBrick_turn_telescope heading turn hlegal hstep
  change 2 * (∑ i, turn i) +
      3 * (∑ i, ons_turnPow (d i) (d (i + 1))) = 0 at htel
  rcases hrect with hfour | hnegfour
  · right
    change (∑ i, turn i) = -6
    change (∑ i, ons_turnPow (d i) (d (i + 1))) = 4 at hfour
    omega
  · left
    change (∑ i, turn i) = 6
    change (∑ i, ons_turnPow (d i) (d (i + 1))) = -4 at hnegfour
    omega


theorem HexAWBrickCycle.turnSum_eq_six_or_neg_six {n : ℕ} [NeZero n]
    (C : HexAWBrickCycle n) (turn : Fin n → ℤ)
    (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
    (hstep : ∀ i, C.heading (i + 1) =
      hexHeadingTurn (C.heading i) (turn i))
    (hn : 3 ≤ n) :
    (∑ i, turn i) = 6 ∨ (∑ i, turn i) = -6 := by
  apply hex_turnSum_eq_six_or_neg_six C.heading turn hlegal hstep
  · simpa [HexAWBrickCycle.direction] using C.closed
  · simpa [HexAWBrickCycle.direction] using C.pos_injective
  · exact hn


theorem HexAWBrickCycle.turnSum_eq_neg_six {n : ℕ} [NeZero n]
    (C : HexAWBrickCycle n) (turn : Fin n → ℤ)
    (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
    (hstep : ∀ i, C.heading (i + 1) =
      hexHeadingTurn (C.heading i) (turn i))
    (hn : 3 ≤ n) (horient : HexBrickInteriorOnLeft C.heading) :
    (∑ i, turn i) = -6 := by
  apply hex_turnSum_eq_neg_six_of_interiorOnLeft
    C.heading turn hlegal hstep
  · simpa [HexAWBrickCycle.direction] using C.closed
  · simpa [HexAWBrickCycle.direction] using C.pos_injective
  · exact hn
  · exact horient

end StatMech.Universality
