/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.GeneralInterior
import Code.Onsager.MasterCorner
import Code.Onsager.PinchFree
import Code.Onsager.TurningTelescope










namespace StatMech.Onsager.GeneralUmlaufsatz

open Finset
open Fin.NatCast
open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.RayFlipV StatMech.Onsager.RayFlipH
  StatMech.Onsager.EdgeUnique StatMech.Onsager.InteriorCells
  StatMech.Onsager.WalkCellBridge StatMech.Onsager.Orientation
  StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellPinch StatMech.Onsager.PinchFree
  StatMech.Onsager.StraightCorner StatMech.Onsager.LeftCornerN
  StatMech.Onsager.LeftCornerE StatMech.Onsager.LeftCornerW
  StatMech.Onsager.LeftCornerS StatMech.Onsager.WalkCornerSum
  StatMech.Onsager.CellGaussBonnetGlobal

variable {n : ℕ} [NeZero n]

theorem zmod2_add_one_add_one (z : ZMod 2) : z = (z + 1) + 1 := by
  rcases (by decide : ∀ w : ZMod 2, w = 0 ∨ w = 1) z with rfl | rfl <;> decide





theorem cornerWeight_rightPattern (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (vx vy : ℤ)
    (hNW : rayParity d (vx - 1) vy = rayParity d (vx - 1) (vy - 1) + 1)
    (hSE : rayParity d vx (vy - 1) = rayParity d (vx - 1) (vy - 1) + 1) :
    cornerWeight (cornerCount (interiorCells d hclosed) (vx, vy)) =
      if rayParity d (vx - 1) vy = 1 then (-1 : ℤ) else 1 := by
  have hnp := pinch_free d hclosed hsimple hn (vx, vy)
  have hcc := cornerCount_interior_eq d hclosed vx vy
  have hmem : ∀ x y : ℤ,
      ((x, y) ∈ interiorCells d hclosed) ↔ rayParity d x y = 1 :=
    fun x y => mem_interiorCells d hclosed (x, y)
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
      (rayParity d (vx - 1) (vy - 1)) with hsw | hsw
  · have hnw : rayParity d (vx - 1) vy = 1 := by rw [hNW, hsw]; decide
    have hse : rayParity d vx (vy - 1) = 1 := by rw [hSE, hsw]; decide
    have hne : rayParity d vx vy = 1 := by
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d vx vy) with hne | hne
      · exfalso
        apply hnp
        right
        simp only [pinchAt, hmem]
        exact ⟨hnw, hse, by simpa [hne], by simpa [hsw]⟩
      · exact hne
    have hcc3 : cornerCount (interiorCells d hclosed) (vx, vy) = 3 := by
      have hz : (cornerCount (interiorCells d hclosed) (vx, vy) : ℤ) = 3 := by
        rw [hcc, hne, hnw, hse, hsw]
        norm_num
      exact_mod_cast hz
    rw [hcc3, hnw]
    decide
  · have hnw : rayParity d (vx - 1) vy = 0 := by rw [hNW, hsw]; decide
    have hse : rayParity d vx (vy - 1) = 0 := by rw [hSE, hsw]; decide
    have hne : rayParity d vx vy = 0 := by
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d vx vy) with hne | hne
      · exact hne
      · exfalso
        apply hnp
        left
        simp only [pinchAt, hmem]
        exact ⟨hne, hsw, by simpa [hnw], by simpa [hse]⟩
    have hcc1 : cornerCount (interiorCells d hclosed) (vx, vy) = 1 := by
      have hz : (cornerCount (interiorCells d hclosed) (vx, vy) : ℤ) = 1 := by
        rw [hcc, hne, hnw, hse, hsw]
        norm_num
      exact_mod_cast hz
    rw [hcc1, hnw]
    decide

theorem cornerWeight_rightPattern_NWSE_NE (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (vx vy : ℤ)
    (hNW : rayParity d (vx - 1) vy = rayParity d vx vy + 1)
    (hSE : rayParity d vx (vy - 1) = rayParity d vx vy + 1) :
    cornerWeight (cornerCount (interiorCells d hclosed) (vx, vy)) =
      if rayParity d (vx - 1) vy = 1 then (-1 : ℤ) else 1 := by
  have hnp := pinch_free d hclosed hsimple hn (vx, vy)
  have hcc := cornerCount_interior_eq d hclosed vx vy
  have hmem : ∀ x y : ℤ,
      ((x, y) ∈ interiorCells d hclosed) ↔ rayParity d x y = 1 :=
    fun x y => mem_interiorCells d hclosed (x, y)
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d vx vy) with hne | hne
  · have hnw : rayParity d (vx - 1) vy = 1 := by rw [hNW, hne]; decide
    have hse : rayParity d vx (vy - 1) = 1 := by rw [hSE, hne]; decide
    have hsw : rayParity d (vx - 1) (vy - 1) = 1 := by
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
          (rayParity d (vx - 1) (vy - 1)) with hsw | hsw
      · exfalso; apply hnp; right; simp only [hmem]
        exact ⟨hnw, hse, by simpa [hne], by simpa [hsw]⟩
      · exact hsw
    have hcc3 : cornerCount (interiorCells d hclosed) (vx, vy) = 3 := by
      have hz : (cornerCount (interiorCells d hclosed) (vx, vy) : ℤ) = 3 := by
        rw [hcc, hne, hnw, hse, hsw]; norm_num
      exact_mod_cast hz
    rw [hcc3, hnw]; decide
  · have hnw : rayParity d (vx - 1) vy = 0 := by rw [hNW, hne]; decide
    have hse : rayParity d vx (vy - 1) = 0 := by rw [hSE, hne]; decide
    have hsw : rayParity d (vx - 1) (vy - 1) = 0 := by
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
          (rayParity d (vx - 1) (vy - 1)) with hsw | hsw
      · exact hsw
      · exfalso; apply hnp; left; simp only [hmem]
        exact ⟨hne, hsw, by simpa [hnw], by simpa [hse]⟩
    have hcc1 : cornerCount (interiorCells d hclosed) (vx, vy) = 1 := by
      have hz : (cornerCount (interiorCells d hclosed) (vx, vy) : ℤ) = 1 := by
        rw [hcc, hne, hnw, hse, hsw]; norm_num
      exact_mod_cast hz
    rw [hcc1, hnw]; decide

theorem cornerWeight_rightPattern_NESW_NW (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (vx vy : ℤ)
    (hNE : rayParity d vx vy = rayParity d (vx - 1) vy + 1)
    (hSW : rayParity d (vx - 1) (vy - 1) = rayParity d (vx - 1) vy + 1) :
    cornerWeight (cornerCount (interiorCells d hclosed) (vx, vy)) =
      if rayParity d vx vy = 1 then (-1 : ℤ) else 1 := by
  have hnp := pinch_free d hclosed hsimple hn (vx, vy)
  have hcc := cornerCount_interior_eq d hclosed vx vy
  have hmem : ∀ x y : ℤ,
      ((x, y) ∈ interiorCells d hclosed) ↔ rayParity d x y = 1 :=
    fun x y => mem_interiorCells d hclosed (x, y)
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
      (rayParity d (vx - 1) vy) with hnw | hnw
  · have hne : rayParity d vx vy = 1 := by rw [hNE, hnw]; decide
    have hsw : rayParity d (vx - 1) (vy - 1) = 1 := by rw [hSW, hnw]; decide
    have hse : rayParity d vx (vy - 1) = 1 := by
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d vx (vy - 1)) with hse | hse
      · exfalso; apply hnp; left; simp only [hmem]
        exact ⟨hne, hsw, by simpa [hnw], by simpa [hse]⟩
      · exact hse
    have hcc3 : cornerCount (interiorCells d hclosed) (vx, vy) = 3 := by
      have hz : (cornerCount (interiorCells d hclosed) (vx, vy) : ℤ) = 3 := by
        rw [hcc, hne, hnw, hse, hsw]; norm_num
      exact_mod_cast hz
    rw [hcc3, hne]; decide
  · have hne : rayParity d vx vy = 0 := by rw [hNE, hnw]; decide
    have hsw : rayParity d (vx - 1) (vy - 1) = 0 := by rw [hSW, hnw]; decide
    have hse : rayParity d vx (vy - 1) = 0 := by
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d vx (vy - 1)) with hse | hse
      · exact hse
      · exfalso; apply hnp; right; simp only [hmem]
        exact ⟨hnw, hse, by simpa [hne], by simpa [hsw]⟩
    have hcc1 : cornerCount (interiorCells d hclosed) (vx, vy) = 1 := by
      have hz : (cornerCount (interiorCells d hclosed) (vx, vy) : ℤ) = 1 := by
        rw [hcc, hne, hnw, hse, hsw]; norm_num
      exact_mod_cast hz
    rw [hcc1, hne]; decide

theorem cornerWeight_rightPattern_NESW_SE (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (vx vy : ℤ)
    (hNE : rayParity d vx vy = rayParity d vx (vy - 1) + 1)
    (hSW : rayParity d (vx - 1) (vy - 1) = rayParity d vx (vy - 1) + 1) :
    cornerWeight (cornerCount (interiorCells d hclosed) (vx, vy)) =
      if rayParity d vx vy = 1 then (-1 : ℤ) else 1 := by
  have hnp := pinch_free d hclosed hsimple hn (vx, vy)
  have hcc := cornerCount_interior_eq d hclosed vx vy
  have hmem : ∀ x y : ℤ,
      ((x, y) ∈ interiorCells d hclosed) ↔ rayParity d x y = 1 :=
    fun x y => mem_interiorCells d hclosed (x, y)
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
      (rayParity d vx (vy - 1)) with hse | hse
  · have hne : rayParity d vx vy = 1 := by rw [hNE, hse]; decide
    have hsw : rayParity d (vx - 1) (vy - 1) = 1 := by rw [hSW, hse]; decide
    have hnw : rayParity d (vx - 1) vy = 1 := by
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d (vx - 1) vy) with hnw | hnw
      · exfalso; apply hnp; left; simp only [hmem]
        exact ⟨hne, hsw, by simpa [hnw], by simpa [hse]⟩
      · exact hnw
    have hcc3 : cornerCount (interiorCells d hclosed) (vx, vy) = 3 := by
      have hz : (cornerCount (interiorCells d hclosed) (vx, vy) : ℤ) = 3 := by
        rw [hcc, hne, hnw, hse, hsw]; norm_num
      exact_mod_cast hz
    rw [hcc3, hne]; decide
  · have hne : rayParity d vx vy = 0 := by rw [hNE, hse]; decide
    have hsw : rayParity d (vx - 1) (vy - 1) = 0 := by rw [hSW, hse]; decide
    have hnw : rayParity d (vx - 1) vy = 0 := by
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d (vx - 1) vy) with hnw | hnw
      · exact hnw
      · exfalso; apply hnp; right; simp only [hmem]
        exact ⟨hnw, hse, by simpa [hne], by simpa [hsw]⟩
    have hcc1 : cornerCount (interiorCells d hclosed) (vx, vy) = 1 := by
      have hz : (cornerCount (interiorCells d hclosed) (vx, vy) : ℤ) = 1 := by
        rw [hcc, hne, hnw, hse, hsw]; norm_num
      exact_mod_cast hz
    rw [hcc1, hne]; decide



theorem rightTurn_ES (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) (i : Fin n)
    (hei : d i = 0) (he : d (i + 1) = 3) :
    leftParity d i = leftParity d (i + 1) ∧
      cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) =
        -(if leftParity d (i + 1) = 1 then (1 : ℤ) else -1) := by
  set vx := (pos d (i + 1)).1
  set vy := (pos d (i + 1)).2
  have hposi : pos d i = (vx - 1, vy) := by
    have hs := pos_succ d hclosed i
    rw [hei] at hs
    rw [Prod.ext_iff]
    constructor <;> simp only [vx, vy, hs, stepOf, Prod.fst_add, Prod.snd_add] <;> omega
  have hposi2 : pos d (i + 1 + 1) = (vx, vy - 1) := by
    have hs := pos_succ d hclosed (i + 1)
    rw [he] at hs
    rw [Prod.ext_iff]
    constructor <;> simp only [vx, vy, hs, stepOf, Prod.fst_add, Prod.snd_add] <;> omega
  have hmid : i ∈ midSet d (vx - 1) vy := by
    simp only [midSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Or.inl hei, ?_, ?_⟩
    · rw [hposi]
      simp [vx]
    · rw [hposi]
  have hstr : i + 1 ∈ straddleSet d (vx - 1) (vy - 1) := by
    simp only [straddleSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Or.inr he, ?_, ?_, ?_⟩
    · simp [vx]
    · rw [hposi2]
      simp [vy]
    · rw [hposi2]
      simp [vy]
  have hSWNW : rayParity d (vx - 1) (vy - 1) = rayParity d (vx - 1) vy + 1 := by
    have h := rayParity_vflip d (vx - 1) (vy - 1)
      (by
        rw [show vy - 1 + 1 = vy by ring]
        exact midSet_card_odd_of_mem d hclosed hsimple hn (vx - 1) vy i hmid)
    rwa [show vy - 1 + 1 = vy by ring] at h
  have hSWSE : rayParity d (vx - 1) (vy - 1) = rayParity d vx (vy - 1) + 1 := by
    have h := rayParity_hflip d hclosed (vx - 1) (vy - 1)
      (straddleSet_card_odd_of_mem d hclosed hsimple hn (vx - 1) (vy - 1) (i + 1) hstr)
    rwa [show vx - 1 + 1 = vx by ring] at h
  have hNW : rayParity d (vx - 1) vy = rayParity d (vx - 1) (vy - 1) + 1 := by
    calc
      rayParity d (vx - 1) vy = (rayParity d (vx - 1) vy + 1) + 1 :=
        zmod2_add_one_add_one _
      _ = rayParity d (vx - 1) (vy - 1) + 1 := by rw [hSWNW]
  have hSE : rayParity d vx (vy - 1) = rayParity d (vx - 1) (vy - 1) + 1 := by
    calc
      rayParity d vx (vy - 1) = (rayParity d vx (vy - 1) + 1) + 1 :=
        zmod2_add_one_add_one _
      _ = rayParity d (vx - 1) (vy - 1) + 1 := by rw [hSWSE]
  have hlki : leftParity d i = rayParity d (vx - 1) vy := by
    unfold leftParity
    rw [hei, hposi]
    rfl
  have hlki1 : leftParity d (i + 1) = rayParity d vx (vy - 1) := by
    unfold leftParity
    rw [he]
    rfl
  constructor
  · rw [hlki, hlki1, hNW, hSE]
  · have hw := cornerWeight_rightPattern d hclosed hsimple hn vx vy hNW hSE
    have hp : pos d (i + 1) = (vx, vy) := by exact Prod.ext rfl rfl
    rw [hp]
    rw [hw, hlki1, hSE, hNW]
    by_cases h : rayParity d (vx - 1) (vy - 1) + 1 = 1 <;> simp [h]

theorem rightTurn_SW (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) (i : Fin n)
    (hei : d i = 3) (he : d (i + 1) = 2) :
    leftParity d i = leftParity d (i + 1) ∧
      cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) =
        -(if leftParity d (i + 1) = 1 then (1 : ℤ) else -1) := by
  set vx := (pos d (i + 1)).1
  set vy := (pos d (i + 1)).2
  have hposi : pos d i = (vx, vy + 1) := by
    have hs := pos_succ d hclosed i
    rw [hei] at hs
    rw [Prod.ext_iff]
    constructor <;> simp only [vx, vy, hs, stepOf, Prod.fst_add, Prod.snd_add] <;> omega
  have hposi2 : pos d (i + 1 + 1) = (vx - 1, vy) := by
    have hs := pos_succ d hclosed (i + 1)
    rw [he] at hs
    rw [Prod.ext_iff]
    constructor <;> simp only [vx, vy, hs, stepOf, Prod.fst_add, Prod.snd_add] <;> omega
  have hstr : i ∈ straddleSet d (vx - 1) vy := by
    simp only [straddleSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Or.inr hei, ?_, ?_, ?_⟩
    · rw [hposi]; simp [vx, vy]
    · rw [hposi]; simp [vx, vy]
    · rw [hposi]; simp [vx, vy]
  have hmid : i + 1 ∈ midSet d (vx - 1) vy := by
    simp only [midSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Or.inr he, ?_, ?_⟩
    · rw [hposi2]; simp [vx]
    · simp [vy]
  have hNWNE : rayParity d (vx - 1) vy = rayParity d vx vy + 1 := by
    have h := rayParity_hflip d hclosed (vx - 1) vy
      (straddleSet_card_odd_of_mem d hclosed hsimple hn (vx - 1) vy i hstr)
    rwa [show vx - 1 + 1 = vx by ring] at h
  have hSW : rayParity d (vx - 1) (vy - 1) = rayParity d (vx - 1) vy + 1 := by
    have h := rayParity_vflip d (vx - 1) (vy - 1)
      (by
        rw [show vy - 1 + 1 = vy by ring]
        exact midSet_card_odd_of_mem d hclosed hsimple hn (vx - 1) vy (i + 1) hmid)
    rwa [show vy - 1 + 1 = vy by ring] at h
  have hNE : rayParity d vx vy = rayParity d (vx - 1) vy + 1 := by
    calc
      rayParity d vx vy = (rayParity d vx vy + 1) + 1 := zmod2_add_one_add_one _
      _ = rayParity d (vx - 1) vy + 1 := by rw [hNWNE]
  have hlki : leftParity d i = rayParity d vx vy := by
    unfold leftParity; rw [hei, hposi]; simp [leftCell]
  have hlki1 : leftParity d (i + 1) = rayParity d (vx - 1) (vy - 1) := by
    unfold leftParity; rw [he]; rfl
  constructor
  · rw [hlki, hlki1, hNE, hSW]
  · have hw := cornerWeight_rightPattern_NESW_NW d hclosed hsimple hn vx vy hNE hSW
    have hp : pos d (i + 1) = (vx, vy) := Prod.ext rfl rfl
    rw [hp, hw, hlki1, hSW, hNE]
    by_cases h : rayParity d (vx - 1) vy + 1 = 1 <;> simp [h]

theorem rightTurn_WN (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) (i : Fin n)
    (hei : d i = 2) (he : d (i + 1) = 1) :
    leftParity d i = leftParity d (i + 1) ∧
      cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) =
        -(if leftParity d (i + 1) = 1 then (1 : ℤ) else -1) := by
  set vx := (pos d (i + 1)).1
  set vy := (pos d (i + 1)).2
  have hposi : pos d i = (vx + 1, vy) := by
    have hs := pos_succ d hclosed i
    rw [hei] at hs
    rw [Prod.ext_iff]
    constructor <;> simp only [vx, vy, hs, stepOf, Prod.fst_add, Prod.snd_add] <;> omega
  have hposi2 : pos d (i + 1 + 1) = (vx, vy + 1) := by
    have hs := pos_succ d hclosed (i + 1)
    rw [he] at hs
    rw [Prod.ext_iff]
    constructor <;> simp only [vx, vy, hs, stepOf, Prod.fst_add, Prod.snd_add] <;> omega
  have hmid : i ∈ midSet d vx vy := by
    simp only [midSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Or.inr hei, ?_, ?_⟩
    · rw [hposi]; simp [vx]
    · rw [hposi]
  have hstr : i + 1 ∈ straddleSet d (vx - 1) vy := by
    simp only [straddleSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Or.inl he, ?_, ?_, ?_⟩
    · simp [vx]
    · rw [hposi2]; simp [vx, vy]
    · rw [hposi2]; simp [vx, vy]
  have hSE : rayParity d vx (vy - 1) = rayParity d vx vy + 1 := by
    have h := rayParity_vflip d vx (vy - 1)
      (by
        rw [show vy - 1 + 1 = vy by ring]
        exact midSet_card_odd_of_mem d hclosed hsimple hn vx vy i hmid)
    rwa [show vy - 1 + 1 = vy by ring] at h
  have hNW : rayParity d (vx - 1) vy = rayParity d vx vy + 1 := by
    have h := rayParity_hflip d hclosed (vx - 1) vy
      (straddleSet_card_odd_of_mem d hclosed hsimple hn (vx - 1) vy (i + 1) hstr)
    rwa [show vx - 1 + 1 = vx by ring] at h
  have hlki : leftParity d i = rayParity d vx (vy - 1) := by
    unfold leftParity; rw [hei, hposi]; simp [leftCell]
  have hlki1 : leftParity d (i + 1) = rayParity d (vx - 1) vy := by
    unfold leftParity; rw [he]; rfl
  constructor
  · rw [hlki, hlki1, hSE, hNW]
  · have hw := cornerWeight_rightPattern_NWSE_NE d hclosed hsimple hn vx vy hNW hSE
    have hp : pos d (i + 1) = (vx, vy) := Prod.ext rfl rfl
    rw [hp, hw, hlki1]
    by_cases h : rayParity d (vx - 1) vy = 1 <;> simp [h]

theorem rightTurn_NE (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) (i : Fin n)
    (hei : d i = 1) (he : d (i + 1) = 0) :
    leftParity d i = leftParity d (i + 1) ∧
      cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) =
        -(if leftParity d (i + 1) = 1 then (1 : ℤ) else -1) := by
  set vx := (pos d (i + 1)).1
  set vy := (pos d (i + 1)).2
  have hposi : pos d i = (vx, vy - 1) := by
    have hs := pos_succ d hclosed i
    rw [hei] at hs
    rw [Prod.ext_iff]
    constructor <;> simp only [vx, vy, hs, stepOf, Prod.fst_add, Prod.snd_add] <;> omega
  have hposi2 : pos d (i + 1 + 1) = (vx + 1, vy) := by
    have hs := pos_succ d hclosed (i + 1)
    rw [he] at hs
    rw [Prod.ext_iff]
    constructor <;> simp only [vx, vy, hs, stepOf, Prod.fst_add, Prod.snd_add] <;> omega
  have hstr : i ∈ straddleSet d (vx - 1) (vy - 1) := by
    simp only [straddleSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Or.inl hei, ?_, ?_, ?_⟩
    · rw [hposi]; simp [vx, vy]
    · rw [hposi]; simp [vx, vy]
    · rw [hposi]; simp [vx, vy]
  have hmid : i + 1 ∈ midSet d vx vy := by
    simp only [midSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Or.inl he, ?_, ?_⟩
    · rw [hposi2]; simp [vx]
    · simp [vy]
  have hSW : rayParity d (vx - 1) (vy - 1) = rayParity d vx (vy - 1) + 1 := by
    have h := rayParity_hflip d hclosed (vx - 1) (vy - 1)
      (straddleSet_card_odd_of_mem d hclosed hsimple hn (vx - 1) (vy - 1) i hstr)
    rwa [show vx - 1 + 1 = vx by ring] at h
  have hSENE : rayParity d vx (vy - 1) = rayParity d vx vy + 1 := by
    have h := rayParity_vflip d vx (vy - 1)
      (by
        rw [show vy - 1 + 1 = vy by ring]
        exact midSet_card_odd_of_mem d hclosed hsimple hn vx vy (i + 1) hmid)
    rwa [show vy - 1 + 1 = vy by ring] at h
  have hNE : rayParity d vx vy = rayParity d vx (vy - 1) + 1 := by
    calc
      rayParity d vx vy = (rayParity d vx vy + 1) + 1 := zmod2_add_one_add_one _
      _ = rayParity d vx (vy - 1) + 1 := by rw [hSENE]
  have hlki : leftParity d i = rayParity d (vx - 1) (vy - 1) := by
    unfold leftParity; rw [hei, hposi]; rfl
  have hlki1 : leftParity d (i + 1) = rayParity d vx vy := by
    unfold leftParity; rw [he]; rfl
  constructor
  · rw [hlki, hlki1, hSW, hNE]
  · have hw := cornerWeight_rightPattern_NESW_SE d hclosed hsimple hn vx vy hNE hSW
    have hp : pos d (i + 1) = (vx, vy) := Prod.ext rfl rfl
    rw [hp, hw, hlki1]
    by_cases h : rayParity d vx vy = 1 <;> simp [h]


theorem rightTurn (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) (i : Fin n)
    (hr : d (i + 1) - d i = 3) :
    leftParity d i = leftParity d (i + 1) ∧
      cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) =
        -(if leftParity d (i + 1) = 1 then (1 : ℤ) else -1) := by
  rcases (by decide : ∀ w : Fin 4, w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) (d i) with
    hdi | hdi | hdi | hdi
  · have hdn : d (i + 1) = 3 := by
      have h := sub_eq_iff_eq_add.mp hr
      simpa [hdi, add_comm] using h
    exact rightTurn_ES d hclosed hsimple hn i hdi hdn
  · have hdn : d (i + 1) = 0 := by
      have h := sub_eq_iff_eq_add.mp hr
      simpa [hdi, add_comm] using h
    exact rightTurn_NE d hclosed hsimple hn i hdi hdn
  · have hdn : d (i + 1) = 1 := by
      have h := sub_eq_iff_eq_add.mp hr
      simpa [hdi, add_comm] using h
    exact rightTurn_WN d hclosed hsimple hn i hdi hdn
  · have hdn : d (i + 1) = 2 := by
      have h := sub_eq_iff_eq_add.mp hr
      simpa [hdi, add_comm] using h
    exact rightTurn_SW d hclosed hsimple hn i hdi hdn


theorem turn_cases (mu nu : Fin 4) (hnu : nu ≠ mu + 2) :
    nu - mu = 0 ∨ nu - mu = 1 ∨ nu - mu = 3 := by
  rcases (by decide : ∀ w : Fin 4, w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) (nu - mu) with
    h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exfalso
    apply hnu
    have heq := sub_eq_iff_eq_add.mp h
    simpa [add_comm] using heq
  · exact Or.inr (Or.inr h)

theorem ons_turnPow_eq_of_turn_zero {mu nu : Fin 4} (h : nu - mu = 0) :
    ons_turnPow mu nu = 0 := by
  have heq : nu = mu := sub_eq_zero.mp h
  simp [ons_turnPow, heq]

theorem ons_turnPow_eq_of_turn_one {mu nu : Fin 4} (h : nu - mu = 1) :
    ons_turnPow mu nu = 1 := by
  have heq := sub_eq_iff_eq_add.mp h
  have heq' : nu = mu + 1 := by simpa [add_comm] using heq
  rw [heq']
  fin_cases mu <;> decide

theorem ons_turnPow_eq_of_turn_three {mu nu : Fin 4} (h : nu - mu = 3) :
    ons_turnPow mu nu = -1 := by
  have heq := sub_eq_iff_eq_add.mp h
  have heq' : nu = mu + 3 := by simpa [add_comm] using heq
  rw [heq']
  fin_cases mu <;> decide


theorem leftParity_step_general (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (hnu : ∀ i, d (i + 1) ≠ d i + 2) (i : Fin n) :
    leftParity d i = leftParity d (i + 1) := by
  rcases turn_cases (d i) (d (i + 1)) (hnu i) with h0 | h1 | h3
  · exact leftCell_parity_eq_of_straight d hclosed hsimple i (sub_eq_zero.mp h0)
  · unfold leftParity
    rw [leftCell_eq_of_leftTurn d hclosed i h1]
  · exact (rightTurn d hclosed hsimple hn i h3).1



theorem leftParity_const_general (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (hnu : ∀ i, d (i + 1) ≠ d i + 2) (k : Fin n) :
    leftParity d k = leftParity d 0 := by
  have haux : ∀ m : ℕ, leftParity d (Nat.cast m) = leftParity d 0 := by
    intro m
    induction m with
    | zero => simp
    | succ j ih =>
        have hcast : (Nat.cast (j + 1) : Fin n) = Nat.cast j + 1 := by
          apply Fin.ext
          rw [Fin.val_natCast, Fin.val_add, Fin.val_natCast, Fin.val_one',
            Nat.add_mod (j % n) (1 % n) n, Nat.mod_mod_of_dvd _ (dvd_refl n),
            Nat.mod_mod_of_dvd _ (dvd_refl n), ← Nat.add_mod]
        rw [hcast, ← leftParity_step_general d hclosed hsimple hn hnu (Nat.cast j), ih]
  have h := haux k.val
  rwa [Fin.cast_val_eq_self] at h



theorem cornerWeight_master_general (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (hnu : ∀ i, d (i + 1) ≠ d i + 2) (i : Fin n) :
    cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) =
      (if leftParity d 0 = 1 then (1 : ℤ) else -1) *
        ons_turnPow (d i) (d (i + 1)) := by
  rcases turn_cases (d i) (d (i + 1)) (hnu i) with h0 | h1 | h3
  · have hst := sub_eq_zero.mp h0
    rw [cornerWeight_straight d hclosed hsimple i hst,
      ons_turnPow_eq_of_turn_zero h0]
    ring
  · have hlp : rayParity d (leftCell (d (i + 1)) (pos d (i + 1))).1
        (leftCell (d (i + 1)) (pos d (i + 1))).2 = leftParity d 0 :=
      leftParity_const_general d hclosed hsimple hn hnu (i + 1)
    have hei : d i = d (i + 1) - 1 := by
      rw [eq_sub_iff_add_eq, sub_eq_iff_eq_add.mp h1]
      abel
    rw [ons_turnPow_eq_of_turn_one h1, mul_one]
    rcases (by decide : ∀ w : Fin 4, w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3)
        (d (i + 1)) with hd | hd | hd | hd
    · rw [cornerWeight_leftTurn_E d hclosed hsimple hn i (by rw [hei, hd]; decide) hd, hlp]
    · rw [cornerWeight_leftTurn_N d hclosed hsimple hn i (by rw [hei, hd]; decide) hd, hlp]
    · rw [cornerWeight_leftTurn_W d hclosed hsimple hn i (by rw [hei, hd]; decide) hd, hlp]
    · rw [cornerWeight_leftTurn_S d hclosed hsimple hn i (by rw [hei, hd]; decide) hd, hlp]
  · have hr := (rightTurn d hclosed hsimple hn i h3).2
    have hlp := leftParity_const_general d hclosed hsimple hn hnu (i + 1)
    rw [hr, hlp, ons_turnPow_eq_of_turn_three h3]
    ring


theorem cornerDiff_eq_sign_mul_turnSum (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
    cornerDiff (interiorCells d hclosed) =
      (if leftParity d 0 = 1 then (1 : ℤ) else -1) *
        ∑ i, ons_turnPow (d i) (d (i + 1)) := by
  rw [cornerDiff_interior_eq_walk_sum d hclosed hsimple,
    ← Equiv.sum_comp (Equiv.addRight (1 : Fin n))
      (fun k => cornerWeight (cornerCount (interiorCells d hclosed) (pos d k)))]
  simp only [Equiv.coe_addRight]
  rw [Finset.sum_congr rfl
    (fun i _ => cornerWeight_master_general d hclosed hsimple hn hnu i),
    ← Finset.mul_sum]



theorem turnSum_eq_four_or_neg_four' {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
    (∑ i, ons_turnPow (d i) (d (i + 1))) = 4 ∨
      (∑ i, ons_turnPow (d i) (d (i + 1))) = -4 := by
  have hn : 3 ≤ m + 3 := by omega
  have hwalk := cornerDiff_eq_sign_mul_turnSum d hclosed hsimple hn hnu
  have hgb := cornerDiff_eq (interiorCells d hclosed)
  have hpinch := pinchCount_eq_zero d hclosed hsimple hn
  have hchi :=
    StatMech.Onsager.GeneralInterior.eulerChar_interiorCells_eq_one d hclosed hsimple
  rw [hchi, hpinch] at hgb
  norm_num at hgb
  by_cases hleft : leftParity d 0 = 1
  · left
    rw [if_pos hleft, one_mul] at hwalk
    exact hwalk.symm.trans hgb
  · right
    rw [if_neg hleft] at hwalk
    omega

theorem turnSum_eq_four_or_neg_four (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
    (∑ i, ons_turnPow (d i) (d (i + 1))) = 4 ∨
      (∑ i, ons_turnPow (d i) (d (i + 1))) = -4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact turnSum_eq_four_or_neg_four' d hclosed hsimple hnu



theorem turnWeightProduct_eq_neg_one (omega : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I) (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
    ∏ i, ons_turnW omega (d i) (d (i + 1)) = -1 := by
  calc
    (∏ i, ons_turnW omega (d i) (d (i + 1))) =
        ∏ i, omega ^ ons_turnPow (d i) (d (i + 1)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact ons_turnW_eq_zpow omega _ _ (hnu i)
    _ = omega ^ (∑ i, ons_turnPow (d i) (d (i + 1))) :=
      ons_prod_zpow omega homega _ _
    _ = -1 := by
      rcases turnSum_eq_four_or_neg_four d hclosed hsimple hn hnu with h | h
      · rw [h]
        simpa [zpow_ofNat] using ons_omega_pow_four omega hI
      · rw [h, show (-4 : ℤ) = -(4 : ℤ) by norm_num, zpow_neg,
          show omega ^ (4 : ℤ) = omega ^ (4 : ℕ) by exact zpow_natCast omega 4,
          ons_omega_pow_four omega hI]
        norm_num

end StatMech.Onsager.GeneralUmlaufsatz
