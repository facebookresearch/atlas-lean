/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.IsingFermionicSquareBox
import Mathlib.Logic.Equiv.Fintype

namespace StatMech.Universality

open Finset SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareLeftVerticalUpper (n : Nat) (_hn : 0 < n)
    (k : Fin (2 * n)) : (fkSquareBoxPlanar n).V :=
  ⟨![-(n : Int), -(n : Int) + (k.val : Int) + 1], by
    intro i
    fin_cases i
    · simp
    · simp
      have hk := k.isLt
      omega⟩

theorem fkIsingSquareLeftVerticalUpper_south_available
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareLeftVerticalUpper n hn k) .south := by
  simp [fkIsingSquareDirectionAvailable, fkIsingSquareLeftVerticalUpper]

def fkIsingSquareLeftVerticalLower (n : Nat) (_hn : 0 < n)
    (k : Fin (2 * n)) : (fkSquareBoxPlanar n).V :=
  ⟨![-(n : Int), -(n : Int) + (k.val : Int)], by
    intro i
    fin_cases i
    · simp
    · simp
      have hk := k.isLt
      omega⟩

theorem fkIsingSquareLeftVerticalLower_north_available
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareLeftVerticalLower n hn k) .north := by
  simp [fkIsingSquareDirectionAvailable, fkIsingSquareLeftVerticalLower]
  have hk := k.isLt
  omega

theorem fkIsingSquareMarkedB_east_available (n : Nat) (hn : 0 < n) :
    fkIsingSquareDirectionAvailable n (fkIsingSquareMarkedB n) .east := by
  simp [fkIsingSquareDirectionAvailable, fkIsingSquareMarkedB]
  omega

theorem fkIsingSquareMarkedA_east_available (n : Nat) (hn : 0 < n) :
    fkIsingSquareDirectionAvailable n (fkIsingSquareMarkedA n) .east := by
  simp [fkIsingSquareDirectionAvailable, fkIsingSquareMarkedA]
  omega

def fkIsingSquareLeftVerticalEdge (n : Nat) (hn : 0 < n)
    (k : Fin (2 * n)) : FKIsingMedialVertex (fkSquareBoxPlanar n) :=
  fkIsingSquareDirectionEdge n (fkIsingSquareLeftVerticalUpper n hn k) .south
    (fkIsingSquareLeftVerticalUpper_south_available n hn k)

theorem fkIsingSquareDirectionDart_endpoint_congr (n : Nat)
    {u v : (fkSquareBoxPlanar n).V} (h : u = v)
    (d : FKIsingSquareDirection)
    (hu : fkIsingSquareDirectionAvailable n u d)
    (hv : fkIsingSquareDirectionAvailable n v d)
    (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareDirectionDart n u d hu turn =
      fkIsingSquareDirectionDart n v d hv turn := by
  subst v
  rfl

inductive FKIsingSquareWiredBoundaryDartIndex (n : Nat)
  | bottom
  | west (k : Fin (2 * n))
  | north (k : Fin (2 * n))
  | top
deriving DecidableEq, Fintype

def fkIsingSquareWiredBoundaryDart (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredBoundaryDartIndex n →
      FKIsingMedialDart (fkSquareBoxPlanar n)
  | .bottom => fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n) .east
      (fkIsingSquareMarkedA_east_available n hn) .clockwise
  | .west k => fkIsingSquareDirectionDart n
      (fkIsingSquareLeftVerticalLower n hn k) .north
      (fkIsingSquareLeftVerticalLower_north_available n hn k) .counterclockwise
  | .north k => fkIsingSquareDirectionDart n
      (fkIsingSquareLeftVerticalUpper n hn k) .south
      (fkIsingSquareLeftVerticalUpper_south_available n hn k) .clockwise
  | .top => fkIsingSquareDirectionDart n (fkIsingSquareMarkedB n) .east
      (fkIsingSquareMarkedB_east_available n hn) .counterclockwise

theorem fkIsingSquareDart_key_injective (n : Nat) :
    Function.Injective (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
      (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
        d.2)) := by
  intro d f h
  rcases Prod.mk.inj h with ⟨he, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hdr, hs⟩
  apply Prod.ext
  · calc
      d.1 = fkIsingSquareDirectionEdge n (fkIsingSquareDartEndpoint n d)
          (fkIsingSquareDartDirection n d)
          (fkIsingSquareDartDirection_available n d) :=
        (fkIsingSquareDirectionEdge_reconstruct n d).symm
      _ = fkIsingSquareDirectionEdge n (fkIsingSquareDartEndpoint n f)
          (fkIsingSquareDartDirection n f)
          (fkIsingSquareDartDirection_available n f) := by congr
      _ = f.1 := fkIsingSquareDirectionEdge_reconstruct n f
  · exact hs

theorem fkIsingSquareWiredBoundaryDart_injective (n : Nat) (hn : 0 < n) :
    Function.Injective (fkIsingSquareWiredBoundaryDart n hn) := by
  intro i j h
  have hkey := congrArg (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
      (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
        d.2)) h
  cases i <;> cases j <;>
    simp [fkIsingSquareWiredBoundaryDart, fkIsingSquareMarkedA,
      fkIsingSquareMarkedB, fkIsingSquareLeftVerticalLower,
      fkIsingSquareLeftVerticalUpper] at hkey ⊢
  all_goals try
    have hv := congrArg (fun x : (fkSquareBoxPlanar n).V => x.1 1) hkey.1
    simp at hv
    omega

def fkIsingSquareWiredBoundaryEmbedding (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredBoundaryDartIndex n ↪
      FKIsingMedialDart (fkSquareBoxPlanar n) :=
  ⟨fkIsingSquareWiredBoundaryDart n hn,
    fkIsingSquareWiredBoundaryDart_injective n hn⟩

def fkIsingSquareWiredShift (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredBoundaryDartIndex n →
      FKIsingSquareWiredBoundaryDartIndex n
  | .bottom => .bottom
  | .west k => if hk : k.val = 0 then .top
      else .north ⟨k.val - 1, by omega⟩
  | .north k => .west k
  | .top => .north ⟨2 * n - 1, by omega⟩

def fkIsingSquareWiredShiftInv (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredBoundaryDartIndex n →
      FKIsingSquareWiredBoundaryDartIndex n
  | .bottom => .bottom
  | .west k => .north k
  | .north k => if hk : k.val + 1 < 2 * n then
      .west ⟨k.val + 1, hk⟩ else .top
  | .top => .west ⟨0, by omega⟩

theorem fkIsingSquareWiredShift_left_inv (n : Nat) (hn : 0 < n) :
    Function.LeftInverse (fkIsingSquareWiredShiftInv n hn)
      (fkIsingSquareWiredShift n hn) := by
  intro i
  cases i with
  | bottom => rfl
  | west k =>
      simp only [fkIsingSquareWiredShift]
      split_ifs with hk
      · simp only [fkIsingSquareWiredShiftInv]
        congr 1
        apply Fin.ext
        exact hk.symm
      · simp only [fkIsingSquareWiredShiftInv]
        split_ifs with hlt
        · congr
          omega
        · omega
  | north k =>
      simp [fkIsingSquareWiredShift, fkIsingSquareWiredShiftInv]
  | top =>
      simp only [fkIsingSquareWiredShift, fkIsingSquareWiredShiftInv]
      split_ifs with hlt
      · omega
      · rfl

theorem fkIsingSquareWiredShift_right_inv (n : Nat) (hn : 0 < n) :
    Function.RightInverse (fkIsingSquareWiredShiftInv n hn)
      (fkIsingSquareWiredShift n hn) := by
  intro i
  cases i with
  | bottom => rfl
  | west k =>
      simp [fkIsingSquareWiredShift, fkIsingSquareWiredShiftInv]
  | north k =>
      simp only [fkIsingSquareWiredShiftInv]
      split_ifs with hlt
      · simp only [fkIsingSquareWiredShift]
        rw [dif_neg (by omega : k.val + 1 ≠ 0)]
        congr 1
      · have hk : k.val = 2 * n - 1 := by omega
        simp only [fkIsingSquareWiredShift]
        congr 1
        apply Fin.ext
        exact hk.symm
  | top =>
      simp [fkIsingSquareWiredShift, fkIsingSquareWiredShiftInv]

def fkIsingSquareWiredShiftEquiv (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingSquareWiredBoundaryDartIndex n) where
  toFun := fkIsingSquareWiredShift n hn
  invFun := fkIsingSquareWiredShiftInv n hn
  left_inv := fkIsingSquareWiredShift_left_inv n hn
  right_inv := fkIsingSquareWiredShift_right_inv n hn

def fkIsingSquareWiredShiftDartEquiv (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingMedialDart (fkSquareBoxPlanar n)) :=
  (fkIsingSquareWiredShiftEquiv n hn).viaFintypeEmbedding
    (fkIsingSquareWiredBoundaryEmbedding n hn)



def fkIsingSquareWiredBondMateEquiv (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingMedialDart (fkSquareBoxPlanar n)) :=
  (fkIsingSquareWiredShiftDartEquiv n hn) *
    (fkIsingSquareBondMateEquiv n hn) *
      (fkIsingSquareWiredShiftDartEquiv n hn).symm

def fkIsingSquareWiredBondMate (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :=
  fkIsingSquareWiredBondMateEquiv n hn d

private theorem perm_conjugate_involutive {X : Type*}
    (sigma B : Equiv.Perm X) (hB : Function.Involutive B) :
    Function.Involutive (sigma * B * sigma.symm) := by
  intro x
  simp only [Equiv.Perm.mul_apply]
  rw [sigma.symm_apply_apply, hB, sigma.apply_symm_apply]

theorem fkIsingSquareWiredBondMate_involutive (n : Nat) (hn : 0 < n) :
    Function.Involutive (fkIsingSquareWiredBondMate n hn) := by
  exact perm_conjugate_involutive
    (fkIsingSquareWiredShiftDartEquiv n hn)
    (fkIsingSquareBondMateEquiv n hn)
    (fkIsingSquareBondMate_involutive n hn)

theorem fkIsingSquareWiredBondMate_ne (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredBondMate n hn d ≠ d := by
  intro h
  let sigma := fkIsingSquareWiredShiftDartEquiv n hn
  let B := fkIsingSquareBondMateEquiv n hn
  have h' := congrArg sigma.symm h
  simp only [fkIsingSquareWiredBondMate, fkIsingSquareWiredBondMateEquiv,
    Equiv.Perm.mul_apply] at h'
  have : B (sigma.symm d) = sigma.symm d := by simpa [sigma, B] using h'
  exact fkIsingSquareBondMate_ne n hn (sigma.symm d) this

theorem fkIsingSquareBondMate_wired_bottom (n : Nat) (hn : 0 < n) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn .bottom) =
      fkIsingSquareWiredBoundaryDart n hn
        (.west ⟨0, by omega⟩) := by
  simp only [fkIsingSquareWiredBoundaryDart, fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint, fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  simp [fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
    fkIsingSquareMarkedA, fkIsingSquareLeftVerticalLower,
    fkIsingSquareDirectionDart]

theorem fkIsingSquareBondMate_wired_west_zero (n : Nat) (hn : 0 < n) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.west ⟨0, by omega⟩)) =
      fkIsingSquareWiredBoundaryDart n hn .bottom := by
  rw [← fkIsingSquareBondMate_wired_bottom n hn]
  exact fkIsingSquareBondMate_involutive n hn _

theorem fkIsingSquareBondMate_wired_west_succ (n : Nat) (hn : 0 < n)
    (k : Fin (2 * n)) (hk : k.val ≠ 0) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.west k)) =
      fkIsingSquareWiredBoundaryDart n hn
        (.north ⟨k.val - 1, by omega⟩) := by
  have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
  have hsouth : -(n : Int) < -(n : Int) + (k.val : Int) := by
    have hkpos' : (0 : Int) < (k.val : Int) := by exact_mod_cast hkpos
    omega
  have hu : fkIsingSquareLeftVerticalLower n hn k =
      fkIsingSquareLeftVerticalUpper n hn ⟨k.val - 1, by omega⟩ := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [fkIsingSquareLeftVerticalLower,
        fkIsingSquareLeftVerticalUpper]
    · simp only [fkIsingSquareLeftVerticalLower,
        fkIsingSquareLeftVerticalUpper]
      rw [Nat.cast_sub (by omega : 1 ≤ k.val)]
      push_cast
      ring
  have hw : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareLeftVerticalLower n hn k) .west := by
    simp [fkIsingSquareDirectionAvailable, fkIsingSquareLeftVerticalLower]
  have hs : fkIsingSquareDirectionAvailable n
      (fkIsingSquareLeftVerticalLower n hn k) .south := by
    simpa [fkIsingSquareDirectionAvailable,
      fkIsingSquareLeftVerticalLower] using hsouth
  simp only [fkIsingSquareWiredBoundaryDart, fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint, fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  simp only [fkIsingSquareNextDirection, hw, hs, ↓reduceIte]
  exact fkIsingSquareDirectionDart_endpoint_congr n hu .south _ _ _

theorem fkIsingSquareBondMate_wired_north_not_last
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n))
    (hk : k.val + 1 < 2 * n) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
      fkIsingSquareWiredBoundaryDart n hn
        (.west ⟨k.val + 1, hk⟩) := by
  have hnorth : -(n : Int) + (k.val : Int) + 1 < (n : Int) := by
    have hk' : (k.val : Int) + 1 < 2 * (n : Int) := by exact_mod_cast hk
    omega
  have hu : fkIsingSquareLeftVerticalUpper n hn k =
      fkIsingSquareLeftVerticalLower n hn ⟨k.val + 1, hk⟩ := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [fkIsingSquareLeftVerticalLower,
        fkIsingSquareLeftVerticalUpper] <;> ring
  have hw : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareLeftVerticalUpper n hn k) .west := by
    simp [fkIsingSquareDirectionAvailable, fkIsingSquareLeftVerticalUpper]
  have hnorth' : fkIsingSquareDirectionAvailable n
      (fkIsingSquareLeftVerticalUpper n hn k) .north := by
    simpa [fkIsingSquareDirectionAvailable,
      fkIsingSquareLeftVerticalUpper] using hnorth
  simp only [fkIsingSquareWiredBoundaryDart, fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint, fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  simp only [fkIsingSquarePreviousDirection, hw, hnorth', ↓reduceIte]
  exact fkIsingSquareDirectionDart_endpoint_congr n hu .north _ _ _

theorem fkIsingSquareBondMate_wired_north_last
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n))
    (hk : ¬k.val + 1 < 2 * n) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
      fkIsingSquareWiredBoundaryDart n hn .top := by
  have hlast : k.val = 2 * n - 1 := by omega
  have htop : -(n : Int) + (k.val : Int) + 1 = (n : Int) := by
    rw [hlast, Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  simp only [fkIsingSquareWiredBoundaryDart, fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint, fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  simp [fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
    fkIsingSquareLeftVerticalUpper, fkIsingSquareMarkedB,
    fkIsingSquareDirectionDart, htop]

theorem fkIsingSquareBondMate_wired_top (n : Nat) (hn : 0 < n) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn .top) =
      fkIsingSquareWiredBoundaryDart n hn
        (.north ⟨2 * n - 1, by omega⟩) := by
  let k : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hk : ¬k.val + 1 < 2 * n := by simp [k]; omega
  rw [← fkIsingSquareBondMate_wired_north_last n hn k hk]
  exact fkIsingSquareBondMate_involutive n hn _

@[simp] theorem fkIsingSquareWiredShiftDartEquiv_apply_boundary
    (n : Nat) (hn : 0 < n) (i : FKIsingSquareWiredBoundaryDartIndex n) :
    fkIsingSquareWiredShiftDartEquiv n hn
        (fkIsingSquareWiredBoundaryDart n hn i) =
      fkIsingSquareWiredBoundaryDart n hn
        (fkIsingSquareWiredShift n hn i) := by
  exact Equiv.Perm.viaFintypeEmbedding_apply_image
    (fkIsingSquareWiredShiftEquiv n hn)
    (fkIsingSquareWiredBoundaryEmbedding n hn) i

@[simp] theorem fkIsingSquareWiredShiftDartEquiv_symm_apply_boundary
    (n : Nat) (hn : 0 < n) (i : FKIsingSquareWiredBoundaryDartIndex n) :
    (fkIsingSquareWiredShiftDartEquiv n hn).symm
        (fkIsingSquareWiredBoundaryDart n hn i) =
      fkIsingSquareWiredBoundaryDart n hn
        (fkIsingSquareWiredShiftInv n hn i) := by
  apply (fkIsingSquareWiredShiftDartEquiv n hn).injective
  rw [(fkIsingSquareWiredShiftDartEquiv n hn).apply_symm_apply]
  rw [fkIsingSquareWiredShiftDartEquiv_apply_boundary]
  rw [fkIsingSquareWiredShift_right_inv]

@[simp] theorem fkIsingSquareWiredBondMate_bottom (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn .bottom) =
      fkIsingSquareWiredBoundaryDart n hn .top := by
  simp only [fkIsingSquareWiredBondMate, fkIsingSquareWiredBondMateEquiv,
    Equiv.Perm.mul_apply,
    fkIsingSquareWiredShiftDartEquiv_symm_apply_boundary,
    fkIsingSquareWiredShiftInv]
  change fkIsingSquareWiredShiftDartEquiv n hn
      (fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn .bottom)) = _
  rw [fkIsingSquareBondMate_wired_bottom]
  rw [fkIsingSquareWiredShiftDartEquiv_apply_boundary]
  simp [fkIsingSquareWiredShift]

@[simp] theorem fkIsingSquareWiredBondMate_top (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn .top) =
      fkIsingSquareWiredBoundaryDart n hn .bottom := by
  rw [← fkIsingSquareWiredBondMate_bottom n hn]
  exact fkIsingSquareWiredBondMate_involutive n hn _

@[simp] theorem fkIsingSquareWiredBondMate_west (n : Nat) (hn : 0 < n)
    (k : Fin (2 * n)) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.west k)) =
      fkIsingSquareWiredBoundaryDart n hn (.north k) := by
  simp only [fkIsingSquareWiredBondMate, fkIsingSquareWiredBondMateEquiv,
    Equiv.Perm.mul_apply,
    fkIsingSquareWiredShiftDartEquiv_symm_apply_boundary,
    fkIsingSquareWiredShiftInv]
  change fkIsingSquareWiredShiftDartEquiv n hn
      (fkIsingSquareBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.north k))) = _
  by_cases hk : k.val + 1 < 2 * n
  · rw [fkIsingSquareBondMate_wired_north_not_last n hn k hk]
    rw [fkIsingSquareWiredShiftDartEquiv_apply_boundary]
    simp [fkIsingSquareWiredShift]
  · rw [fkIsingSquareBondMate_wired_north_last n hn k hk]
    rw [fkIsingSquareWiredShiftDartEquiv_apply_boundary]
    simp only [fkIsingSquareWiredShift]
    have hlast : k.val = 2 * n - 1 := by omega
    congr 2
    apply Fin.ext
    exact hlast.symm

@[simp] theorem fkIsingSquareWiredBondMate_north (n : Nat) (hn : 0 < n)
    (k : Fin (2 * n)) :
    fkIsingSquareWiredBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
      fkIsingSquareWiredBoundaryDart n hn (.west k) := by
  rw [← fkIsingSquareWiredBondMate_west n hn k]
  exact fkIsingSquareWiredBondMate_involutive n hn _




inductive FKIsingSquareWiredCarrier (n : Nat)
  | dart : FKIsingMedialDart (fkSquareBoxPlanar n) →
      FKIsingSquareWiredCarrier n
  | bond : FKIsingMedialDart (fkSquareBoxPlanar n) →
      FKIsingSquareWiredCarrier n
  | source : FKIsingSquareWiredCarrier n
  | terminal : FKIsingSquareWiredCarrier n
deriving DecidableEq, Fintype

def fkIsingSquareWiredSourceDart (n : Nat) (hn : 0 < n) :=
  fkIsingSquareWiredBoundaryDart n hn .bottom

def fkIsingSquareWiredTerminalDart (n : Nat) (hn : 0 < n) :=
  fkIsingSquareWiredBoundaryDart n hn .top



def fkIsingSquareWiredIncidenceMate (n : Nat) :
    FKIsingSquareWiredCarrier n → FKIsingSquareWiredCarrier n
  | .dart d => .bond d
  | .bond d => .dart d
  | .source => .source
  | .terminal => .terminal

@[simp] theorem fkIsingSquareWiredIncidenceMate_involutive (n : Nat) :
    Function.Involutive (fkIsingSquareWiredIncidenceMate n) := by
  intro x
  cases x <;> rfl



def fkIsingSquareWiredTransitionMate (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    FKIsingSquareWiredCarrier n → FKIsingSquareWiredCarrier n
  | .source => .bond (fkIsingSquareWiredSourceDart n hn)
  | .terminal => .bond (fkIsingSquareWiredTerminalDart n hn)
  | .dart d => .dart (FKIsingMedialDart.localMate omega d)
  | .bond d =>
      if d = fkIsingSquareWiredSourceDart n hn then .source
      else if d = fkIsingSquareWiredTerminalDart n hn then .terminal
      else .bond (fkIsingSquareWiredBondMate n hn d)

theorem fkIsingSquareWiredSourceDart_ne_terminalDart
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredSourceDart n hn ≠
      fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
  cases hi

theorem fkIsingSquareWiredTransitionMate_involutive
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Function.Involutive (fkIsingSquareWiredTransitionMate n hn omega) := by
  let a := fkIsingSquareWiredSourceDart n hn
  let b := fkIsingSquareWiredTerminalDart n hn
  let B := fkIsingSquareWiredBondMate n hn
  have hab : a ≠ b := fkIsingSquareWiredSourceDart_ne_terminalDart n hn
  have hBa : B a = b := by
    simpa [a, b, B, fkIsingSquareWiredSourceDart,
      fkIsingSquareWiredTerminalDart] using
      fkIsingSquareWiredBondMate_bottom n hn
  have hBb : B b = a := by
    simpa [a, b, B, fkIsingSquareWiredSourceDart,
      fkIsingSquareWiredTerminalDart] using
      fkIsingSquareWiredBondMate_top n hn
  have hInv : Function.Involutive B := by
    simpa [B] using fkIsingSquareWiredBondMate_involutive n hn
  intro x
  cases x with
  | source => simp [fkIsingSquareWiredTransitionMate, a, b, hab]
  | terminal => simp [fkIsingSquareWiredTransitionMate, a, b, hab.symm]
  | dart d =>
      change FKIsingSquareWiredCarrier.dart
        (FKIsingMedialDart.localMate omega
          (FKIsingMedialDart.localMate omega d)) = .dart d
      rw [FKIsingMedialDart.localMate_involutive]
  | bond d =>
      by_cases ha : d = a
      · subst d
        simp [fkIsingSquareWiredTransitionMate, a]
      by_cases hb : d = b
      · subst d
        simp [fkIsingSquareWiredTransitionMate, a, b, hab.symm]
      · have hBdA : B d ≠ a := by
          intro h
          have hh := congrArg B h
          rw [hInv d, hBa] at hh
          exact hb hh
        have hBdB : B d ≠ b := by
          intro h
          have hh := congrArg B h
          rw [hInv d, hBb] at hh
          exact ha hh
        have hfirst : fkIsingSquareWiredTransitionMate n hn omega (.bond d) =
            .bond (B d) := by
          simp [fkIsingSquareWiredTransitionMate, a, b, B, ha, hb]
        have hsecond : fkIsingSquareWiredTransitionMate n hn omega (.bond (B d)) =
            .bond (B (B d)) := by
          simp [fkIsingSquareWiredTransitionMate, a, b, B, hBdA, hBdB]
        rw [hfirst, hsecond, hInv d]

theorem fkIsingSquareWiredTransitionMate_ne
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredTransitionMate n hn omega x ≠ x := by
  cases x with
  | source => simp [fkIsingSquareWiredTransitionMate]
  | terminal => simp [fkIsingSquareWiredTransitionMate]
  | dart d =>
      simp [fkIsingSquareWiredTransitionMate,
        FKIsingMedialDart.localMate_ne omega d]
  | bond d =>
      by_cases ha : d = fkIsingSquareWiredSourceDart n hn
      · simp [fkIsingSquareWiredTransitionMate, ha]
      by_cases hb : d = fkIsingSquareWiredTerminalDart n hn
      · subst d
        simp [fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredSourceDart_ne_terminalDart n hn |>.symm]
      · simp [fkIsingSquareWiredTransitionMate, ha, hb,
          fkIsingSquareWiredBondMate_ne n hn d]



def fkIsingSquareWiredLoopGraph (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    SimpleGraph (FKIsingSquareWiredCarrier n) where
  Adj x y :=
    (x ≠ .source ∧ x ≠ .terminal ∧
      y = fkIsingSquareWiredIncidenceMate n x) ∨
    y = fkIsingSquareWiredTransitionMate n hn omega x
  symm := by
    intro x y h
    rcases h with ⟨hxs, hxt, rfl⟩ | rfl
    · left
      cases x <;> simp_all [fkIsingSquareWiredIncidenceMate]
    · right
      exact (fkIsingSquareWiredTransitionMate_involutive n hn omega x).symm
  loopless := ⟨by
    intro x h
    rcases h with ⟨hxs, hxt, h⟩ | h
    · cases x with
      | source => exact hxs rfl
      | terminal => exact hxt rfl
      | dart d => simp [fkIsingSquareWiredIncidenceMate] at h
      | bond d => simp [fkIsingSquareWiredIncidenceMate] at h
    · exact fkIsingSquareWiredTransitionMate_ne n hn omega x h.symm⟩

noncomputable instance fkIsingSquareWiredLoopGraphDecidableAdj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    DecidableRel (fkIsingSquareWiredLoopGraph n hn omega).Adj :=
  Classical.decRel _

theorem fkIsingSquareWiredIncidenceMate_ne_transitionMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n)
    (hsource : x ≠ .source) (hterminal : x ≠ .terminal) :
    fkIsingSquareWiredIncidenceMate n x ≠
      fkIsingSquareWiredTransitionMate n hn omega x := by
  cases x with
  | source => exact False.elim (hsource rfl)
  | terminal => exact False.elim (hterminal rfl)
  | dart d => simp [fkIsingSquareWiredIncidenceMate,
      fkIsingSquareWiredTransitionMate]
  | bond d =>
      simp only [fkIsingSquareWiredIncidenceMate,
        fkIsingSquareWiredTransitionMate]
      split_ifs <;> simp

@[simp] theorem fkIsingSquareWiredLoopGraph_adj_source_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredLoopGraph n hn omega).Adj .source z ↔
      z = .bond (fkIsingSquareWiredSourceDart n hn) := by
  simp [fkIsingSquareWiredLoopGraph, fkIsingSquareWiredTransitionMate]

@[simp] theorem fkIsingSquareWiredLoopGraph_adj_terminal_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredLoopGraph n hn omega).Adj .terminal z ↔
      z = .bond (fkIsingSquareWiredTerminalDart n hn) := by
  simp [fkIsingSquareWiredLoopGraph, fkIsingSquareWiredTransitionMate]

theorem fkIsingSquareWiredLoopGraph_source_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredLoopGraph n hn omega).degree .source = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareWiredLoopGraph n hn omega).neighborFinset .source =
        {.bond (fkIsingSquareWiredSourceDart n hn)} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp
  rw [hfin]
  simp

theorem fkIsingSquareWiredLoopGraph_terminal_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredLoopGraph n hn omega).degree .terminal = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareWiredLoopGraph n hn omega).neighborFinset .terminal =
        {.bond (fkIsingSquareWiredTerminalDart n hn)} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp
  rw [hfin]
  simp

theorem fkIsingSquareWiredLoopGraph_internal_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n)
    (hsource : x ≠ .source) (hterminal : x ≠ .terminal) :
    (fkIsingSquareWiredLoopGraph n hn omega).degree x = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin : (fkIsingSquareWiredLoopGraph n hn omega).neighborFinset x =
      {fkIsingSquareWiredIncidenceMate n x,
        fkIsingSquareWiredTransitionMate n hn omega x} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    change ((x ≠ .source ∧ x ≠ .terminal ∧
        z = fkIsingSquareWiredIncidenceMate n x) ∨
      z = fkIsingSquareWiredTransitionMate n hn omega x) ↔ _
    simp [hsource, hterminal, eq_comm]
  rw [hfin]
  exact Finset.card_pair
    (fkIsingSquareWiredIncidenceMate_ne_transitionMate
      n hn omega x hsource hterminal)



theorem fkIsingSquareWiredLoopGraph_source_reachable_terminal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source .terminal := by
  apply jeb_two_odd_reachable_fin (fkIsingSquareWiredLoopGraph n hn omega)
  · rw [fkIsingSquareWiredLoopGraph_source_degree]
    exact odd_one
  · rw [fkIsingSquareWiredLoopGraph_terminal_degree]
    exact odd_one
  · intro z hsource hterminal
    rw [fkIsingSquareWiredLoopGraph_internal_degree n hn omega z
      hsource hterminal]
    exact even_two


noncomputable def fkIsingSquareWiredExplorationPath
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredLoopGraph n hn omega).Path .source .terminal :=
  (fkIsingSquareWiredLoopGraph_source_reachable_terminal n hn omega).some.toPath

def fkIsingSquareWiredExplorationOrder
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    List (FKIsingSquareWiredCarrier n) :=
  (fkIsingSquareWiredExplorationPath n hn omega :
    (fkIsingSquareWiredLoopGraph n hn omega).Walk .source .terminal).support

theorem fkIsingSquareWiredExplorationOrder_nodup
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredExplorationOrder n hn omega).Nodup :=
  (fkIsingSquareWiredExplorationPath n hn omega).isPath.support_nodup


def fkIsingSquareWiredExplorationFinset
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Finset (FKIsingSquareWiredCarrier n) :=
  Finset.univ.filter fun z =>
    (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z

def fkIsingSquareWiredExplorationTrace
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    List (FKIsingSquareWiredCarrier n) :=
  (fkIsingSquareWiredExplorationFinset n hn omega).toList

theorem mem_fkIsingSquareWiredExplorationTrace_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    z ∈ fkIsingSquareWiredExplorationTrace n hn omega ↔
      (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z := by
  simp [fkIsingSquareWiredExplorationTrace,
    fkIsingSquareWiredExplorationFinset]

theorem fkIsingSquareWired_localMate_mem_trace_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (.dart (FKIsingMedialDart.localMate omega d) :
        FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn omega ↔
      (.dart d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn omega := by
  rw [mem_fkIsingSquareWiredExplorationTrace_iff,
    mem_fkIsingSquareWiredExplorationTrace_iff]
  have hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj (.dart d)
      (.dart (FKIsingMedialDart.localMate omega d)) := by
    exact Or.inr rfl
  exact ⟨fun h => h.trans hadj.symm.reachable,
    fun h => h.trans hadj.reachable⟩

theorem fkIsingSquareWired_closed_west_mem_iff_south
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ↔
      (.dart (e, .south) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) := by
  have h := fkIsingSquareWired_localMate_mem_trace_iff n hn
    (setClosed e.1 omega) (e, .west)
  simpa [FKIsingMedialDart.localMate] using h.symm

theorem fkIsingSquareWired_closed_east_mem_iff_north
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ↔
      (.dart (e, .north) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) := by
  have h := fkIsingSquareWired_localMate_mem_trace_iff n hn
    (setClosed e.1 omega) (e, .east)
  simpa [FKIsingMedialDart.localMate] using h.symm

theorem fkIsingSquareWired_open_west_mem_iff_north
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) ↔
      (.dart (e, .north) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
  have h := fkIsingSquareWired_localMate_mem_trace_iff n hn
    (setOpen e.1 omega) (e, .west)
  simpa [FKIsingMedialDart.localMate] using h.symm

theorem fkIsingSquareWired_open_east_mem_iff_south
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) ↔
      (.dart (e, .south) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
  have h := fkIsingSquareWired_localMate_mem_trace_iff n hn
    (setOpen e.1 omega) (e, .east)
  simpa [FKIsingMedialDart.localMate] using h.symm

set_option maxHeartbeats 1000000 in


theorem fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch
        (fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega))
        (.dart (e, .west)) (.dart (e, .south))
        (.dart (e, .east)) (.dart (e, .north)) := by
  have hlocal_of_ne
      (d : FKIsingMedialVertex (fkSquareBoxPlanar n)) (hd : d ≠ e)
      (side : FKIsingMedialSide) :
      FKIsingMedialDart.localMate (setOpen e.1 omega) (d, side) =
        FKIsingMedialDart.localMate (setClosed e.1 omega) (d, side) := by
    have hde : d.1 ≠ e.1 := by
      intro h
      exact hd (Subtype.ext h)
    cases h : omega d.1 <;> cases side <;>
      simp [FKIsingMedialDart.localMate, setOpen, setClosed,
        Function.update_of_ne hde, h]
  ext x y
  cases x with
  | source =>
      cases y <;>
        simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
          SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate]
  | terminal =>
      cases y <;>
        simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
          SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate]
  | bond d =>
      cases y <;>
        simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
          SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredIncidenceMate]
  | dart d =>
      cases y with
      | source =>
          simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
            SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
            SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredIncidenceMate]
      | terminal =>
          simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
            SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
            SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredIncidenceMate]
      | bond f =>
          simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
            SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
            SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredIncidenceMate]
      | dart f =>
          rcases d with ⟨d, ds⟩
          rcases f with ⟨f, fs⟩
          by_cases hd : d = e <;> by_cases hf : f = e
          · subst d
            subst f
            cases ds <;> cases fs <;>
              simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
                SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
                SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
                fkIsingSquareWiredIncidenceMate,
                FKIsingMedialDart.localMate]
          · subst d
            cases ds <;>
              simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
                SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
                SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
                fkIsingSquareWiredIncidenceMate,
                FKIsingMedialDart.localMate, hf]
          · subst f
            have hl := hlocal_of_ne d hd ds
            cases fs <;>
              simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
                SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
                SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
                fkIsingSquareWiredIncidenceMate, hl, hd]
          · have hl := hlocal_of_ne d hd ds
            simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
              SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
              SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
              fkIsingSquareWiredIncidenceMate, hl, hd, hf]

def fkIsingSquareWiredCompletedLoopGraph
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    SimpleGraph (FKIsingSquareWiredCarrier n) :=
  fkIsingSquareWiredLoopGraph n hn omega ⊔
    SimpleGraph.edge .source .terminal

noncomputable instance fkIsingSquareWiredCompletedLoopGraphDecidableAdj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    DecidableRel (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj :=
  Classical.decRel _

theorem fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable .source z ↔
      (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z := by
  rw [fkIsingSquareWiredCompletedLoopGraph, reachable_sup_edge_iff]
  constructor
  · rintro (h | ⟨_, hterminal⟩ | ⟨_, hsource⟩)
    · exact h
    · exact (fkIsingSquareWiredLoopGraph_source_reachable_terminal
        n hn omega).trans hterminal
    · exact hsource
  · exact Or.inl

theorem fkIsingSquareWiredCompletedLoopGraph_source_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).degree .source = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).neighborFinset .source =
        {.bond (fkIsingSquareWiredSourceDart n hn), .terminal} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareWiredCompletedLoopGraph, SimpleGraph.edge_adj]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, by simp⟩
  rw [hfin]
  simp

theorem fkIsingSquareWiredCompletedLoopGraph_terminal_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).degree .terminal = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).neighborFinset .terminal =
        {.bond (fkIsingSquareWiredTerminalDart n hn), .source} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareWiredCompletedLoopGraph, SimpleGraph.edge_adj]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, by simp⟩
  rw [hfin]
  simp

theorem fkIsingSquareWiredCompletedLoopGraph_internal_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n)
    (hsource : x ≠ .source) (hterminal : x ≠ .terminal) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).degree x = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).neighborFinset x =
        (fkIsingSquareWiredLoopGraph n hn omega).neighborFinset x := by
    ext z
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareWiredCompletedLoopGraph, SimpleGraph.edge_adj,
      hsource, hterminal]
  rw [hfin, SimpleGraph.card_neighborFinset_eq_degree,
    fkIsingSquareWiredLoopGraph_internal_degree n hn omega x
      hsource hterminal]

theorem fkIsingSquareWiredCompletedLoopGraph_even_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    Even ((fkIsingSquareWiredCompletedLoopGraph n hn omega).degree x) := by
  by_cases hs : x = .source
  · subst x
    rw [fkIsingSquareWiredCompletedLoopGraph_source_degree]
    exact even_two
  by_cases ht : x = .terminal
  · subst x
    rw [fkIsingSquareWiredCompletedLoopGraph_terminal_degree]
    exact even_two
  · rw [fkIsingSquareWiredCompletedLoopGraph_internal_degree
      n hn omega x hs ht]
    exact even_two

theorem fkIsingSquareWiredCompletedLoopGraph_degree_eq_two
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).degree x = 2 := by
  by_cases hs : x = .source
  · subst x
    exact fkIsingSquareWiredCompletedLoopGraph_source_degree n hn omega
  by_cases ht : x = .terminal
  · subst x
    exact fkIsingSquareWiredCompletedLoopGraph_terminal_degree n hn omega
  · exact fkIsingSquareWiredCompletedLoopGraph_internal_degree
      n hn omega x hs ht

set_option maxHeartbeats 1000000 in
theorem fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredCompletedLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch
        (fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega))
        (.dart (e, .west)) (.dart (e, .south))
        (.dart (e, .east)) (.dart (e, .north)) := by
  rw [fkIsingSquareWiredCompletedLoopGraph,
    fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch]
  ext x y
  cases x <;> cases y <;>
    simp [fkIsingSquareWiredCompletedLoopGraph, medialTwoEdgeSwitch,
      SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
      SimpleGraph.edge_adj]

theorem fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)).Adj
      (.dart (e, .west)) (.dart (e, .south)) := by
  apply Or.inl
  exact Or.inr (by simp [fkIsingSquareWiredTransitionMate,
    FKIsingMedialDart.localMate])

theorem fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)).Adj
      (.dart (e, .east)) (.dart (e, .north)) := by
  apply Or.inl
  exact Or.inr (by simp [fkIsingSquareWiredTransitionMate,
    FKIsingMedialDart.localMate])

theorem fkIsingSquareWired_open_local_mem_of_closed_west_mem_not_east
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega))
    (heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∉
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)) :
    ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
  let G := fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  have hsourceWest : G.Reachable .source W := by
    change (fkIsingSquareWiredCompletedLoopGraph n hn
      (setClosed e.1 omega)).Reachable .source (.dart (e, .west))
    rw [fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareWiredExplorationTrace_iff]
    exact hwest
  have hwestEast : ¬ G.Reachable W E := by
    intro h
    apply heast
    rw [mem_fkIsingSquareWiredExplorationTrace_iff,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    exact hsourceWest.trans h
  have hwestSouth : G.Adj W S :=
    fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj
      n hn omega e
  have heastNorth : G.Adj E N :=
    fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj
      n hn omega e
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_left G
    (fkIsingSquareWiredCompletedLoopGraph_even_degree n hn
      (setClosed e.1 omega))
    hwestSouth heastNorth hwestEast hsourceWest
  rw [← fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    n hn omega e] at hall
  intro side
  rw [mem_fkIsingSquareWiredExplorationTrace_iff,
    ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
  cases side
  · exact hall.1
  · exact hall.2.2.1
  · exact hall.2.1
  · exact hall.2.2.2

theorem fkIsingSquareWired_open_local_mem_of_closed_east_mem_not_west
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega))
    (hwest : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∉
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)) :
    ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
  let G := fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  have hsourceEast : G.Reachable .source E := by
    change (fkIsingSquareWiredCompletedLoopGraph n hn
      (setClosed e.1 omega)).Reachable .source (.dart (e, .east))
    rw [fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareWiredExplorationTrace_iff]
    exact heast
  have hwestEast : ¬ G.Reachable W E := by
    intro h
    apply hwest
    rw [mem_fkIsingSquareWiredExplorationTrace_iff,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    exact hsourceEast.trans h.symm
  have hwestSouth : G.Adj W S :=
    fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj
      n hn omega e
  have heastNorth : G.Adj E N :=
    fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj
      n hn omega e
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_right G
    (fkIsingSquareWiredCompletedLoopGraph_even_degree n hn
      (setClosed e.1 omega))
    hwestSouth heastNorth hwestEast hsourceEast
  rw [← fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    n hn omega e] at hall
  intro side
  rw [mem_fkIsingSquareWiredExplorationTrace_iff,
    ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
  cases side
  · exact hall.1
  · exact hall.2.2.1
  · exact hall.2.1
  · exact hall.2.2.2

theorem fkIsingSquareWired_open_local_not_mem_of_closed_west_east_not_mem
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∉
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega))
    (heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∉
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)) :
    ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
      fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
  let G := fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  have hsourceWest : ¬ G.Reachable .source W := by
    simpa only [G, fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareWiredExplorationTrace_iff] using hwest
  have hsourceEast : ¬ G.Reachable .source E := by
    simpa only [G, fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareWiredExplorationTrace_iff] using heast
  have hwestSouth : G.Adj W S :=
    fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj
      n hn omega e
  have heastNorth : G.Adj E N :=
    fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj
      n hn omega e
  have hiff (z : FKIsingSquareWiredCarrier n) :
      (fkIsingSquareWiredCompletedLoopGraph n hn
          (setOpen e.1 omega)).Reachable .source z ↔
        G.Reachable .source z := by
    rw [fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch]
    exact medialTwoEdgeSwitch_reachable_iff_of_disjoint G
      hwestSouth heastNorth hsourceWest hsourceEast
  intro side hopen
  have hopenReach :
      (fkIsingSquareWiredCompletedLoopGraph n hn
        (setOpen e.1 omega)).Reachable .source (.dart (e, side)) := by
    rw [fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareWiredExplorationTrace_iff]
    exact hopen
  have hclosed : (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) := by
    rw [mem_fkIsingSquareWiredExplorationTrace_iff,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    exact (hiff _).1 hopenReach
  cases side
  · exact hwest hclosed
  · exact heast hclosed
  · exact hwest
      ((fkIsingSquareWired_closed_west_mem_iff_south n hn omega e).2 hclosed)
  · exact heast
      ((fkIsingSquareWired_closed_east_mem_iff_north n hn omega e).2 hclosed)



theorem fkIsingSquareWired_local_switch_component_classification
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    ((.dart (e, .west) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega)) ∨
    ((.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega)) ∨
    ((.dart (e, .west) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega)) ∨
    ((.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)) := by
  classical
  by_cases hwest : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)
  · by_cases heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)
    · exact Or.inr (Or.inr (Or.inr ⟨hwest, heast⟩))
    · exact Or.inr (Or.inl ⟨hwest, heast,
        fkIsingSquareWired_open_local_mem_of_closed_west_mem_not_east
          n hn omega e hwest heast⟩)
  · by_cases heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)
    · exact Or.inr (Or.inr (Or.inl ⟨hwest, heast,
        fkIsingSquareWired_open_local_mem_of_closed_east_mem_not_west
          n hn omega e heast hwest⟩))
    · exact Or.inl ⟨hwest, heast,
        fkIsingSquareWired_open_local_not_mem_of_closed_west_east_not_mem
          n hn omega e hwest heast⟩



theorem fkIsingSquareWiredPath_mem_support_iff_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (p : (fkIsingSquareWiredLoopGraph n hn omega).Walk
      (.source : FKIsingSquareWiredCarrier n) .terminal)
    (hp : p.IsPath) (z : FKIsingSquareWiredCarrier n) :
    z ∈ p.support ↔
      (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z := by
  let H := fkIsingSquareWiredLoopGraph n hn omega
  let G := fkIsingSquareWiredCompletedLoopGraph n hn omega
  have hle : H ≤ G := le_sup_left
  have hts : G.Adj (.terminal : FKIsingSquareWiredCarrier n) .source := by
    exact Or.inr (by simp [SimpleGraph.edge_adj])
  have hst_not_adj :
      ¬ H.Adj (.terminal : FKIsingSquareWiredCarrier n) .source := by
    intro h
    have h' := h.symm
    rw [fkIsingSquareWiredLoopGraph_adj_source_iff] at h'
    simp at h'
  have hedge :
      s((.terminal : FKIsingSquareWiredCarrier n), .source) ∉ p.edges := by
    intro h
    exact hst_not_adj (p.adj_of_mem_edges h)
  let q : G.Walk (.terminal : FKIsingSquareWiredCarrier n) .terminal :=
    (p.mapLe hle).cons hts
  have hq : q.IsCycle := by
    change ((p.mapLe hle).cons hts).IsCycle
    rw [Walk.cons_isCycle_iff]
    exact ⟨hp.mapLe hle,
      by simpa only [Walk.edges_mapLe_eq_edges] using hedge⟩
  have hcycles : G.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
    cases v with
    | source =>
        simpa only [G] using
          fkIsingSquareWiredCompletedLoopGraph_source_degree n hn omega
    | terminal =>
        simpa only [G] using
          fkIsingSquareWiredCompletedLoopGraph_terminal_degree n hn omega
    | dart d =>
        simpa only [G] using
          fkIsingSquareWiredCompletedLoopGraph_internal_degree
            n hn omega (.dart d) (by simp) (by simp)
    | bond d =>
        simpa only [G] using
          fkIsingSquareWiredCompletedLoopGraph_internal_degree
            n hn omega (.bond d) (by simp) (by simp)
  constructor
  · intro hz
    exact (p.takeUntil z hz).reachable
  · intro hz
    have hclosed : ∀ v, v ∈ q.toSubgraph.verts →
        ∀ w, G.Adj v w → q.toSubgraph.Adj v w := by
      intro v hv w hadj
      exact (hq.adj_toSubgraph_iff_of_isCycles hcycles hv w).2 hadj
    obtain ⟨c, hc⟩ :=
      q.toSubgraph_connected.exists_verts_eq_connectedComponentSupp hclosed
    have hsource : (.source : FKIsingSquareWiredCarrier n) ∈ c.supp := by
      rw [← hc, Walk.mem_verts_toSubgraph]
      simp [q]
    have hzG : G.Reachable .source z := by
      rw [fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
      exact hz
    have hzc : z ∈ c.supp := by
      rw [c.mem_supp_iff]
      exact hsource ▸ ConnectedComponent.sound hzG.symm
    rw [← hc, Walk.mem_verts_toSubgraph] at hzc
    simp only [q, Walk.support_cons, List.mem_cons] at hzc
    rcases hzc with rfl | hzc
    · simp
    · simpa only [Walk.support_mapLe_eq_support] using hzc

theorem mem_fkIsingSquareWiredExplorationOrder_iff_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    z ∈ fkIsingSquareWiredExplorationOrder n hn omega ↔
      (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z := by
  simpa only [fkIsingSquareWiredExplorationOrder] using
    fkIsingSquareWiredPath_mem_support_iff_reachable n hn omega
      (fkIsingSquareWiredExplorationPath n hn omega)
      (fkIsingSquareWiredExplorationPath n hn omega).isPath z

theorem mem_fkIsingSquareWiredExplorationOrder_iff_trace
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    z ∈ fkIsingSquareWiredExplorationOrder n hn omega ↔
      z ∈ fkIsingSquareWiredExplorationTrace n hn omega := by
  rw [mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
    mem_fkIsingSquareWiredExplorationTrace_iff]

private def fkIsingSquareWiredWalkCast
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) : H.Walk u v := h ▸ p

@[simp] private theorem fkIsingSquareWiredWalkCast_support
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWiredWalkCast h p).support = p.support := by
  subst H
  rfl

@[simp] private theorem fkIsingSquareWiredWalkCast_isPath
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWiredWalkCast h p).IsPath ↔ p.IsPath := by
  subst H
  rfl

theorem fkIsingSquareWired_sourceTerminalPath_unique
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (p q : (fkIsingSquareWiredLoopGraph n hn omega).Walk
      (.source : FKIsingSquareWiredCarrier n) .terminal)
    (hp : p.IsPath) (hq : q.IsPath) : p = q := by
  let H := fkIsingSquareWiredLoopGraph n hn omega
  let G := fkIsingSquareWiredCompletedLoopGraph n hn omega
  have hle : H ≤ G := le_sup_left
  have hmem (z : FKIsingSquareWiredCarrier n) :
      z ∈ p.support ↔ z ∈ q.support := by
    rw [fkIsingSquareWiredPath_mem_support_iff_reachable n hn omega p hp,
      fkIsingSquareWiredPath_mem_support_iff_reachable n hn omega q hq]
  have hfin : p.support.toFinset = q.support.toFinset := by
    ext z
    simpa only [List.mem_toFinset] using hmem z
  have hsupportLen : p.support.length = q.support.length := by
    rw [← List.toFinset_card_of_nodup hp.support_nodup,
      ← List.toFinset_card_of_nodup hq.support_nodup, hfin]
  have hlen : p.length = q.length := by
    have hpLengthSupport := p.length_support
    have hqLengthSupport := q.length_support
    omega
  have hcycles : G.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
    simpa only [G] using
      fkIsingSquareWiredCompletedLoopGraph_degree_eq_two n hn omega v
  have hget : ∀ i, i ≤ p.length → p.getVert i = q.getVert i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst i
        simp
      by_cases hi1 : i = 1
      · subst i
        have hpLen : 0 < p.length := by
          by_contra hzero
          have hz : p.length = 0 := Nat.eq_zero_of_not_pos hzero
          have heq := Walk.eq_of_length_eq_zero hz
          simp at heq
        have hqLen : 0 < q.length := by simpa [hlen] using hpLen
        have hpAdj := p.adj_getVert_succ hpLen
        have hqAdj := q.adj_getVert_succ hqLen
        simp only [Walk.getVert_zero, zero_add] at hpAdj hqAdj
        rw [fkIsingSquareWiredLoopGraph_adj_source_iff] at hpAdj hqAdj
        exact hpAdj.trans hqAdj.symm
      have hi2 : 2 ≤ i := by omega
      have him1 : i - 1 < i := by omega
      have him2 : i - 2 < i := by omega
      have hprev := ih (i - 2) him2 (by omega)
      have hcurr := ih (i - 1) him1 (by omega)
      have hpPrevAdj : G.Adj (p.getVert (i - 1)) (p.getVert (i - 2)) := by
        have h := p.adj_getVert_succ (show i - 2 < p.length by omega)
        have heq : i - 2 + 1 = i - 1 := by omega
        rw [heq] at h
        exact (hle h).symm
      obtain ⟨z, _hz, huniq⟩ := hcycles.existsUnique_ne_adj hpPrevAdj
      have hpNext : p.getVert (i - 2) ≠ p.getVert i ∧
          G.Adj (p.getVert (i - 1)) (p.getVert i) := by
        constructor
        · intro heq
          have hinj := hp.getVert_injOn (show i - 2 ≤ p.length by omega)
            hi heq
          omega
        · have h := p.adj_getVert_succ (show i - 1 < p.length by omega)
          have heq : i - 1 + 1 = i := by omega
          rw [heq] at h
          exact hle h
      have hqNext : q.getVert (i - 2) ≠ q.getVert i ∧
          G.Adj (q.getVert (i - 1)) (q.getVert i) := by
        constructor
        · intro heq
          have hinj := hq.getVert_injOn
            (show i - 2 ≤ q.length by omega)
            (show i ≤ q.length by omega) heq
          omega
        · have h := q.adj_getVert_succ (show i - 1 < q.length by omega)
          have heq : i - 1 + 1 = i := by omega
          rw [heq] at h
          exact hle h
      have hpz : p.getVert i = z := huniq _ hpNext
      have hqz : q.getVert i = z := by
        apply huniq
        simpa only [hprev, hcurr] using hqNext
      exact hpz.trans hqz.symm
  apply Walk.ext_support
  apply List.ext_getElem hsupportLen
  intro i hip hiq
  have hpLengthSupport := p.length_support
  have hqLengthSupport := q.length_support
  have hipLength : i ≤ p.length := by omega
  have hiqLength : i ≤ q.length := by omega
  rw [← p.getVert_eq_support_getElem hipLength,
    ← q.getVert_eq_support_getElem hiqLength]
  exact hget i hipLength

theorem fkIsingSquareWiredExplorationPath_mem_edges_of_adj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hx : x ∈ fkIsingSquareWiredExplorationOrder n hn omega)
    (hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    s(x, y) ∈ (fkIsingSquareWiredExplorationPath n hn omega :
      (fkIsingSquareWiredLoopGraph n hn omega).Walk .source .terminal).edges := by
  let H := fkIsingSquareWiredLoopGraph n hn omega
  let G := fkIsingSquareWiredCompletedLoopGraph n hn omega
  let p : H.Walk (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn omega
  have hle : H ≤ G := le_sup_left
  have hts : G.Adj (.terminal : FKIsingSquareWiredCarrier n) .source :=
    Or.inr (by simp [SimpleGraph.edge_adj])
  have hst_not_adj :
      ¬ H.Adj (.terminal : FKIsingSquareWiredCarrier n) .source := by
    intro h
    have h' := h.symm
    rw [fkIsingSquareWiredLoopGraph_adj_source_iff] at h'
    simp at h'
  have hedge :
      s((.terminal : FKIsingSquareWiredCarrier n), .source) ∉ p.edges := by
    intro h
    exact hst_not_adj (p.adj_of_mem_edges h)
  let q : G.Walk (.terminal : FKIsingSquareWiredCarrier n) .terminal :=
    (p.mapLe hle).cons hts
  have hq : q.IsCycle := by
    change ((p.mapLe hle).cons hts).IsCycle
    rw [Walk.cons_isCycle_iff]
    exact ⟨(fkIsingSquareWiredExplorationPath n hn omega).isPath.mapLe hle,
      by simpa only [Walk.edges_mapLe_eq_edges] using hedge⟩
  have hcycles : G.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
    simpa only [G] using
      fkIsingSquareWiredCompletedLoopGraph_degree_eq_two n hn omega v
  have hxq : x ∈ q.toSubgraph.verts := by
    rw [Walk.mem_verts_toSubgraph]
    simp only [q, Walk.support_cons, List.mem_cons,
      Walk.support_mapLe_eq_support]
    right
    simpa [p, fkIsingSquareWiredExplorationOrder] using hx
  have hqadj : q.toSubgraph.Adj x y :=
    (hq.adj_toSubgraph_iff_of_isCycles hcycles hxq y).2 (hle hadj)
  rw [Walk.adj_toSubgraph_iff_mem_edges] at hqadj
  simp only [q, Walk.edges_cons, List.mem_cons,
    Walk.edges_mapLe_eq_edges] at hqadj
  rcases hqadj with hxy | hxy
  · rcases Sym2.eq_iff.mp hxy with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact False.elim (hst_not_adj hadj)
    · rcases h with ⟨rfl, rfl⟩
      exact False.elim (hst_not_adj hadj.symm)
  · exact hxy

def fkIsingSquareWiredPathUsesLocalSide
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide) : Prop :=
  (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
    fkIsingSquareWiredExplorationOrder n hn omega

theorem fkIsingSquareWired_localMate_infix_explorationOrder
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (h : fkIsingSquareWiredPathUsesLocalSide n hn omega e side) :
    [(.dart (e, side) : FKIsingSquareWiredCarrier n),
        .dart (FKIsingMedialDart.localMate omega (e, side))] <:+:
        fkIsingSquareWiredExplorationOrder n hn omega ∨
      [(.dart (FKIsingMedialDart.localMate omega (e, side)) :
          FKIsingSquareWiredCarrier n), .dart (e, side)] <:+:
        fkIsingSquareWiredExplorationOrder n hn omega := by
  have hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj
      (.dart (e, side))
      (.dart (FKIsingMedialDart.localMate omega (e, side))) := Or.inr rfl
  apply Walk.infix_support_iff_mem_edges.mpr
  apply fkIsingSquareWiredExplorationPath_mem_edges_of_adj n hn omega h hadj

@[simp] theorem fkIsingSquareWiredExplorationOrder_source_mem
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (.source : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn omega := by
  simp [fkIsingSquareWiredExplorationOrder,
    fkIsingSquareWiredExplorationPath]

@[simp] theorem fkIsingSquareWiredExplorationOrder_terminal_mem
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (.terminal : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn omega := by
  simp [fkIsingSquareWiredExplorationOrder,
    fkIsingSquareWiredExplorationPath]



def fkIsingSquareWiredCarrierTangentCode (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredCarrier n → Int
  | .dart d | .bond d => fkIsingSquareCornerTangentCode
      (fkIsingSquareDartDirection n d) (fkIsingSquareSideCorner d.2).2
  | .source => fkIsingSquareCornerTangentCode
      (fkIsingSquareDartDirection n (fkIsingSquareWiredSourceDart n hn))
      (fkIsingSquareSideCorner (fkIsingSquareWiredSourceDart n hn).2).2 + 4
  | .terminal => fkIsingSquareCornerTangentCode
      (fkIsingSquareDartDirection n (fkIsingSquareWiredTerminalDart n hn))
      (fkIsingSquareSideCorner (fkIsingSquareWiredTerminalDart n hn).2).2




def fkIsingSquareOrientedPrincipalBondTurn (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n)) : Int :=
  let raw := fkIsingSquareSignedEighthTurn
    (fkIsingSquareWiredCarrierTangentCode n hn (.bond d))
    (fkIsingSquareWiredCarrierTangentCode n hn (.bond f) + 4)
  if raw = -4 ∧ (fkIsingSquareSideCorner d.2).2 = .counterclockwise
    then 4 else raw

def fkIsingSquareWiredBoundaryForward (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n)) : Prop :=
  (d = fkIsingSquareWiredSourceDart n hn ∧
      f = fkIsingSquareWiredTerminalDart n hn) ∨
    ∃ k : Fin (2 * n),
      d = fkIsingSquareWiredBoundaryDart n hn (.west k) ∧
      f = fkIsingSquareWiredBoundaryDart n hn (.north k)

def fkIsingSquareWiredBoundaryReverse (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n)) : Prop :=
  fkIsingSquareWiredBoundaryForward n hn f d

noncomputable instance fkIsingSquareWiredBoundaryForwardDecidable
    (n : Nat) (hn : 0 < n) :
    DecidableRel (fkIsingSquareWiredBoundaryForward n hn) :=
  Classical.decRel _

noncomputable instance fkIsingSquareWiredBoundaryReverseDecidable
    (n : Nat) (hn : 0 < n) :
    DecidableRel (fkIsingSquareWiredBoundaryReverse n hn) :=
  Classical.decRel _




def fkIsingSquareWiredBondTurn (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n)) : Int :=
  if fkIsingSquareWiredBoundaryForward n hn d f then -6
  else if fkIsingSquareWiredBoundaryReverse n hn d f then 6
  else fkIsingSquareOrientedPrincipalBondTurn n hn d f


def fkIsingSquareWiredTransitionTurn (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredCarrier n) : Int :=
  match x, y with
  | .dart d, .dart f =>
      if f = FKIsingMedialDart.localMate omega d then
        fkIsingSquareSignedEighthTurn
          (fkIsingSquareWiredCarrierTangentCode n hn (.dart d) + 4)
          (fkIsingSquareWiredCarrierTangentCode n hn (.dart f))
      else 0
  | .bond d, .bond f => fkIsingSquareWiredBondTurn n hn d f
  | _, _ => 0

@[simp] theorem fkIsingSquareWiredTransitionTurn_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredTransitionTurn n hn omega (.dart d)
        (.dart (FKIsingMedialDart.localMate omega d)) =
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareWiredCarrierTangentCode n hn (.dart d) + 4)
        (fkIsingSquareWiredCarrierTangentCode n hn
          (.dart (FKIsingMedialDart.localMate omega d))) := by
  simp [fkIsingSquareWiredTransitionTurn]


theorem fkIsingSquareWiredTransitionTurn_local_table
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .west)) (.dart (e, .south)) = -2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .south)) (.dart (e, .west)) = 2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .east)) (.dart (e, .north)) = -2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .north)) (.dart (e, .east)) = 2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .west)) (.dart (e, .north)) = 2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .north)) (.dart (e, .west)) = -2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .east)) (.dart (e, .south)) = 2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .south)) (.dart (e, .east)) = -2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    cases ha : (fkIsingSquareOrientedEdge n e).axis <;>
    simp [fkIsingSquareWiredTransitionTurn,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, FKIsingMedialDart.localMate,
      setOpen, setClosed, fkIsingSquareSignedEighthTurn,
      FKIsingSquareDirection.eighthTurn, ha]

def fkIsingSquareWiredExplorationTurnSteps
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) : List Int :=
  let path := fkIsingSquareWiredExplorationOrder n hn omega
  List.zipWith (fkIsingSquareWiredTransitionTurn n hn omega)
    path path.tail

def fkIsingSquareWiredRawTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) : Int :=
  let path := fkIsingSquareWiredExplorationOrder n hn omega
  if z ∈ path then
    ((fkIsingSquareWiredExplorationTurnSteps n hn omega).take
      (path.idxOf z)).sum
  else 0

theorem fkIsingSquareWiredRawTurnCount_succ
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (i : Nat)
    (hi : i + 1 < (fkIsingSquareWiredExplorationOrder n hn omega).length) :
    fkIsingSquareWiredRawTurnCount n hn omega
        (fkIsingSquareWiredExplorationOrder n hn omega)[i + 1] =
      fkIsingSquareWiredRawTurnCount n hn omega
        (fkIsingSquareWiredExplorationOrder n hn omega)[i] +
      fkIsingSquareWiredTransitionTurn n hn omega
        (fkIsingSquareWiredExplorationOrder n hn omega)[i]
        (fkIsingSquareWiredExplorationOrder n hn omega)[i + 1] := by
  let p := fkIsingSquareWiredExplorationOrder n hn omega
  let t := fkIsingSquareWiredExplorationTurnSteps n hn omega
  have hi' : i + 1 < p.length := by simpa [p] using hi
  have hi0 : i < p.length := by omega
  have hmem0 : p[i] ∈ p := List.getElem_mem _
  have hmem1 : p[i + 1] ∈ p := List.getElem_mem _
  have hnodup : p.Nodup := by
    simpa [p] using fkIsingSquareWiredExplorationOrder_nodup n hn omega
  have hidx0 : p.idxOf p[i] = i := List.get_idxOf hnodup ⟨i, hi0⟩
  have hidx1 : p.idxOf p[i + 1] = i + 1 :=
    List.get_idxOf hnodup ⟨i + 1, hi'⟩
  have htlen : i < t.length := by
    simp [t, fkIsingSquareWiredExplorationTurnSteps]
    omega
  have htget :
      t[i] = fkIsingSquareWiredTransitionTurn n hn omega p[i] p[i + 1] := by
    simp [t, fkIsingSquareWiredExplorationTurnSteps, p]
  change (if p[i + 1] ∈ p then
      (t.take (p.idxOf p[i + 1])).sum else 0) = _
  rw [if_pos hmem1]
  change _ = (if p[i] ∈ p then
      (t.take (p.idxOf p[i])).sum else 0) + _
  rw [if_pos hmem0, hidx0, hidx1,
    List.sum_take_succ t i htlen, htget]

theorem fkIsingSquareWiredRawTurnCount_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (h : fkIsingSquareWiredPathUsesLocalSide n hn omega e side) :
    (fkIsingSquareWiredRawTurnCount n hn omega
        (.dart (FKIsingMedialDart.localMate omega (e, side))) =
      fkIsingSquareWiredRawTurnCount n hn omega (.dart (e, side)) +
        fkIsingSquareWiredTransitionTurn n hn omega
          (.dart (e, side))
          (.dart (FKIsingMedialDart.localMate omega (e, side)))) ∨
    (fkIsingSquareWiredRawTurnCount n hn omega (.dart (e, side)) =
      fkIsingSquareWiredRawTurnCount n hn omega
        (.dart (FKIsingMedialDart.localMate omega (e, side))) +
        fkIsingSquareWiredTransitionTurn n hn omega
          (.dart (FKIsingMedialDart.localMate omega (e, side)))
          (.dart (e, side))) := by
  let p := fkIsingSquareWiredExplorationOrder n hn omega
  let x : FKIsingSquareWiredCarrier n := .dart (e, side)
  let y : FKIsingSquareWiredCarrier n :=
    .dart (FKIsingMedialDart.localMate omega (e, side))
  have hxy := fkIsingSquareWired_localMate_infix_explorationOrder
    n hn omega e side h
  have hx : x ∈ p := by simpa [x, p] using h
  have hy : y ∈ p := hxy.elim
    (fun hf => hf.mem (by simp [y]))
    (fun hb => hb.mem (by simp [y]))
  have hix : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : p.idxOf y < p.length := List.idxOf_lt_length_iff.mpr hy
  rcases hxy with hf | hb
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hf
    have hs := fkIsingSquareWiredRawTurnCount_succ n hn omega (p.idxOf x)
      (by rw [← hi]; exact hiy)
    left
    simpa only [p, x, y, List.getElem_idxOf hix,
      ← hi, List.getElem_idxOf hiy] using hs
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hb
    have hs := fkIsingSquareWiredRawTurnCount_succ n hn omega (p.idxOf y)
      (by rw [← hi]; exact hix)
    right
    simpa only [p, x, y, List.getElem_idxOf hiy,
      ← hi, List.getElem_idxOf hix] using hs

theorem fkIsingSquareWired_closed_west_south_rawTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    fkIsingSquareWiredRawTurnCount n hn (setClosed e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareWiredRawTurnCount n hn (setClosed e.1 omega)
        (.dart (e, .west)) - 2 := by
  have hm := fkIsingSquareWiredRawTurnCount_localMate
    n hn (setClosed e.1 omega) e .west h
  rcases fkIsingSquareWiredTransitionTurn_local_table n hn omega e with
    ⟨hWS, hSW, _hEN, _hNE, _hWN, _hNW, _hES, _hSE⟩
  simp only [FKIsingMedialDart.localMate, setClosed_self] at hm
  rw [hWS, hSW] at hm
  omega

theorem fkIsingSquareWired_closed_east_north_rawTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    fkIsingSquareWiredRawTurnCount n hn (setClosed e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareWiredRawTurnCount n hn (setClosed e.1 omega)
        (.dart (e, .east)) - 2 := by
  have hm := fkIsingSquareWiredRawTurnCount_localMate
    n hn (setClosed e.1 omega) e .east h
  rcases fkIsingSquareWiredTransitionTurn_local_table n hn omega e with
    ⟨_hWS, _hSW, hEN, hNE, _hWN, _hNW, _hES, _hSE⟩
  simp only [FKIsingMedialDart.localMate, setClosed_self] at hm
  rw [hEN, hNE] at hm
  omega

theorem fkIsingSquareWired_open_west_north_rawTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    fkIsingSquareWiredRawTurnCount n hn (setOpen e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareWiredRawTurnCount n hn (setOpen e.1 omega)
        (.dart (e, .west)) + 2 := by
  have hm := fkIsingSquareWiredRawTurnCount_localMate
    n hn (setOpen e.1 omega) e .west h
  rcases fkIsingSquareWiredTransitionTurn_local_table n hn omega e with
    ⟨_hWS, _hSW, _hEN, _hNE, hWN, hNW, _hES, _hSE⟩
  simp only [FKIsingMedialDart.localMate, setOpen_self] at hm
  rw [hWN, hNW] at hm
  omega

theorem fkIsingSquareWired_open_east_south_rawTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    fkIsingSquareWiredRawTurnCount n hn (setOpen e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareWiredRawTurnCount n hn (setOpen e.1 omega)
        (.dart (e, .east)) + 2 := by
  have hm := fkIsingSquareWiredRawTurnCount_localMate
    n hn (setOpen e.1 omega) e .east h
  rcases fkIsingSquareWiredTransitionTurn_local_table n hn omega e with
    ⟨_hWS, _hSW, _hEN, _hNE, _hWN, _hNW, hES, hSE⟩
  simp only [FKIsingMedialDart.localMate, setOpen_self] at hm
  rw [hES, hSE] at hm
  omega

def fkIsingSquareWiredPhysicalTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) : Int :=
  fkIsingSquareWiredRawTurnCount n hn omega z -
    fkIsingSquareWiredRawTurnCount n hn omega .terminal

def fkIsingSquareWiredLiftedWinding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) : Real :=
  (fkIsingSquareWiredPhysicalTurnCount n hn omega z : Real) *
    (Real.pi / 4)

theorem fkIsingSquareWired_closed_west_south_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .west)) - Real.pi / 2 := by
  simp only [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount,
    fkIsingSquareWired_closed_west_south_rawTurnCount n hn omega e h]
  push_cast
  ring

theorem fkIsingSquareWired_closed_east_north_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .east)) - Real.pi / 2 := by
  simp only [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount,
    fkIsingSquareWired_closed_east_north_rawTurnCount n hn omega e h]
  push_cast
  ring

theorem fkIsingSquareWired_open_west_north_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .west)) + Real.pi / 2 := by
  simp only [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount,
    fkIsingSquareWired_open_west_north_rawTurnCount n hn omega e h]
  push_cast
  ring

theorem fkIsingSquareWired_open_east_south_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .east)) + Real.pi / 2 := by
  simp only [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount,
    fkIsingSquareWired_open_east_south_rawTurnCount n hn omega e h]
  push_cast
  ring

@[simp] theorem fkIsingSquareWiredLiftedWinding_terminal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    fkIsingSquareWiredLiftedWinding n hn omega .terminal = 0 := by
  simp [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount]

def fkIsingSquareWiredCarrierPosition (n : Nat) (_hn : 0 < n) :
    FKIsingSquareWiredCarrier n → Complex
  | .dart d | .bond d =>
      (fkIsingSquareSitePosition (fkIsingSquareOrientedEdge n d.1).tail.1 +
        fkIsingSquareSitePosition (fkIsingSquareOrientedEdge n d.1).head.1) / 2
  | .source => fkIsingSquareSitePosition (fkIsingSquareMarkedA n).1 - 1 / 2
  | .terminal => fkIsingSquareSitePosition (fkIsingSquareMarkedB n).1 - 1 / 2


def fkIsingSquareWiredDobrushinDomain (n : Nat) (hn : 0 < n) :
    FKIsingDobrushinDomain (fkSquareBoxPlanar n)
      (FKIsingSquareWiredCarrier n) where
  wiredArc := fkIsingSquareWiredArc n
  markedA := fkIsingSquareMarkedA n
  markedB := fkIsingSquareMarkedB n
  markedA_mem := fkIsingSquareMarkedA_mem_wiredArc n
  markedB_mem := fkIsingSquareMarkedB_mem_wiredArc n
  sourceEdge := .source
  terminalEdge := .terminal
  medialPosition := fkIsingSquareWiredCarrierPosition n hn
  exploration := fkIsingSquareWiredExplorationTrace n hn
  source_mem := by
    intro omega
    rw [mem_fkIsingSquareWiredExplorationTrace_iff]
  terminal_mem := by
    intro omega
    rw [mem_fkIsingSquareWiredExplorationTrace_iff]
    exact fkIsingSquareWiredLoopGraph_source_reachable_terminal n hn omega
  winding := fkIsingSquareWiredLiftedWinding n hn
  winding_terminal := fkIsingSquareWiredLiftedWinding_terminal n hn

end
end StatMech.Universality
