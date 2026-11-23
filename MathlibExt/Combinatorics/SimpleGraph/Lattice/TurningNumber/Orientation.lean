/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.InteriorCells
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring.RingNF

/-!
# The cells to the left of a closed walk

For a step in direction `w` starting at `p`, `leftCell w p` is the unit cell on its left. Going
straight or turning left keeps the next left cell on the same side of the walk, so for a simple
closed walk without right turns the ray parity of the left cell, `leftParity d k`, is the same for
all `k`. Its value fixes the orientation: `1` when the walk runs counterclockwise around its
interior.

## Main definitions

* `StatMech.Onsager.Orientation.leftCell`: the cell to the left of a step.
* `StatMech.Onsager.Orientation.leftParity`: the ray parity of the cell to the left of step `k`.

## Main results

* `StatMech.Onsager.Orientation.leftParity_const`: the left parity is constant along the walk.
-/

@[expose] public section

namespace StatMech.Onsager.Orientation

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity
open Fin.NatCast

variable {n : ℕ} [NeZero n]

/-- The unit cell to the left of the step in direction `w` starting at `p` (cells are named by their
  lower-left corners). -/
def leftCell : Fin 4 → ℤ × ℤ → ℤ × ℤ
  | 0, p => p
  | 1, p => (p.1 - 1, p.2)
  | 2, p => (p.1 - 1, p.2 - 1)
  | 3, p => (p.1, p.2 - 1)

/-- At a left turn, the steps before and after the turn have the same left cell. -/
theorem leftCell_eq_of_leftTurn (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n)
    (hturn : d (k + 1) - d k = 1) :
    leftCell (d k) (pos d k) = leftCell (d (k + 1)) (pos d (k + 1)) := by
  have hstep : pos d (k + 1) = pos d k + stepOf (d k) := pos_succ d hclosed k
  have hd1 : d (k + 1) = d k + 1 := by rw [sub_eq_iff_eq_add] at hturn; rw [hturn, add_comm]
  rw [hd1, hstep]
  set p := pos d k with hp
  generalize d k = dk
  fin_cases dk
  · change leftCell 0 p = leftCell 1 (p + stepOf 0)
    simp only [leftCell, stepOf, Prod.fst_add, Prod.snd_add, Prod.ext_iff]; omega
  · change leftCell 1 p = leftCell 2 (p + stepOf 1)
    simp only [leftCell, stepOf, Prod.fst_add, Prod.snd_add, Prod.ext_iff]; omega
  · change leftCell 2 p = leftCell 3 (p + stepOf 2)
    simp only [leftCell, stepOf, Prod.fst_add, Prod.snd_add, Prod.ext_iff]; omega
  · change leftCell 3 p = leftCell 0 (p + stepOf 3)
    simp only [leftCell, stepOf, Prod.fst_add, Prod.snd_add, Prod.ext_iff]; omega

/-- A vertical step through the point `(c, h)` has `(c, h)` as a vertex; if `(c, h)` is not a walk
  vertex, no vertical step straddles height `h` on the line `x = c`. -/
theorem no_vEdge_of_not_vertex (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (c h : ℤ) (hnv : ∀ k : Fin n, pos d k ≠ (c, h)) :
    ∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = c →
      ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ h ∧
          h < max ((pos d k).2) ((pos d (k + 1)).2)) := by
  intro k hvk hx ⟨hmn, hmx⟩
  have hxc := vert_x_const d hclosed k hvk
  rcases vert_y_step d hclosed k hvk with hy | hy
  · exact hnv k (Prod.ext hx (by omega))
  · exact hnv (k + 1) (Prod.ext (by rw [hxc]; exact hx) (by omega))

/-- If `(c, h)` is not a walk vertex, no horizontal step starts at `x = c` on height `h`. -/
theorem no_hEdge_of_not_vertex (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (c h : ℤ) (hnv : ∀ k : Fin n, pos d k ≠ (c, h)) :
    ∀ k : Fin n, isHorizEdge (d k) → min ((pos d k).1) ((pos d (k + 1)).1) = c →
      (pos d k).2 ≠ h := by
  intro k hhk hx hy
  have hyc := horiz_y_const d hclosed k hhk
  rcases horiz_x_step d hclosed k hhk with h1 | h1
  · exact hnv k (Prod.ext (by omega) hy)
  · exact hnv (k + 1) (Prod.ext (by omega) (by rw [hyc]; exact hy))

/-- In a simple walk, a vertical step on the segment above the vertex `pos d m` is step `m` or step
  `m - 1`. -/
theorem vEdge_lower_index (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (c h : ℤ) (m : Fin n) (hpm : pos d m = (c, h))
    (j : Fin n) (hvj : isVertEdge (d j)) (hxj : (pos d j).1 = c)
    (hstraddle : min ((pos d j).2) ((pos d (j + 1)).2) ≤ h ∧
      h < max ((pos d j).2) ((pos d (j + 1)).2)) :
    j = m ∨ j + 1 = m := by
  obtain ⟨hmn, hmx⟩ := hstraddle
  have hxc := vert_x_const d hclosed j hvj
  rcases vert_y_step d hclosed j hvj with hy | hy
  · exact Or.inl (hsimple ((Prod.ext hxj (by omega)).trans hpm.symm))
  · exact Or.inr (hsimple ((Prod.ext (by rw [hxc]; exact hxj) (by omega)).trans hpm.symm))

/-- In a simple walk, a horizontal step on the segment to the right of the vertex `pos d m` is step
  `m` or step `m - 1`. -/
theorem hEdge_left_index (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (c h : ℤ) (m : Fin n) (hpm : pos d m = (c, h))
    (j : Fin n) (hhj : isHorizEdge (d j)) (hxj : min ((pos d j).1) ((pos d (j + 1)).1) = c)
    (hyj : (pos d j).2 = h) :
    j = m ∨ j + 1 = m := by
  have hyc := horiz_y_const d hclosed j hhj
  rcases horiz_x_step d hclosed j hhj with h1 | h1
  · exact Or.inl (hsimple ((Prod.ext (by omega) hyj).trans hpm.symm))
  · exact Or.inr (hsimple ((Prod.ext (by omega) (by rw [hyc]; exact hyj)).trans hpm.symm))

/-- In a simple walk, a vertical step on the segment below the vertex `pos d m` is step `m` or step
  `m - 1`. -/
theorem vEdge_upper_index (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (c h : ℤ) (m : Fin n) (hpm : pos d m = (c, h + 1))
    (j : Fin n) (hvj : isVertEdge (d j)) (hxj : (pos d j).1 = c)
    (hstraddle : min ((pos d j).2) ((pos d (j + 1)).2) ≤ h ∧
      h < max ((pos d j).2) ((pos d (j + 1)).2)) :
    j = m ∨ j + 1 = m := by
  obtain ⟨hmn, hmx⟩ := hstraddle
  have hxc := vert_x_const d hclosed j hvj
  rcases vert_y_step d hclosed j hvj with hy | hy
  · exact Or.inr (hsimple ((Prod.ext (by rw [hxc]; exact hxj) (by omega)).trans hpm.symm))
  · exact Or.inl (hsimple ((Prod.ext hxj (by omega)).trans hpm.symm))

/-- In a simple walk, a horizontal step on the segment to the left of the vertex `pos d m` is step
  `m` or step `m - 1`. -/
theorem hEdge_right_index (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (c h : ℤ) (m : Fin n) (hpm : pos d m = (c + 1, h))
    (j : Fin n) (hhj : isHorizEdge (d j)) (hxj : min ((pos d j).1) ((pos d (j + 1)).1) = c)
    (hyj : (pos d j).2 = h) :
    j = m ∨ j + 1 = m := by
  have hyc := horiz_y_const d hclosed j hhj
  rcases horiz_x_step d hclosed j hhj with h1 | h1
  · exact Or.inr (hsimple ((Prod.ext (by omega) (by rw [hyc]; exact hyj)).trans hpm.symm))
  · exact Or.inl (hsimple ((Prod.ext (by omega) hyj).trans hpm.symm))

/-- Going straight, consecutive left cells have the same ray parity. -/
theorem leftCell_parity_eq_of_straight (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (k : Fin n) (hst : d (k + 1) = d k) :
    rayParity d (leftCell (d k) (pos d k)).1 (leftCell (d k) (pos d k)).2
      = rayParity d (leftCell (d (k + 1)) (pos d (k + 1))).1
          (leftCell (d (k + 1)) (pos d (k + 1))).2 := by
  have hstep : pos d (k + 1) = pos d k + stepOf (d k) := pos_succ d hclosed k
  rw [hst]
  match hdk : d k with
  | 0 =>
    have hp1 : pos d (k + 1) = ((pos d k).1 + 1, (pos d k).2) := by
      rw [hstep, hdk]; ext <;> simp [stepOf]
    simp only [leftCell, hp1]
    apply rayParity_hstep d hclosed (pos d k).1 (pos d k).2
    intro j hvj hxj hstrd
    rcases vEdge_lower_index d hclosed hsimple ((pos d k).1 + 1) (pos d k).2 (k + 1) hp1 j hvj hxj
        ⟨hstrd.1, hstrd.2⟩ with h | h
    · rw [h, hst, hdk] at hvj; exact absurd hvj (by decide)
    · rw [add_right_cancel h, hdk] at hvj; exact absurd hvj (by decide)
  | 1 =>
    have hp1 : pos d (k + 1) = ((pos d k).1, (pos d k).2 + 1) := by
      rw [hstep, hdk]; ext <;> simp [stepOf]
    simp only [leftCell, hp1]
    apply rayParity_vstep d ((pos d k).1 - 1) (pos d k).2
    intro j hhj hxj hyj
    rcases hEdge_right_index d hclosed hsimple ((pos d k).1 - 1) ((pos d k).2 + 1) (k + 1)
        (by rw [hp1]; ext <;> simp) j hhj hxj hyj with h | h
    · rw [h, hst, hdk] at hhj; exact absurd hhj (by decide)
    · rw [add_right_cancel h, hdk] at hhj; exact absurd hhj (by decide)
  | 2 =>
    have hp1 : pos d (k + 1) = ((pos d k).1 - 1, (pos d k).2) := by
      rw [hstep, hdk]; ext <;> simp [stepOf]; omega
    have hstr' : ∀ j : Fin n, isVertEdge (d j) → (pos d j).1 = (((pos d k).1 - 1) - 1) + 1 →
        ¬ (min ((pos d j).2) ((pos d (j + 1)).2) ≤ (pos d k).2 - 1 ∧
           (pos d k).2 - 1 < max ((pos d j).2) ((pos d (j + 1)).2)) := by
      intro j hvj hxj hstrd
      rcases vEdge_upper_index d hclosed hsimple ((pos d k).1 - 1) ((pos d k).2 - 1) (k + 1)
          (by rw [hp1, Prod.mk.injEq]; omega) j hvj (by omega) ⟨hstrd.1, hstrd.2⟩ with h | h
      · rw [h, hst, hdk] at hvj; exact absurd hvj (by decide)
      · rw [add_right_cancel h, hdk] at hvj; exact absurd hvj (by decide)
    simp only [leftCell, hp1]
    have key : rayParity d (((pos d k).1 - 1) - 1) ((pos d k).2 - 1)
             = rayParity d ((pos d k).1 - 1) ((pos d k).2 - 1) := by
      have := rayParity_hstep d hclosed (((pos d k).1 - 1) - 1) ((pos d k).2 - 1) hstr'
      rwa [show (((pos d k).1 - 1) - 1) + 1 = (pos d k).1 - 1 from by ring] at this
    exact key.symm
  | 3 =>
    have hp1 : pos d (k + 1) = ((pos d k).1, (pos d k).2 - 1) := by
      rw [hstep, hdk]; ext <;> simp [stepOf]; omega
    have hstr' : ∀ j : Fin n, isHorizEdge (d j) →
        min ((pos d j).1) ((pos d (j + 1)).1) = (pos d k).1 →
        (pos d j).2 ≠ (((pos d k).2 - 1) - 1) + 1 := by
      intro j hhj hxj hyj
      rcases hEdge_left_index d hclosed hsimple (pos d k).1 ((pos d k).2 - 1) (k + 1)
          (by rw [hp1, Prod.mk.injEq]; omega) j hhj hxj (by omega) with h | h
      · rw [h, hst, hdk] at hhj; exact absurd hhj (by decide)
      · rw [add_right_cancel h, hdk] at hhj; exact absurd hhj (by decide)
    simp only [leftCell, hp1]
    have key : rayParity d (pos d k).1 (((pos d k).2 - 1) - 1)
             = rayParity d (pos d k).1 ((pos d k).2 - 1) := by
      have := rayParity_vstep d (pos d k).1 (((pos d k).2 - 1) - 1) hstr'
      rwa [show (((pos d k).2 - 1) - 1) + 1 = (pos d k).2 - 1 from by ring] at this
    exact key.symm

/-- The ray parity of the cell to the left of step `k`. -/
def leftParity (d : Fin n → Fin 4) (k : Fin n) : ZMod 2 :=
  rayParity d (leftCell (d k) (pos d k)).1 (leftCell (d k) (pos d k)).2

/-- For a simple closed walk without right turns, consecutive steps have the same left parity. -/
theorem leftParity_step (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) (k : Fin n) :
    leftParity d k = leftParity d (k + 1) := by
  rcases hreflexfree k with h0 | h1
  · exact leftCell_parity_eq_of_straight d hclosed hsimple k (by rw [sub_eq_zero] at h0; exact h0)
  · unfold leftParity; rw [leftCell_eq_of_leftTurn d hclosed k h1]

/-- For a simple closed walk without right turns, the left parity is the same for every step. -/
theorem leftParity_const (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) (k : Fin n) :
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
      rw [hcast, ← leftParity_step d hclosed hsimple hreflexfree (Nat.cast j), ih]
  have := haux k.val
  rwa [Fin.cast_val_eq_self] at this

end StatMech.Onsager.Orientation
