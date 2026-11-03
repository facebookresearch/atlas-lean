/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CornerWeights
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.InteriorEulerBound
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.PinchFree

/-!
# The discrete Umlaufsatz for lattice walks without right turns

Let `d : Fin n → Fin 4` be the step directions of a simple closed walk on `ℤ²` in which every turn
is straight or a left (counterclockwise) quarter turn. Then the walk has exactly four left turns:
`cc d = 4`. This is the discrete theorem of turning tangents (Hopf's Umlaufsatz) for such walks:
the tangent direction makes exactly one full counterclockwise revolution. The walks covered are
exactly the boundaries of lattice rectangles traversed counterclockwise; clockwise walks and
non-convex polygons are excluded by the hypothesis.

The proof combines the cell Gauss–Bonnet formula for the bounded face `S` of the walk,
`cornerDiff S = 4 * eulerChar S + 2 * pinchCount S`, with `pinchCount S = 0`,
`cornerDiff S = cc d` (the walk runs counterclockwise around `S`), `eulerChar S ≤ 1` and
`4 ≤ cc d`.

The hypothesis excluding right turns and reversals is essential to this statement. The general
discrete Umlaufsatz, in which right turns are allowed (reversals are still excluded) and the signed
number of quarter turns is `±4`, is `StatMech.Onsager.GeneralUmlaufsatz.turnSum_eq_four_or_neg_four`
in `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LatticeUmlaufsatz`. The smooth
Umlaufsatz is recorded as the wanted theorem `hopf_umlaufsatz` in
`WantedExt.Geometry.HopfUmlaufsatzWanted`; it concerns smooth unit-speed curves and total curvature
`2π`, a different statement.

## Main results

* `StatMech.Onsager.UmlaufsatzFinal.cc_eq_four_of_no_right_turn`: a simple closed lattice walk with
  only straight steps and left turns (a rectangle traversed counterclockwise) has exactly four left
  turns.
* `StatMech.Onsager.UmlaufsatzFinal.interiorCells_bridge`: the ray-parity interior equals the
  bounded face.

## References

* H. Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Math. 2 (1935).
* J. O'Rourke, *Art Gallery Theorems and Algorithms*, Oxford University Press (1987): an
  orthogonal polygon has four more convex than reflex vertices.
-/

@[expose] public section

namespace StatMech.Onsager.UmlaufsatzFinal

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellPinch StatMech.Onsager.InteriorCells StatMech.Onsager.Orientation
  StatMech.Onsager.MasterCorner StatMech.Onsager.PinchFree
  StatMech.Onsager.CellGaussBonnetGlobal

variable {m : ℕ}

/-- The two descriptions of the cell to the left of a step agree. -/
theorem leftCell_bridge (d : Fin (m + 3) → Fin 4) (k : Fin (m + 3)) :
    Orientation.leftCell (d k) (pos d k) = WalkCellBoundary.leftCell d k := by
  rw [WalkCellBoundary.leftCell]
  match hd : d k with
  | 0 => simp [Orientation.leftCell]
  | 1 => simp [Orientation.leftCell]
  | 2 => simp [Orientation.leftCell]
  | 3 => simp [Orientation.leftCell]

/-- The cell to the left of the first step is inside: the walk is positively oriented. -/
theorem leftParity_zero (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    leftParity d 0 = 1 := by
  unfold Orientation.leftParity
  rw [leftCell_bridge d 0]
  exact WalkCellBoundary.leftCell_parity_one d hclosed hsimple hreflexfree 0

/-- The ray-parity interior of a simple closed walk without right turns equals its bounded face. -/
theorem interiorCells_bridge (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    InteriorCells.interiorCells d hclosed
      = WalkCellRegion.interiorCells d hclosed hsimple hreflexfree := by
  ext p
  rw [InteriorCells.mem_interiorCells, WalkCellRegion.mem_interiorCells_iff_rayParity]

/-- The discrete Umlaufsatz for walks of length `m + 3` without right turns. -/
theorem cc_eq_four' (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cc d = 4 := by
  have hn : 3 ≤ m + 3 := by omega
  have hW : leftParity d 0 = 1 := leftParity_zero d hclosed hsimple hreflexfree
  have hle : eulerChar (InteriorCells.interiorCells d hclosed) ≤ 1 := by
    rw [interiorCells_bridge d hclosed hsimple hreflexfree]
    exact CellEulerFaithful.eulerChar_interiorCells_le_one d hclosed hsimple hreflexfree
  have hpinch := PinchFree.pinchCount_eq_zero d hclosed hsimple hn
  have h1 := MasterCorner.cornerDiff_eq_weight_mul_cc d hclosed hsimple hn hreflexfree
  have h2 := cornerDiff_eq (InteriorCells.interiorCells d hclosed)
  rw [hpinch] at h2
  rw [ite_eq_left hW, one_mul] at h1
  have hkey : (cc d : ℤ) = 4 * eulerChar (InteriorCells.interiorCells d hclosed) := by
    rw [← h1, h2]; ring
  have hcc4 : 4 ≤ cc d := four_le_cc d hclosed hreflexfree
  omega

/-- The discrete Umlaufsatz for walks of length at least `3` without right turns. -/
theorem cc_eq_four {n : ℕ} [NeZero n] (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cc d = 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact cc_eq_four' d hclosed hsimple hreflexfree

/-- A closed walk without right turns or reversals has length at least `3`. -/
theorem three_le_n {n : ℕ} [NeZero n] (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) : 3 ≤ n := by
  have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  by_contra hlt
  push Not at hlt
  interval_cases n
  · rw [Fin.sum_univ_one] at hclosed
    exact stepOf_ne_zero (d 0) hclosed
  · have ht0 := hreflexfree 0
    have ht1 := hreflexfree 1
    rw [Fin.sum_univ_two] at hclosed
    simp only [show ((0 : Fin 2) + 1 = 1) from rfl,
      show ((1 : Fin 2) + 1 = 0) from rfl] at ht0 ht1
    obtain ⟨a, ha⟩ : ∃ a, d 0 = a := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, d 1 = b := ⟨_, rfl⟩
    rw [ha, hb] at hclosed ht0 ht1
    fin_cases a <;> fin_cases b <;> revert hclosed ht0 ht1 <;> decide

/-- Discrete Umlaufsatz (theorem of turning tangents) for lattice walks without right turns: a
  simple closed walk on `ℤ²` whose every turn is straight or a left quarter turn has exactly four
  left turns, i.e. its direction makes one full counterclockwise revolution. Right turns and
  reversals are excluded by hypothesis, so the walks covered are exactly counterclockwise
  boundaries of lattice rectangles (no reflex corner); the general signed statement is
  `StatMech.Onsager.GeneralUmlaufsatz.turnSum_eq_four_or_neg_four`. Compare H. Hopf, *Über die
  Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Math. 2 (1935), for smooth curves. -/
theorem cc_eq_four_of_no_right_turn {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cc d = 4 :=
  cc_eq_four d hclosed hsimple (three_le_n d hclosed hreflexfree) hreflexfree

/-- The hypothesis of `StatMech.Onsager.BaseCase.base_cc_eq_four` holds: a simple closed walk
  without right turns has fewer than eight left turns. -/
theorem hnodbl_discharged {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    Function.Injective (pos d) → cc d < 8 :=
  fun hsimple => by rw [cc_eq_four_of_no_right_turn d hclosed hsimple hreflexfree]; norm_num

end StatMech.Onsager.UmlaufsatzFinal
