/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellEuler

import Mathlib.Tactic.NormNum

/-!
# The local identity behind the cell Gauss–Bonnet formula

The naive discrete Gauss–Bonnet formula `cornerDiff S = 4 * eulerChar S` fails for cell sets with
pinch points, where two cells touch only at a corner: the two diagonal cells `(0, 0)` and
`(1, 1)` have corner defect `6` and Euler characteristic `1`. This file sets up the local
bookkeeping for adding one cell, in terms of the Booleans `e, w, n, s, ne, nw, se, sw` recording
which neighbouring cells are present, and checks by exhaustion over the `2⁸` cases that the change
of the corner defect equals four times the change of the Euler characteristic plus twice the change
of the number of pinch points.

## Main definitions

* `StatMech.Onsager.CellGaussBonnet.lhsLocal`: the change of the corner defect.
* `StatMech.Onsager.CellGaussBonnet.deltaV`, `StatMech.Onsager.CellGaussBonnet.deltaE`: the new
  vertices and edges.
* `StatMech.Onsager.CellGaussBonnet.pinchDelta`: the change of the number of pinch points.

## Main results

* `StatMech.Onsager.CellGaussBonnet.gaussBonnet_stated_false`: the formula without pinch term fails.
* `StatMech.Onsager.CellGaussBonnet.localIdentity_corrected`: the local identity with pinch term.
-/

@[expose] public section

namespace StatMech.Onsager.CellGaussBonnet

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler

/-- Two diagonally touching cells have corner defect `6`. -/
theorem cornerDiff_cex :
    cornerDiff ({((0:ℤ), (0:ℤ)), ((1:ℤ), (1:ℤ))} : Finset (ℤ × ℤ)) = 6 := by decide

/-- Two diagonally touching cells have Euler characteristic `1`. -/
theorem eulerChar_cex :
    eulerChar ({((0:ℤ), (0:ℤ)), ((1:ℤ), (1:ℤ))} : Finset (ℤ × ℤ)) = 1 := by decide

/-- The formula `cornerDiff S = 4 * eulerChar S` fails in general (two diagonally touching cells);
  see `StatMech.Onsager.CellGaussBonnetGlobal.cornerDiff_eq` for the correct formula with a pinch
  term. -/
theorem gaussBonnet_stated_false :
    ¬ ∀ S : Finset (ℤ × ℤ), cornerDiff S = 4 * eulerChar S := by
  intro h
  have := h ({((0:ℤ), (0:ℤ)), ((1:ℤ), (1:ℤ))} : Finset (ℤ × ℤ))
  rw [cornerDiff_cex, eulerChar_cex] at this
  norm_num at this

/-- The indicator `1` or `0` of a Boolean. -/
def bI (b : Bool) : ℤ := if b then 1 else 0

/-- The vertex weight `cornerWeight` extended to integers. -/
def icw (k : ℤ) : ℤ := (if k = 1 then 1 else 0) - (if k = 3 then 1 else 0)

/-- The change of the vertex weight from `m` to `m + 1` incident cells. -/
def ijump (m : ℤ) : ℤ := icw (m + 1) - icw m

/-- The indicator of `m = 0`. -/
def isZero (m : ℤ) : ℤ := if m = 0 then 1 else 0

/-- The change of the corner defect when a cell is added, given which of its eight neighbours are
  present (`e, w, n, s, ne, nw, se, sw`). -/
def lhsLocal (e w n s ne nw se sw : Bool) : ℤ :=
  ijump (bI w + bI s + bI sw) + ijump (bI e + bI se + bI s)
    + ijump (bI n + bI nw + bI w) + ijump (bI ne + bI n + bI e)

/-- The number of new vertices when a cell is added, given its eight neighbours. -/
def deltaV (e w n s ne nw se sw : Bool) : ℤ :=
  isZero (bI w + bI s + bI sw) + isZero (bI e + bI se + bI s)
    + isZero (bI n + bI nw + bI w) + isZero (bI ne + bI n + bI e)

/-- The number of new edges when a cell is added, given its four side neighbours. -/
def deltaE (e w n s : Bool) : ℤ :=
  (1 - bI s) + (1 - bI n) + (1 - bI w) + (1 - bI e)

/-- Four times the change of the Euler characteristic when a cell is added. -/
def rhsStated (e w n s ne nw se sw : Bool) : ℤ :=
  4 * (deltaV e w n s ne nw se sw - deltaE e w n s + 1)

/-- The change of the corner defect is not always four times the change of the Euler
  characteristic. -/
theorem localIdentity_stated_false :
    ¬ ∀ e w n s ne nw se sw : Bool,
      lhsLocal e w n s ne nw se sw = rhsStated e w n s ne nw se sw := by
  intro h
  have := h false false false false false false false true
  simp only [lhsLocal, rhsStated, deltaV, deltaE, bI, ijump, icw, isZero] at this
  norm_num at this

/-- The change of the number of pinch points at the four corners of a new cell, given its eight
  neighbours. -/
def pinchDelta (e w n s ne nw se sw : Bool) : ℤ :=
  (bI (sw && !w && !s) - bI (w && s && !sw))
  + (bI (se && !e && !s) - bI (e && s && !se))
  + (bI (nw && !n && !w) - bI (n && w && !nw))
  + (bI (ne && !n && !e) - bI (n && e && !ne))

/-- Four times the change of the Euler characteristic plus twice the change of the number of pinch
  points. -/
def rhsCorrected (e w n s ne nw se sw : Bool) : ℤ :=
  rhsStated e w n s ne nw se sw + 2 * pinchDelta e w n s ne nw se sw

/-- Local cell Gauss–Bonnet identity: when a cell is added, the change of the corner defect is four
  times the change of the Euler characteristic plus twice the change of the number of pinch
  points. -/
theorem localIdentity_corrected :
    ∀ e w n s ne nw se sw : Bool,
      lhsLocal e w n s ne nw se sw = rhsCorrected e w n s ne nw se sw := by
  decide

end StatMech.Onsager.CellGaussBonnet
