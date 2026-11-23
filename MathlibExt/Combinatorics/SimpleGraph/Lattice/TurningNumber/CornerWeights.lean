/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellGaussBonnet
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LeftCornerE
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LeftCornerN
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LeftCornerS
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.LeftCornerW
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.StraightCorner
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCornerSum

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Corner weights along a simple closed walk without right turns

Combining the straight and left-turn cases, the corner weight of the interior at the vertex after
step `i` is `σ` at a left turn and `0` at a straight step, where `σ = ±1` is fixed by the
orientation (`leftParity d 0`). Summing over the walk gives `cornerDiff = σ * cc d`; with the cell
Gauss–Bonnet formula this reduces the count of left turns to the Euler characteristic of the
interior.

## Main results

* `StatMech.Onsager.MasterCorner.cornerWeight_master`.
* `StatMech.Onsager.MasterCorner.cornerDiff_eq_weight_mul_cc`.
* `StatMech.Onsager.MasterCorner.cc_eq_four`: four left turns, given a pinch-free interior of
  Euler characteristic `1`.
-/

@[expose] public section

namespace StatMech.Onsager.MasterCorner

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.InteriorCells StatMech.Onsager.Orientation StatMech.Onsager.LeftCornerN
  StatMech.Onsager.LeftCornerE StatMech.Onsager.LeftCornerW StatMech.Onsager.LeftCornerS
  StatMech.Onsager.StraightCorner StatMech.Onsager.WalkCornerSum StatMech.Onsager.CellPinch
  StatMech.Onsager.CellGaussBonnetGlobal

variable {n : ℕ} [NeZero n]

/-- The corner weight of the interior at the vertex after step `i` is `±1` (sign given by the
  orientation) at a left turn and `0` at a straight step. -/
theorem cornerWeight_master (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) (i : Fin n) :
    cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1)))
      = (if leftParity d 0 = 1 then (1 : ℤ) else -1) * (if d (i + 1) - d i = 1 then 1 else 0) := by
  rcases hreflexfree i with h0 | h1
  · have hst : d (i + 1) = d i := by rw [sub_eq_zero] at h0; exact h0
    rw [cornerWeight_straight d hclosed hsimple i hst,
      ite_eq_right (show ¬ (d (i + 1) - d i = 1) from by rw [h0]; decide), mul_zero]
  · rw [ite_eq_left h1, mul_one]
    have hlp : rayParity d (leftCell (d (i + 1)) (pos d (i + 1))).1
          (leftCell (d (i + 1)) (pos d (i + 1))).2 = leftParity d 0 :=
      leftParity_const d hclosed hsimple hreflexfree (i + 1)
    have hei : d i = d (i + 1) - 1 := by
      rw [eq_sub_iff_add_eq, sub_eq_iff_eq_add.mp h1]; abel
    rcases (by decide : ∀ w : Fin 4, w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) (d (i + 1)) with
      hd | hd | hd | hd
    · rw [cornerWeight_leftTurn_E d hclosed hsimple hn i (by rw [hei, hd]; decide) hd, hlp]
    · rw [cornerWeight_leftTurn_N d hclosed hsimple hn i (by rw [hei, hd]; decide) hd, hlp]
    · rw [cornerWeight_leftTurn_W d hclosed hsimple hn i (by rw [hei, hd]; decide) hd, hlp]
    · rw [cornerWeight_leftTurn_S d hclosed hsimple hn i (by rw [hei, hd]; decide) hd, hlp]

/-- The corner defect of the interior equals `±cc d`, the sign given by the orientation of the
  walk. -/
theorem cornerDiff_eq_weight_mul_cc (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cornerDiff (interiorCells d hclosed)
      = (if leftParity d 0 = 1 then (1 : ℤ) else -1) * (cc d : ℤ) := by
  rw [cornerDiff_interior_eq_walk_sum d hclosed hsimple,
    ← Equiv.sum_comp (Equiv.addRight (1 : Fin n))
      (fun k => cornerWeight (cornerCount (interiorCells d hclosed) (pos d k)))]
  simp only [Equiv.coe_addRight]
  rw [Finset.sum_congr rfl (fun i _ => cornerWeight_master d hclosed hsimple hn hreflexfree i),
    ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_boole]
  rfl

/-- A simple closed walk without right turns whose interior is pinch-free with Euler characteristic
  `1` has four left turns. -/
theorem cc_eq_four (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (hpinch : pinchCount (interiorCells d hclosed) = 0)
    (hchi : eulerChar (interiorCells d hclosed) = 1) :
    cc d = 4 := by
  have h1 := cornerDiff_eq_weight_mul_cc d hclosed hsimple hn hreflexfree
  have h2 := cornerDiff_eq (interiorCells d hclosed)
  rw [hchi, hpinch] at h2
  norm_num at h2
  have h3 : (if leftParity d 0 = 1 then (1 : ℤ) else -1) * (cc d : ℤ) = 4 := h1.symm.trans h2
  have hcc4 : 4 ≤ cc d := four_le_cc d hclosed hreflexfree
  by_cases hW : leftParity d 0 = 1
  · rw [ite_eq_left hW, one_mul] at h3; omega
  · rw [ite_eq_right hW] at h3; omega

end StatMech.Onsager.MasterCorner
