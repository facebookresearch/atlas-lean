/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.ZMod
import MathlibExt.Combinatorics.Additive.FiniteFieldDifferenceBases

/-! # Tests for difference bases of finite-field squares -/

open MetaMathlibExt

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

example : groupDiffBasisNumber 1 (ZMod 3 × ZMod 3) ≤ 5 := by
  have h := groupDiffBasisNumber_prod_self_le (K := ZMod 3)
    (by rw [ZMod.ringChar_zmod_n]; decide)
  simpa only [Nat.card_eq_fintype_card, ZMod.card, groupDiffBasisNumber_one_zmod_three] using h

-- A nonzero first coordinate and nonzero second coordinate test the parabola witness formula.
example :
    let a : ZMod 3 := 2
    let b : ZMod 3 := 2
    let x := (a + b / a) / 2
    let y := x - a
    ((x, x ^ 2) : ZMod 3 × ZMod 3) - (y, y ^ 2) = (a, b) := by
  simp only [div_self (show (2 : ZMod 3) ≠ 0 by decide),
    show (2 : ZMod 3) + 1 = 0 by decide, zero_div]
  decide

-- A horizontal difference is possible even when the two parabola points have equal squares.
example : ((2, 1) : ZMod 3 × ZMod 3) - (1, 1) = (1, 0) := by decide

-- The vertical lift of {0, 1} overlaps the parabola at (0, 0); it still covers all residues.
example :
    let B : Finset (ZMod 3 × ZMod 3) :=
      (Finset.univ.image fun x : ZMod 3 => (x, x ^ 2)) ∪
        ({0, 1} : Finset (ZMod 3)).image (fun x => (0, x))
    B.card = 4 ∧ ∀ z, 1 ≤ subRepCount B z := by decide

-- In characteristic two the parabola alone misses a horizontal difference.
example : subRepCount (Finset.univ.image fun x : ZMod 2 => (x, x ^ 2)) (1, 0) = 0 := by decide
