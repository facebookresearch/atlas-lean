/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Finite.FiniteFieldSquare
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

@[expose] public section

set_option autoImplicit false

/-!
# Examples for squares avoiding `0`, `1`, and `-1` in finite fields

Exercises `exists_sq_ne_zero_one_neg_one` on `ZMod 7` (concrete witness `2`,
since `2 ^ 2 = 4`), on the non-prime field `GaloisField 2 3` (eight
elements), and checks sharpness: over `ZMod 5` every square is `0`, `1`, or
`-1`, so the hypothesis `5 < |F|` cannot be weakened to `4 < |F|`.
-/

/-- Over `ZMod 7`, the element `2` has square `4`, avoiding `0`, `1`, `-1`. -/
example : ∃ r : ZMod 7, r ^ 2 ≠ 0 ∧ r ^ 2 ≠ 1 ∧ r ^ 2 ≠ -1 := by
  exact ⟨2, by decide, by decide, by decide⟩

/-- The abstract theorem applied to `ZMod 7`. -/
example : ∃ r : ZMod 7, r ^ 2 ≠ 0 ∧ r ^ 2 ≠ 1 ∧ r ^ 2 ≠ -1 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact exists_sq_ne_zero_one_neg_one (F := ZMod 7) (by simp [ZMod.card])

/-- The abstract theorem applied to the eight-element field. -/
example : ∃ r : GaloisField 2 3, r ^ 2 ≠ 0 ∧ r ^ 2 ≠ 1 ∧ r ^ 2 ≠ -1 := by
  classical
  have : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  refine exists_sq_ne_zero_one_neg_one ?_
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
  norm_num

/-- Sharpness: over `ZMod 5`, every square is `0`, `1`, or `-1`. -/
example : ∀ r : ZMod 5, r ^ 2 = 0 ∨ r ^ 2 = 1 ∨ r ^ 2 = -1 := by decide
