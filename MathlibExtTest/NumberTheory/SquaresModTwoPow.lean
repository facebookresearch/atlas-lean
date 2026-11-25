/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquaresModTwoPow

/-!
# Tests for squares modulo consecutive powers of two
-/

open MetaMathlibExt

-- At k = 0 the truncated exponent gives a right-hand side outside the residue range.
example (x : ℕ) (hx : x < 2) : ¬(IsSquare (x : ZMod 1) ∧ ¬IsSquare (x : ZMod 2)) := by
  intro h
  have he : x = 2 := (isSquare_mod_two_pow_even_not_odd_iff 0 x hx).mp h
  omega

-- The first two nonempty cases have exceptional residues 5 and 20.
example : IsSquare (5 : ZMod 4) ∧ ¬IsSquare (5 : ZMod 8) :=
  (isSquare_mod_two_pow_even_not_odd_iff 1 5 (by decide)).mpr rfl

example : IsSquare (20 : ZMod 16) ∧ ¬IsSquare (20 : ZMod 32) :=
  (isSquare_mod_two_pow_even_not_odd_iff 2 20 (by decide)).mpr rfl

-- The root 1 of 17 modulo 16 ceases to work modulo 32, but another root exists.
example : IsSquare (17 : ZMod 32) := by
  by_contra hn
  have hs : IsSquare (17 : ZMod 16) := ⟨1, rfl⟩
  exact (by decide : (17 : ℕ) ≠ 20)
    ((isSquare_mod_two_pow_even_not_odd_iff 2 17 (by decide)).mp ⟨hs, hn⟩)

-- At k = 0 both moduli are 1, and the only representative is 0.
example : ¬(IsSquare (0 : ZMod 1) ∧ ¬IsSquare (0 : ZMod 1)) := by
  intro h
  have := (isSquare_mod_two_pow_odd_not_even_iff 0 0 (by decide)).mp h
  exact (by decide : ¬((0 : ℕ) = 1 ∨ 0 = 2)) this

-- Modulo 4, the two exceptional residues reduce to 0 and 1 modulo 2.
example : IsSquare (2 : ZMod 2) ∧ ¬IsSquare (2 : ZMod 4) :=
  (isSquare_mod_two_pow_odd_not_even_iff 1 2 (by decide)).mpr (Or.inl rfl)

example : IsSquare (3 : ZMod 2) ∧ ¬IsSquare (3 : ZMod 4) :=
  (isSquare_mod_two_pow_odd_not_even_iff 1 3 (by decide)).mpr (Or.inr rfl)

-- Multiplication by four carries the exceptional pair to 8 and 12 modulo 16.
example (x : ℕ) (hx : x < 16) :
    (IsSquare (x : ZMod 8) ∧ ¬IsSquare (x : ZMod 16)) ↔ x = 8 ∨ x = 12 :=
  isSquare_mod_two_pow_odd_not_even_iff 2 x hx
