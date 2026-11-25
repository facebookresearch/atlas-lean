/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Sqrt
import MathlibExt.NumberTheory.PowAddPowEqSqModSixty

/-! # Tests for the solutions of `n^x + (5p)^y = z^2` modulo 60 -/

open MathlibExt.NumberTheory.PowAddPowEqSqWanted

-- Both permitted exponents occur, with one witness from each residue class of n.
example : 27 ^ 0 + 35 ^ 1 = 6 ^ 2 :=
  (solutions_mod_sixty 27 7 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide)).2
    (Or.inl ⟨rfl, rfl, rfl⟩)

example : 63 ^ 1 + 95 ^ 0 = 8 ^ 2 :=
  (solutions_mod_sixty 63 19 1 0 8 (by decide) (by decide) (by decide) (by decide) (by decide)).2
    (Or.inr ⟨rfl, rfl, rfl⟩)

-- At n = 27 and p = 19, neither 28 nor 96 is a square.
example (x y z : ℕ) : 27 ^ x + 95 ^ y ≠ z ^ 2 := by
  intro h
  rcases (solutions_mod_sixty 27 19 x y z (by decide) (by decide) (by decide) (by decide)
    (by decide)).1 h with ⟨_, _, hz⟩ | ⟨_, _, hz⟩
  · exact Nat.not_exists_sq' (n := 96) (m := 9) (by decide) (by decide) ⟨z, hz⟩
  · exact Nat.not_exists_sq' (n := 28) (m := 5) (by decide) (by decide) ⟨z, hz⟩
