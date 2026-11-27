/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellLucasDiophantinePellLucasSequenceIsSquareIff
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs
import MathlibExt.NumberTheory.PellLucasDiophantine
import MathlibExt.NumberTheory.PellNumberSequence

/-!
# Tests for square Pell–Lucas numbers

The classification gives both square terms and excludes later terms, including indices
in the even and odd residue classes.

Source: Sérgio Mendes, "The Diophantine Equation `Q_n^x + Q_{n+1}^x = y^2`",
INTEGERS 26 (2026), Article A72, Lemma 2
(<https://math.colgate.edu/~integers/vol26.html>).
-/

set_option autoImplicit false

namespace MathlibExtTest.NumberTheory.PellLucasDiophantinePellLucasSequenceIsSquareIff

open MathlibExt.NumberTheory.PellLucasDiophantineWanted

example : IsSquare (MetaMathlibExt.pellLucasSequence 0) :=
  (pellLucasSequence_isSquare_iff 0).mpr (Or.inl rfl)

example : IsSquare (MetaMathlibExt.pellLucasSequence 1) :=
  (pellLucasSequence_isSquare_iff 1).mpr (Or.inr rfl)

example : ¬IsSquare (MetaMathlibExt.pellLucasSequence 3) := by
  intro h
  have hn := (pellLucasSequence_isSquare_iff 3).mp h
  omega

example : ¬IsSquare (MetaMathlibExt.pellLucasSequence 4) := by
  intro h
  have hn := (pellLucasSequence_isSquare_iff 4).mp h
  omega

example : ¬IsSquare (MetaMathlibExt.pellLucasSequence 5) := by
  intro h
  have hn := (pellLucasSequence_isSquare_iff 5).mp h
  omega

example (n : ℕ) (hn : 2 ≤ n) : ¬IsSquare (MetaMathlibExt.pellLucasSequence n) := by
  intro h
  have hindex := (pellLucasSequence_isSquare_iff n).mp h
  omega

end MathlibExtTest.NumberTheory.PellLucasDiophantinePellLucasSequenceIsSquareIff
