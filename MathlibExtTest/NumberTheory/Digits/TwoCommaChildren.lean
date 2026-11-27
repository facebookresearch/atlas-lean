/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.TwoCommaChildren

open MetaMathlibExt

-- The upper endpoint for x in base three gives a single-digit parent.
example : ∃ y z : Fin 3, y ≠ z ∧ IsCommaCandidate 3 1 y ∧ IsCommaCandidate 3 1 z :=
  ((two_commaChildren_iff 3 (by decide)).1 1 (by decide) (by decide)).2
    ⟨1, by decide, by decide, rfl⟩

-- The largest allowed leading digit in base ten can occur with no middle nines.
example : ∃ y z : Fin 10, y ≠ z ∧ IsCommaCandidate 10 881 y ∧ IsCommaCandidate 10 881 z :=
  ((two_commaChildren_iff 10 (by decide)).2 881 (by decide)).2
    ⟨8, 0, by decide, by decide, by decide⟩

-- The decimal children of 1918 are 1999 and 2000. The parent has one middle nine.
example : ∃ y z : Fin 10, y ≠ z ∧ IsCommaCandidate 10 1918 y ∧ IsCommaCandidate 10 1918 z :=
  ((two_commaChildren_iff 10 (by decide)).2 1918 (by decide)).2
    ⟨1, 1, by decide, by decide, by decide⟩

-- In base two the required leading digit has an empty range.
example (n : ℕ) (hn : 4 ≤ n) :
    ¬ ∃ y z : Fin 2, y ≠ z ∧ IsCommaCandidate 2 n y ∧ IsCommaCandidate 2 n z := by
  intro h
  obtain ⟨d, _, hd, hd', _⟩ := ((two_commaChildren_iff 2 (by decide)).2 n hn).1 h
  omega
