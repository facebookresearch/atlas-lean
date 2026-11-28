/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.InitialRepetitionsQuadraticNonresidues

/-! # Tests for the quadratic nonresidue count in the initial-repetitions congruences -/

open MetaMathlibExt

private def nonsquareResidues (p : ℕ) [NeZero p] : Finset ℕ :=
  letI (x : ZMod p) : Decidable (IsSquare x) :=
    inferInstanceAs (Decidable (∃ y : ZMod p, x = y * y))
  (Finset.Icc 1 (p - 1)).filter fun r ↦
    ¬ IsSquare ((16 * r + 1 : ℕ) : ZMod p) ∧ ¬ IsSquare ((8 * r + 1 : ℕ) : ZMod p)

-- Both primes omitted in the paper have no qualifying residues.
example : nonsquareResidues 2 = ∅ ∧ nonsquareResidues 3 = ∅ := by decide

-- In particular, r = 4 is excluded: 16 * 4 + 1 is zero modulo 5.
example : nonsquareResidues 5 = {2} := by decide

-- An odd prime congruent to 3 modulo 4 with a nonzero count.
example : nonsquareResidues 11 = {8, 9} := by decide

open scoped Classical in
example :
    ((Finset.Icc 1 6).filter fun r ↦
      ¬ IsSquare ((16 * r + 1 : ℕ) : ZMod 7) ∧ ¬ IsSquare ((8 * r + 1 : ℕ) : ZMod 7)).card = 1 :=
  card_not_isSquare_sixteen_mul_add_one_eight_mul_add_one 7 (by decide)
