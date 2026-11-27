/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FrobeniusDeterminant

/-! # Tests for `MathlibExt.GroupTheory.FrobeniusDeterminant` -/

namespace MathlibExtTest.FrobeniusDeterminant

open MvPolynomial
open MathlibExt.GroupTheory.FrobeniusDeterminantWanted.RepresentationTheory.FrobeniusDeterminant

-- Test section: the group matrix has the variable `x_{gh}` at `(g, h)`, not `x_{gh⁻¹}`.
example (G : Type*) [Group G] [Fintype G] [DecidableEq G] (g h : G) :
    groupMatrix G g h = X (g * h) :=
  rfl

-- Its row at the identity lists the variables in the order of the columns.
example (G : Type*) [Group G] [Fintype G] [DecidableEq G] (h : G) :
    groupMatrix G 1 h = X h := by
  simp [groupMatrix]

-- Test section: the group determinant of the trivial group is its single variable.
example : groupDeterminant Unit = X () := by
  simp [groupDeterminant, groupMatrix, Matrix.det_unique]

-- Test section: the Frobenius determinant theorem. The group determinant of every finite group is
-- a nonzero polynomial, since it is a product of powers of irreducible polynomials.
example (G : Type*) [Group G] [Fintype G] [DecidableEq G] : groupDeterminant G ≠ 0 := by
  obtain ⟨r, p, -, hirr, -, hdet⟩ := frobenius_group_determinant G
  rw [hdet, Finset.prod_ne_zero_iff]
  exact fun j _ => pow_ne_zero _ (hirr j).ne_zero

-- For an abelian group every conjugacy class is a single element, so the group determinant has
-- as many pairwise non-associated irreducible factors as the group has elements.
example (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] :
    ∃ p : Fin (Nat.card G) → MvPolynomial G ℂ, (∀ j, Irreducible (p j)) ∧
      (∀ i j, i ≠ j → ¬ Associated (p i) (p j)) ∧
      groupDeterminant G = ∏ j, p j ^ (p j).totalDegree := by
  obtain ⟨r, p, hr, hirr, hassoc, hdet⟩ := frobenius_group_determinant G
  obtain rfl : r = Nat.card G := hr.trans (Nat.card_congr ConjClasses.mkEquiv.symm)
  exact ⟨p, hirr, hassoc, hdet⟩

-- The trivial group has a single conjugacy class: its group determinant, the variable `x_1`, is a
-- power of a single irreducible polynomial.
example : ∃ p : Fin 1 → MvPolynomial Unit ℂ, (∀ j, Irreducible (p j)) ∧
    X () = ∏ j, p j ^ (p j).totalDegree := by
  obtain ⟨r, p, hr, hirr, -, hdet⟩ := frobenius_group_determinant Unit
  obtain rfl : r = 1 :=
    hr.trans ((Nat.card_congr ConjClasses.mkEquiv.symm).trans Nat.card_unique)
  refine ⟨p, hirr, ?_⟩
  rw [← hdet]
  simp [groupDeterminant, groupMatrix, Matrix.det_unique]

end MathlibExtTest.FrobeniusDeterminant
