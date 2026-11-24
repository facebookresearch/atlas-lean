/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.RingTheory.Ideal.AdicAssociatedGraded

/-!
# Associated-graded pieces of an ideal

For an ideal `I` in a commutative ring, this file defines the degree-`n`
piece `I ^ n / I ^ (n + 1)`, the external direct-sum carrier of all pieces,
and the initial-form quotient map in a fixed degree.

The piece, direct-sum carrier and symbol interfaces reuse the canonical
ideal-adic provider, including its existing graded multiplication. This file
constructs no second multiplication.

## Main declarations

* `Ideal.AssociatedGradedPiece`
* `Ideal.AssociatedGraded`
* `Ideal.initialForm`
* `Ideal.initialForm_apply`
* `Ideal.initialForm_surjective`
* `Ideal.initialForm_eq_zero_iff`
-/

@[expose] public section

set_option autoImplicit false

open scoped DirectSum

namespace Ideal

universe u

variable {R : Type u} [CommRing R]

/-- The degree-`n` piece `I ^ n / I ^ (n + 1)` of the associated graded
ring, presented as a quotient of the ideal `I ^ n` by `I • ⊤`. -/
abbrev AssociatedGradedPiece (I : Ideal R) (n : ℕ) : Type u :=
  I.adicGradedPiece n

/-- The canonical ideal-adic associated-graded carrier, with its existing
graded-ring structure. -/
noncomputable abbrev AssociatedGraded (I : Ideal R) : Type u :=
  I.adicAssociatedGraded

/-- The class of an element of `I ^ n` in the degree-`n` associated-graded
piece. -/
def initialForm (I : Ideal R) (n : ℕ) :
    (I ^ n : Ideal R) →ₗ[R] AssociatedGradedPiece I n :=
  I.adicSymbol n

@[simp]
lemma initialForm_apply (I : Ideal R) (n : ℕ) (x : (I ^ n : Ideal R)) :
    initialForm I n x = Submodule.Quotient.mk x :=
  rfl

/-- Every class in a graded piece has a representative in `I ^ n`. -/
theorem initialForm_surjective (I : Ideal R) (n : ℕ) :
    Function.Surjective (initialForm I n) :=
  Submodule.mkQ_surjective _

/-- An initial form vanishes exactly when its representative lies in the
next ideal power. -/
theorem initialForm_eq_zero_iff (I : Ideal R) (n : ℕ)
    (x : (I ^ n : Ideal R)) :
    initialForm I n x = 0 ↔ (x : R) ∈ I ^ (n + 1) := by
  rw [initialForm_apply, Submodule.Quotient.mk_eq_zero]
  simp [Submodule.mem_smul_top_iff, pow_succ']

end Ideal
