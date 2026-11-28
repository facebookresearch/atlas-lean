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
# Associated graded pieces and initial forms

For an ideal `I` in a commutative ring `R`, the degree-`n` piece is `I^n/I^(n+1)`, represented
as the quotient of the module `I^n` by `I • ⊤` inside that module. The associated graded ring
is the direct sum of these pieces over `n : ℕ`.

The `R`-linear initial-form map sends `x : I^n` to its quotient class. It is surjective, and
its value is zero exactly when the underlying element of `R` lies in `I^(n+1)`.

Reference: Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
-/

@[expose] public section

set_option autoImplicit false

open scoped DirectSum

namespace Ideal

universe u

variable {R : Type u} [CommRing R]

/-- For an ideal `I` in a commutative ring `R` and `n : ℕ`, the degree-`n` associated graded piece
is `I^n/I^(n+1)`. Its quotient presentation is `(I^n : Ideal R) ⧸ (I • ⊤ : Submodule R (I^n :
Ideal R))`; multiplication by `I` on `I^n` has image `I^(n+1)`. -/
abbrev AssociatedGradedPiece (I : Ideal R) (n : ℕ) : Type u :=
  I.adicGradedPiece n

/-- For an ideal `I` in a commutative ring `R`, the associated graded ring `gr_I R` has underlying
direct sum `⨁ n : ℕ, I^n/I^(n+1)`. A representative `x ∈ I^p` multiplied by `y ∈ I^q`
represents the degree-`p+q` product `[xy]`. -/
noncomputable abbrev AssociatedGraded (I : Ideal R) : Type u :=
  I.adicAssociatedGraded

/-- For an ideal `I` in a commutative ring `R` and `n : ℕ`, `initialForm I n` is the `R`-linear
quotient map `I^n → I^n/I^(n+1)`. It sends `x : (I^n : Ideal R)` to `Submodule.Quotient.mk x`. -/
def initialForm (I : Ideal R) (n : ℕ) :
    (I ^ n : Ideal R) →ₗ[R] AssociatedGradedPiece I n :=
  I.adicSymbol n

@[simp]
lemma initialForm_apply (I : Ideal R) (n : ℕ) (x : (I ^ n : Ideal R)) :
    initialForm I n x = Submodule.Quotient.mk x :=
  rfl

/-- For an ideal `I` in a commutative ring `R` and every `n : ℕ`, the map `initialForm I n : I^n →
I^n/I^(n+1)` is surjective. Every element of the degree-`n` piece is the quotient class of an
element of `I^n`. -/
theorem initialForm_surjective (I : Ideal R) (n : ℕ) :
    Function.Surjective (initialForm I n) :=
  Submodule.mkQ_surjective _

/-- For an ideal `I` in a commutative ring `R`, `n : ℕ`, and `x : (I^n : Ideal R)`, the equation
`initialForm I n x = 0` holds if and only if `(x : R) ∈ I^(n+1)`. -/
theorem initialForm_eq_zero_iff (I : Ideal R) (n : ℕ)
    (x : (I ^ n : Ideal R)) :
    initialForm I n x = 0 ↔ (x : R) ∈ I ^ (n + 1) := by
  rw [initialForm_apply, Submodule.Quotient.mk_eq_zero]
  simp [Submodule.mem_smul_top_iff, pow_succ']

end Ideal
