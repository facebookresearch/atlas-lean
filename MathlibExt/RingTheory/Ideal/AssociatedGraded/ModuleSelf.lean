/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.RingTheory.Ideal.AssociatedGraded.Module

/-!
# Associated graded pieces of the regular module

For an ideal `I` in a commutative ring `R`, the regular module satisfies `I^n R = I^n`. The
resulting quotient identification gives an `R/I`-linear equivalence between its degree-`n`
associated graded module piece and `I^n/I^(n+1)`.

This equivalence sends the module initial form of a representative `x ∈ I^n` to the ring
initial form of the same `x`.

Reference: Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Ideal

universe u

variable {R : Type u} [CommRing R]

/-- Let `R` be a commutative ring, `I : Ideal R`, and `n : ℕ`. The equality `I^n • R = I^n`
identifies `I.AssociatedGradedModulePiece R n = I^n R/I^(n+1) R` with `I.AssociatedGradedPiece
n = I^n/I^(n+1)`. This is an `R/I`-linear equivalence, acting as the identity on
representatives in `I^n`. -/
noncomputable def associatedGradedModulePieceSelfEquiv
    (I : Ideal R) (n : ℕ) :
    I.AssociatedGradedModulePiece R n ≃ₗ[R ⧸ I]
      I.AssociatedGradedPiece n := by
  let A : Submodule R R := I ^ n • ⊤
  let B : Submodule R R := I ^ n
  have hAB : A = B := by
    ext x
    simp [A, B]
  let e : A ≃ₗ[R] B := LinearEquiv.ofEq A B hAB
  have he : Submodule.map e.toLinearMap (I • (⊤ : Submodule R A)) =
      I • (⊤ : Submodule R B) := by
    ext y
    simp [Submodule.mem_smul_top_iff, e]
  let eQ : (A ⧸ (I • ⊤ : Submodule R A)) ≃ₗ[R]
      (B ⧸ (I • ⊤ : Submodule R B)) :=
    Submodule.Quotient.equiv _ _ e he
  exact eQ.extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- Let `R` be a commutative ring, `I : Ideal R`, `n : ℕ`, and `x : (I^n : Ideal R)`. The
regular-module equivalence satisfies `I.associatedGradedModulePieceSelfEquiv n
(I.initialFormModule R n x) = I.initialForm n x`, where `x` on the module side is regarded as
an element of `I^n • R`. Both classes therefore have the same representative. -/
theorem associatedGradedModulePieceSelfEquiv_initialForm
    (I : Ideal R) (n : ℕ) (x : (I ^ n : Ideal R)) :
    I.associatedGradedModulePieceSelfEquiv n
      (I.initialFormModule R n ⟨x, by simp [x.2]⟩) =
      I.initialForm n x := by
  rfl

end Ideal
