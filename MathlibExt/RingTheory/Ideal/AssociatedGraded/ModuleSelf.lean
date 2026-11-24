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
# The regular module and associated-graded ring pieces

For the regular module `R`, the degree-`n` associated-graded module piece is
canonically linearly equivalent over `R ⧸ I` to the degree-`n` piece of the
associated-graded ring.  The equivalence preserves initial forms of
representatives.


## Main declarations

* `Ideal.associatedGradedModulePieceSelfEquiv`
* `Ideal.associatedGradedModulePieceSelfEquiv_initialForm`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Ideal

universe u

variable {R : Type u} [CommRing R]

/-- The degree-`n` associated-graded piece of the regular module is the
corresponding degree-`n` piece of the associated-graded ring. -/
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

/-- The regular-module equivalence sends a module initial form to the ring
initial form of the same representative. -/
theorem associatedGradedModulePieceSelfEquiv_initialForm
    (I : Ideal R) (n : ℕ) (x : (I ^ n : Ideal R)) :
    I.associatedGradedModulePieceSelfEquiv n
      (I.initialFormModule R n ⟨x, by simp [x.2]⟩) =
      I.initialForm n x := by
  rfl

end Ideal
