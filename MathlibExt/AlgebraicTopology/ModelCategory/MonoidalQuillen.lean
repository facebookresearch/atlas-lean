/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Fixed-left tensor Quillen adjunctions

In a closed symmetric monoidal model category, tensoring on the left by a
cofibrant object is a left Quillen functor.  The proof identifies its action
on a morphism with the pushout product against the initial map into the fixed
object and then applies the pushout-product axiom.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

private noncomputable def initialPushoutProductIso
    (K : C) {A B : C} (j : A ⟶ B) :
    (Arrow.mk (initial.to K) □ Arrow.mk j) ≅ Arrow.mk (K ◁ j) := by
  let hA : IsInitial ((⊥_ C) ⊗ A) :=
    initialIsInitial.isInitialObj (tensorRight A)
  let hB : IsInitial ((⊥_ C) ⊗ B) :=
    initialIsInitial.isInitialObj (tensorRight B)
  let _ : IsIso ((⊥_ C) ◁ j) := isIso_of_isInitial hA hB _
  have hp : IsPushout (initial.to K ▷ A) ((⊥_ C) ◁ j)
      (𝟙 (K ⊗ A)) (hB.to (K ⊗ A)) :=
    .of_vert_isIso (sq := ⟨hA.hom_ext _ _⟩)
  set_option backward.defeqAttrib.useBackward true in
    set_option backward.isDefEq.respectTransparency false in
      exact Arrow.isoMk' _ _ hp.isoPushout.symm (Iso.refl _)
        (pushout.hom_ext (by simp) (hB.hom_ext _ _))

/-- Tensoring on the left by a cofibrant object is a left Quillen functor in
a closed symmetric monoidal model category. -/
theorem ihomAdjunction_isQuillenAdjunction_of_isCofibrant
    (K : C) [IsCofibrant K] :
    Adjunction.IsQuillenAdjunction (ihom.adjunction K) :=
  { preservesCofibrations := by
      intro A B j hj
      have hbox :=
        IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
          (C := C) (initial.to K) j
            ((cofibration_iff _).mp inferInstance) hj
      exact ((cofibrations C).arrow_mk_iso_iff
        (initialPushoutProductIso K j)).mp hbox
    preservesTrivialCofibrations := by
      intro A B j hj
      have hbox :=
        IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
          (C := C) (initial.to K) j
            ((cofibration_iff _).mp inferInstance) hj
      exact ((trivialCofibrations C).arrow_mk_iso_iff
        (initialPushoutProductIso K j)).mp hbox }

end HomotopicalAlgebra
