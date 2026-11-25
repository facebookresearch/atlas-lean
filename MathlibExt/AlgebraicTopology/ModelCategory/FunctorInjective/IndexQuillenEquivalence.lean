/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.CategoryTheory.Functor.KanExtension.RightIndexAdjunctionProperties
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.KanExtensions
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# Quillen equivalence of the existing native Ran along an index equivalence

The adjunction is the existing e.functor.ranAdjunction M. The given
original models retain their pointwise weak and left classes. No
injective model, index equivalence or Kan extension is chosen anew.
-/

set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM
open CategoryTheory Functor

namespace HomotopicalAlgebra.FunctorInjective.IndexQuillenEquivalence

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]
  [ModelCategory (D ⥤ M)] [ModelCategory (E ⥤ M)]
  (e : D ≌ E) [∀ F : D ⥤ M, e.functor.HasRightKanExtension F]

/-- The actual native forward Ran adjunct detects weak arrows in the original models. -/
theorem homEquiv_weakEquivalence_iff_of_pointwise
    (hWD : weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D)
    (hWE : weakEquivalences (E ⥤ M) = (weakEquivalences M).functorCategory E)
    {X : E ⥤ M} {Y : D ⥤ M} (f : e.functor ⋙ X ⟶ Y) :
    weakEquivalences (D ⥤ M) f ↔
      weakEquivalences (E ⥤ M) ((e.functor.ranAdjunction M).homEquiv X Y f) := by
  rw [hWD, hWE]
  exact RightIndexAdjunctionProperties.homEquiv_property_iff e (weakEquivalences M) f

/-- The inverse of the same native Ran Hom equivalence retains the original weak criterion. -/
theorem inverse_weakEquivalence_iff_of_pointwise
    (hWD : weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D)
    (hWE : weakEquivalences (E ⥤ M) = (weakEquivalences M).functorCategory E)
    {X : E ⥤ M} {Y : D ⥤ M} (c : X ⟶ e.functor.ran.obj Y) :
    weakEquivalences (E ⥤ M) c ↔
      weakEquivalences (D ⥤ M) (((e.functor.ranAdjunction M).homEquiv X Y).symm c) := by
  rw [hWE, hWD]
  exact RightIndexAdjunctionProperties.inverse_property_iff e (weakEquivalences M) c

/-- Given original pointwise weak and left classes give QE of the same native Ran adjunction. -/
theorem isQuillenEquivalence_of_pointwise_classes
    (hWD : weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D)
    (hWE : weakEquivalences (E ⥤ M) = (weakEquivalences M).functorCategory E)
    (hCD : cofibrations (D ⥤ M) = (cofibrations M).functorCategory D)
    (hCE : cofibrations (E ⥤ M) = (cofibrations M).functorCategory E)
    (hTD : trivialCofibrations (D ⥤ M) = (trivialCofibrations M).functorCategory D)
    (hTE : trivialCofibrations (E ⥤ M) = (trivialCofibrations M).functorCategory E) :
    (e.functor.ranAdjunction M).IsQuillenEquivalence where
  toIsQuillenAdjunction :=
    KanExtensions.isQuillen_of_pointwise_left_classes e.functor hCD hCE hTD hTE
  homEquiv_weakEquivalence_iff f :=
    homEquiv_weakEquivalence_iff_of_pointwise e hWD hWE f

end HomotopicalAlgebra.FunctorInjective.IndexQuillenEquivalence
