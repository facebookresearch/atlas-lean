/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory.Restriction
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# The actual native right Kan Quillen adjunction for existing injective classes

The functor and adjunction are the existing `u.ran` and `u.ranAdjunction`.
The two original diagram models and their pointwise left classes are
given. This theorem constructs no model or replacement algorithm.
-/

set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM
open CategoryTheory Functor MorphismProperty

namespace HomotopicalAlgebra.FunctorInjective.KanExtensions

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]

/-- Original restriction preserves both given pointwise injective left classes. -/
theorem preserves_left_classes_of_eqs
    [CategoryWithCofibrations (D ⥤ M)] [CategoryWithCofibrations (E ⥤ M)]
    [CategoryWithWeakEquivalences (D ⥤ M)] [CategoryWithWeakEquivalences (E ⥤ M)]
    (hCD : cofibrations (D ⥤ M) = (cofibrations M).functorCategory D)
    (hCE : cofibrations (E ⥤ M) = (cofibrations M).functorCategory E)
    (hTD : trivialCofibrations (D ⥤ M) = (trivialCofibrations M).functorCategory D)
    (hTE : trivialCofibrations (E ⥤ M) = (trivialCofibrations M).functorCategory E)
    (u : D ⥤ E) :
    PreservesCofibrations ((whiskeringLeft D E M).obj u) ∧
      PreservesTrivialCofibrations ((whiskeringLeft D E M).obj u) := by
  constructor
  · change cofibrations (E ⥤ M) ≤
      (cofibrations (D ⥤ M)).inverseImage ((whiskeringLeft D E M).obj u)
    rw [hCE, hCD]
    exact functorCategory_le_inverseImage_whiskeringLeft (cofibrations M) u
  · change trivialCofibrations (E ⥤ M) ≤
      (trivialCofibrations (D ⥤ M)).inverseImage ((whiskeringLeft D E M).obj u)
    rw [hTE, hTD]
    exact functorCategory_le_inverseImage_whiskeringLeft (trivialCofibrations M) u

/-- The actual native Ran adjunction is Quillen for the given original pointwise left classes. -/
theorem isQuillen_of_pointwise_left_classes (u : D ⥤ E)
    [∀ F : D ⥤ M, u.HasRightKanExtension F]
    [ModelCategory (D ⥤ M)] [ModelCategory (E ⥤ M)]
    (hCD : cofibrations (D ⥤ M) = (cofibrations M).functorCategory D)
    (hCE : cofibrations (E ⥤ M) = (cofibrations M).functorCategory E)
    (hTD : trivialCofibrations (D ⥤ M) = (trivialCofibrations M).functorCategory D)
    (hTE : trivialCofibrations (E ⥤ M) = (trivialCofibrations M).functorCategory E) :
    (u.ranAdjunction M).IsQuillenAdjunction := by
  have h := preserves_left_classes_of_eqs hCD hCE hTD hTE u
  exact ⟨h.1, h.2⟩

end HomotopicalAlgebra.FunctorInjective.KanExtensions
