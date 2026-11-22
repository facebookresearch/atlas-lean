/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceConcatenationFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceComponentSourceNaturality

/-!
# Actual concatenation of original flagged components

The original full concatenation functor descends in both variables to
its actual category components. The map retains every original scalar
coefficient, and follows each original face, degeneracy and source map.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

variable {K L : SSet.{u}} {x y z : K _⦋0⦌} {q r : SimplexCategoryᵒᵖ}

private def rightConcatenation (T : Object K x y q) :
    Object K y z q ⥤ Object K x z q :=
  CategoryTheory.Prod.sectR T (Object K y z q) ⋙ concatenationFunctor K x y z q

private def leftConcatenation (U : Object K y z q) :
    Object K x y q ⥤ Object K x z q :=
  CategoryTheory.Prod.sectL (Object K x y q) U ⋙ concatenationFunctor K x y z q

/-- The SAME native original concatenation on the actual two component labels. -/
def concatenate (a : ConnectedComponents (Object K x y q))
    (b : ConnectedComponents (Object K y z q)) : ConnectedComponents (Object K x z q) :=
  _root_.Quotient.lift (fun T => (rightConcatenation (z := z) T).mapConnectedComponents b)
    (by
      intro T T' h
      induction b using _root_.Quotient.inductionOn' with
      | h U =>
        exact _root_.Quotient.sound (zigzag_obj_of_zigzag (leftConcatenation (x := x) U) h)) a

/-- Both original complete objects give precisely their same native concatenation label. -/
theorem concatenate_mk (T : Object K x y q) (U : Object K y z q) :
    concatenate (ConnectedComponents.mk T) (ConnectedComponents.mk U) =
      ConnectedComponents.mk (concat T U) := rfl

/-- Original scalar restriction retains both entire inputs and all flags before concatenation. -/
theorem scalarObject_concat (θ : q ⟶ r) (T : Object K x y q) (U : Object K y z q) :
    scalarObject θ (concat T U) = concat (scalarObject θ T) (scalarObject θ U) := by
  rfl

/-- Every SAME original scalar operator commutes with the actual component concatenation. -/
theorem concatenate_scalar (θ : q ⟶ r)
    (a : ConnectedComponents (Object K x y q)) (b : ConnectedComponents (Object K y z q)) :
    (simplicialSet K x z).map θ (concatenate a b) =
      concatenate ((simplicialSet K x y).map θ a) ((simplicialSet K y z).map θ b) := by
  induction a using _root_.Quotient.inductionOn' with
  | h T =>
    induction b using _root_.Quotient.inductionOn' with
    | h U =>
      exact congrArg ConnectedComponents.mk (scalarObject_concat θ T U)

/-- The genuine full component composition map at the same original three vertex labels. -/
def composition (K : SSet.{u}) (x y z : K _⦋0⦌) :
    simplicialSet K x y ⊗ simplicialSet K y z ⟶ simplicialSet K x z where
  app q := ↾fun ab => concatenate ab.1 ab.2
  naturality _q _r θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b⟩
    exact (concatenate_scalar θ a b).symm

/-- The full original composition map retains both actual original necklaces in every scalar. -/
theorem composition_app_mk (K : SSet.{u}) (x y z : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (T : Object K x y q) (U : Object K y z q) :
    (composition K x y z).app q (ConnectedComponents.mk T, ConnectedComponents.mk U) =
      ConnectedComponents.mk (concat T U) := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
