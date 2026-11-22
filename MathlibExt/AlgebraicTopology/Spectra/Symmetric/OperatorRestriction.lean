/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorRepresentation
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorIndexSource
public import MathlibExt.CategoryTheory.Enriched.WholeRepresentationCurry

/-!
# Restricting the genuine operator to every original finite-index arrow

The original index arrow embeds as its full empty coefficient. Restriction
uses the actual underlying functor of the genuine enriched representation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  {T : V}

/-- Every original value object of the actual coend representation. -/
def representationObject (X : Representation T) (n : I) : V := by
  letI : EnrichedCategory V I := enrichedCategory T
  exact X.obj n

/-- The actual entire operator action, with its explicit coend source and value target. -/
def representationAction (X : Representation T) (n k : I) :
    representationObject X n ⊗ Hom T n k ⟶ representationObject X k := by
  letI : EnrichedCategory V I := enrichedCategory T
  exact X.action n k

/-- The full original representation action retains the actual operator identity equation. -/
theorem representationAction_unit (X : Representation T) (n : I) :
    (representationObject X n ◁ identity T n) ≫ representationAction X n n =
      (ρ_ (representationObject X n)).hom := by
  let _ : EnrichedCategory V I := enrichedCategory T
  exact X.unit n

/-- The full original representation action retains the complete operator composition equation. -/
theorem representationAction_assoc (X : Representation T) (n k l : I) :
    (α_ (representationObject X n) (Hom T n k) (Hom T k l)).inv ≫
      representationAction X n k ▷ Hom T k l ≫ representationAction X k l =
      (representationObject X n ◁ composition T n k l) ≫ representationAction X n l := by
  let _ : EnrichedCategory V I := enrichedCategory T
  exact X.assoc n k l

/-- All original finite-index maps embed into the actual underlying operator category. -/
def indexEmbedding (T : V) :
    letI : EnrichedCategory V I := enrichedCategory T
    I ⥤ ForgetEnrichment V I := by
  letI : EnrichedCategory V I := enrichedCategory T
  exact
    { obj n := ForgetEnrichment.of V n
      map f := ForgetEnrichment.homOf V (arrow T f)
      map_id n := by
        exact (congrArg (ForgetEnrichment.homOf V) (arrow_id T n)).trans
          (ForgetEnrichment.homOf_eId V n)
      map_comp {n k l} f g := by
        exact (congrArg (ForgetEnrichment.homOf V) (arrow_comp T f g).symm).trans
          (ForgetEnrichment.homOf_comp V (X := n) (Y := k) (Z := l) (arrow T f) (arrow T g)) }

variable [MonoidalClosed V]

/-- The unchanged indexed objects and all original arrows of an actual enriched operator representation. -/
abbrev ordinaryDiagram (X : Representation T) : I ⥤ V := by
  letI : EnrichedCategory V I := enrichedCategory T
  exact indexEmbedding T ⋙ X.toEnrichedFunctor.forget ⋙ ForgetEnrichment.equivFunctor V V

/-- Every original object is retained by restriction. -/
theorem ordinaryDiagram_obj (X : Representation T) (n : I) :
    (ordinaryDiagram X).obj n = representationObject X n := rfl

/-- Every original index arrow acts by its entire degree-zero coefficient and genuine action. -/
theorem ordinaryDiagram_map (X : Representation T) {n k : I} (f : n ⟶ k) :
    (ordinaryDiagram X).map f =
      (ρ_ (representationObject X n)).inv ≫
        (representationObject X n ◁ arrow T f) ≫ representationAction X n k := by
  let _ : EnrichedCategory V I := enrichedCategory T
  change MonoidalClosed.uncurry' (arrow T f ≫ MonoidalClosed.curry (representationAction X n k)) = _
  rw [MonoidalClosed.uncurry', MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]

/-- The actual whole coefficient action extracted from the identity-labelled generator. -/
def representationCoefficient (X : Representation T) (a n : I) :
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ⊗ representationObject X n ⟶
      representationObject X (a ⊗ n) :=
  (β_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a) (representationObject X n)).hom ≫
    (representationObject X n ◁ generator T a n (a ⊗ n) (𝟙 (a ⊗ n))) ≫
      representationAction X n (a ⊗ n)

end CategoryTheory.Spectra.Symmetric.OperatorCoend
