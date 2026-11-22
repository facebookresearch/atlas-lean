/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveBasedNative.Migration
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Quillen

/-!
# Actual original presentations and literal strict native diagrams

Compose a proved whole source equivalence with the actual chosen-base
extension/restriction equivalence. The full source functors, units, counits
and both triangles are retained. All five actual model classes compare on
the same original source map. No model structure is an input.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped MonoidalClosed ZeroObject CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]

/-- The whole actual source equivalence followed by the proved strict extension equivalence. -/
def strictSourceEquivalence (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    C ≌ BasedNativePresentation.StrictCarrier (A := A) :=
  e.trans EnrichedZeroCompletion.basedDiagramEquivalence

/-- The whole forward source functor retains the actual original map and strict extension. -/
theorem strictSourceEquivalence_functor
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (strictSourceEquivalence e).functor = e.functor ⋙ EnrichedZeroCompletion.strictExtension :=
  rfl

/-- The whole inverse source functor is actual strict restriction and the original inverse. -/
theorem strictSourceEquivalence_inverse
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (strictSourceEquivalence e).inverse = EnrichedZeroCompletion.strictRestriction ⋙ e.inverse :=
  rfl

/-- Every actual converted source object preserves the chosen base literally. -/
theorem strictSourceEquivalence_base
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    ((strictSourceEquivalence e).functor.obj X).obj.toEnrichedFunctor.obj
      EnrichedZeroCompletion.zero = (0 : PointedCGWH.{u, v}) :=
  ((strictSourceEquivalence e).functor.obj X).property

/-- The full restriction comparison is the actual chosen-base equivalence unit inverse. -/
def strictSourceRestrictionIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (strictSourceEquivalence e).functor ⋙ EnrichedZeroCompletion.strictRestriction ≅ e.functor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e.functor EnrichedZeroCompletion.basedDiagramEquivalence.unitIso.symm ≪≫
      Functor.rightUnitor _

/-- The actual original-source and chosen-base units/counits satisfy the whole forward triangle. -/
theorem strictSourceEquivalence_functor_triangle
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (strictSourceEquivalence e).functor.map ((strictSourceEquivalence e).unitIso.hom.app X) ≫
      (strictSourceEquivalence e).counitIso.hom.app ((strictSourceEquivalence e).functor.obj X) =
        𝟙 _ :=
  (strictSourceEquivalence e).functor_unit_comp X

/-- The actual original-source and chosen-base units/counits satisfy the whole inverse triangle. -/
theorem strictSourceEquivalence_inverse_triangle
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (Y : BasedNativePresentation.StrictCarrier (A := A)) :
    (strictSourceEquivalence e).unitIso.hom.app ((strictSourceEquivalence e).inverse.obj Y) ≫
      (strictSourceEquivalence e).inverse.map ((strictSourceEquivalence e).counitIso.hom.app Y) =
        𝟙 _ :=
  (strictSourceEquivalence e).unit_inverse_comp Y

/-- The whole original source map retains the naturality of the actual composed unit. -/
theorem strictSourceEquivalence_unit_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    f ≫ (strictSourceEquivalence e).unitIso.hom.app Y =
      (strictSourceEquivalence e).unitIso.hom.app X ≫
        (strictSourceEquivalence e).inverse.map ((strictSourceEquivalence e).functor.map f) :=
  (strictSourceEquivalence e).unitIso.hom.naturality f

/-- The whole strict source map retains the naturality of the actual composed counit. -/
theorem strictSourceEquivalence_counit_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : BasedNativePresentation.StrictCarrier (A := A)} (f : X ⟶ Y) :
    (strictSourceEquivalence e).functor.map ((strictSourceEquivalence e).inverse.map f) ≫
      (strictSourceEquivalence e).counitIso.hom.app Y =
        (strictSourceEquivalence e).counitIso.hom.app X ≫ f :=
  (strictSourceEquivalence e).counitIso.hom.naturality f

private theorem strictSourceProperty_iff
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (P : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} A)) [P.RespectsIso]
    {X Y : C} (f : X ⟶ Y) :
    P (EnrichedZeroCompletion.strictRestriction.map ((strictSourceEquivalence e).functor.map f)) ↔
      P (e.functor.map f) :=
  P.arrow_mk_iso_iff
    (CategoryTheory.Arrow.isoOfNatIso (strictSourceRestrictionIso e) (CategoryTheory.Arrow.mk f))

variable [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The literal original source map retains the entire strict native weak class. -/
theorem strictSource_weakEquivalences_iff
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    (let _ : ModelCategory (BasedNativePresentation.StrictCarrier (A := A)) :=
       BasedNativePresentation.strictModelCategory
     weakEquivalences _ ((strictSourceEquivalence e).functor.map f)) ↔
    (let _ : ModelCategory C := modelCategory e
     weakEquivalences C f) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  exact strictSourceProperty_iff e (weakEquivalences _) f

/-- The literal original source map retains the entire strict native fibration class. -/
theorem strictSource_fibrations_iff
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    (let _ : ModelCategory (BasedNativePresentation.StrictCarrier (A := A)) :=
       BasedNativePresentation.strictModelCategory
     fibrations _ ((strictSourceEquivalence e).functor.map f)) ↔
    (let _ : ModelCategory C := modelCategory e
     fibrations C f) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  exact strictSourceProperty_iff e (fibrations _) f

/-- The literal original source map retains the entire strict native trivial-fibration class. -/
theorem strictSource_trivialFibrations_iff
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    (let _ : ModelCategory (BasedNativePresentation.StrictCarrier (A := A)) :=
       BasedNativePresentation.strictModelCategory
     trivialFibrations _ ((strictSourceEquivalence e).functor.map f)) ↔
    (let _ : ModelCategory C := modelCategory e
     trivialFibrations C f) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  exact strictSourceProperty_iff e (trivialFibrations _) f

/-- The literal original source map retains the entire strict native cofibration class. -/
theorem strictSource_cofibrations_iff
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    (let _ : ModelCategory (BasedNativePresentation.StrictCarrier (A := A)) :=
       BasedNativePresentation.strictModelCategory
     cofibrations _ ((strictSourceEquivalence e).functor.map f)) ↔
    (let _ : ModelCategory C := modelCategory e
     cofibrations C f) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  exact strictSourceProperty_iff e (cofibrations _) f

/-- The literal original source map retains the entire strict native trivial-cofibration class. -/
theorem strictSource_trivialCofibrations_iff
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    (let _ : ModelCategory (BasedNativePresentation.StrictCarrier (A := A)) :=
       BasedNativePresentation.strictModelCategory
     trivialCofibrations _ ((strictSourceEquivalence e).functor.map f)) ↔
    (let _ : ModelCategory C := modelCategory e
     trivialCofibrations C f) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := Native.modelCategory
  exact strictSourceProperty_iff e (trivialCofibrations _) f

/-- The actual forward original-source/strict adjunction preserves both whole left classes. -/
theorem strictSource_isQuillenAdjunction
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    let _ : ModelCategory (BasedNativePresentation.StrictCarrier (A := A)) :=
      BasedNativePresentation.strictModelCategory
    (strictSourceEquivalence e).toAdjunction.IsQuillenAdjunction := by
  let _ : ModelCategory C := modelCategory e
  let _ : ModelCategory (BasedNativePresentation.StrictCarrier (A := A)) :=
    BasedNativePresentation.strictModelCategory
  exact { preservesCofibrations := fun _ _ f h => (strictSource_cofibrations_iff e f).mpr h
          preservesTrivialCofibrations := fun _ _ f h =>
            (strictSource_trivialCofibrations_iff e f).mpr h }

/-- The actual inverse original-source/strict adjunction preserves both whole right classes. -/
theorem inverseStrictSource_isQuillenAdjunction
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    let _ : ModelCategory (BasedNativePresentation.StrictCarrier (A := A)) :=
      BasedNativePresentation.strictModelCategory
    (strictSourceEquivalence e).symm.toAdjunction.IsQuillenAdjunction := by
  let _ : ModelCategory C := modelCategory e
  let _ : ModelCategory (BasedNativePresentation.StrictCarrier (A := A)) :=
    BasedNativePresentation.strictModelCategory
  apply CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · exact fun _ _ f h => (strictSource_fibrations_iff e f).mpr h
  · exact fun _ _ f h => (strictSource_trivialFibrations_iff e f).mpr h

end HomotopicalAlgebra.EnrichedProjective.NativePresentation
