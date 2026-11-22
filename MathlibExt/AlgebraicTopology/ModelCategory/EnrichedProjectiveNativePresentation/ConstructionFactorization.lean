/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Construction
import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence

/-!
# Complete source cardinal data with the constructed original bottom

Use the exact existing native construction and the actual carrier inverse.
Both full Z/i/p/Arrow/fac packets, original generator cardinal fields and
actual counit comparisons require no incoming model, bottom or data dictionary.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory HomotopicalAlgebra MorphismProperty
open CategoryTheory.MorphismProperty.FunctorialFactorizationData
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation.Construction

attribute [local instance] Native.Construction.generatorOrderBot

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]

/-- The actual free-I cardinal data transported with the ORIGINAL carrier inverse. -/
def cofibrantFactorizationData (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
    Native.Construction.modelCategory
  change FunctorialFactorizationData
    ((cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor)
    ((trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor)
  exact (Native.Construction.cofibrantFactorizationData (A := A)).ofEquivalence e

/-- The actual free-J cardinal data transported with the ORIGINAL carrier inverse. -/
def fibrantFactorizationData (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : ModelCategory C := modelCategory e
    FunctorialFactorizationData (trivialCofibrations C) (fibrations C) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
    Native.Construction.modelCategory
  change FunctorialFactorizationData
    ((trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor)
    ((fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).inverseImage e.functor)
  exact (Native.Construction.fibrantFactorizationData (A := A)).ofEquivalence e

/-- The whole free-I middle functor retains the actual inverse and original native data. -/
theorem cofibrantFactorizationData_Z
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (cofibrantFactorizationData e).Z =
      e.functor.mapArrow ⋙ (Native.Construction.cofibrantFactorizationData (A := A)).Z ⋙
        e.inverse := rfl

/-- The whole free-J middle functor retains the actual inverse and original native data. -/
theorem fibrantFactorizationData_Z
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (fibrantFactorizationData e).Z =
      e.functor.mapArrow ⋙ (Native.Construction.fibrantFactorizationData (A := A)).Z ⋙
        e.inverse := rfl

/-- The original free-I data at exactly the supplied cardinal determines ALL source fields. -/
theorem cofibrantFactorizationData_original_fields
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : (generators (A := A)
      PointedCGWH.realizedBoundaryInclusions.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} :=
        Native.Construction.generatorsI_isCardinalForSmallObjectArgument
    let original := SmallObject.functorialFactorizationData
      (generators (A := A) PointedCGWH.realizedBoundaryInclusions.{u, v})
        realizedGeneratorCardinal.{v}
    (cofibrantFactorizationData e).Z = e.functor.mapArrow ⋙ original.Z ⋙ e.inverse ∧
      (∀ f, (cofibrantFactorizationData e).i.app f =
        e.unitIso.hom.app f.left ≫ e.inverse.map (original.i.app (e.functor.mapArrow.obj f))) ∧
      (∀ f, (cofibrantFactorizationData e).p.app f =
        e.inverse.map (original.p.app (e.functor.mapArrow.obj f)) ≫ e.unitIso.inv.app f.right) := by
  exact ⟨rfl, (fun _ => rfl), (fun _ => rfl)⟩

/-- The original free-J data at exactly the supplied cardinal determines ALL source fields. -/
theorem fibrantFactorizationData_original_fields
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    let _ : (generators (A := A)
      PointedCGWH.realizedHornInclusions.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} :=
        Native.Construction.generatorsJ_isCardinalForSmallObjectArgument
    let original := SmallObject.functorialFactorizationData
      (generators (A := A) PointedCGWH.realizedHornInclusions.{u, v}) realizedGeneratorCardinal.{v}
    (fibrantFactorizationData e).Z = e.functor.mapArrow ⋙ original.Z ⋙ e.inverse ∧
      (∀ f, (fibrantFactorizationData e).i.app f =
        e.unitIso.hom.app f.left ≫ e.inverse.map (original.i.app (e.functor.mapArrow.obj f))) ∧
      (∀ f, (fibrantFactorizationData e).p.app f =
        e.inverse.map (original.p.app (e.functor.mapArrow.obj f)) ≫ e.unitIso.inv.app f.right) := by
  exact ⟨rfl, (fun _ => rfl), (fun _ => rfl)⟩

/-- An arbitrary original commutative square retains its complete free-I middle map. -/
theorem cofibrantFactorizationData_Z_map
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {f g : CategoryTheory.Arrow C} (φ : f ⟶ g) :
    (cofibrantFactorizationData e).Z.map φ =
      e.inverse.map ((Native.Construction.cofibrantFactorizationData (A := A)).Z.map
        (e.functor.mapArrow.map φ)) := rfl

/-- An arbitrary original commutative square retains its complete free-J middle map. -/
theorem fibrantFactorizationData_Z_map
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {f g : CategoryTheory.Arrow C} (φ : f ⟶ g) :
    (fibrantFactorizationData e).Z.map φ =
      e.inverse.map ((Native.Construction.fibrantFactorizationData (A := A)).Z.map
        (e.functor.mapArrow.map φ)) := rfl

/-- The complete free-I components factor exactly the ORIGINAL caller arrow. -/
theorem cofibrantFactorizationData_fac
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (f : CategoryTheory.Arrow C) :
    (cofibrantFactorizationData e).i.app f ≫ (cofibrantFactorizationData e).p.app f = f.hom :=
  (cofibrantFactorizationData e).fac_app

/-- The complete free-J components factor exactly the ORIGINAL caller arrow. -/
theorem fibrantFactorizationData_fac
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (f : CategoryTheory.Arrow C) :
    (fibrantFactorizationData e).i.app f ≫ (fibrantFactorizationData e).p.app f = f.hom :=
  (fibrantFactorizationData e).fac_app

/-- The actual carrier counit compares the ENTIRE free-I middle functor. -/
def cofibrantFactorizationDataZComparisonIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (cofibrantFactorizationData e).Z ⋙ e.functor ≅
      e.functor.mapArrow ⋙ (Native.Construction.cofibrantFactorizationData (A := A)).Z :=
  (Native.Construction.cofibrantFactorizationData (A := A)).ofEquivalenceZComparisonIso e

/-- The actual carrier counit compares the ENTIRE free-J middle functor. -/
def fibrantFactorizationDataZComparisonIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (fibrantFactorizationData e).Z ⋙ e.functor ≅
      e.functor.mapArrow ⋙ (Native.Construction.fibrantFactorizationData (A := A)).Z :=
  (Native.Construction.fibrantFactorizationData (A := A)).ofEquivalenceZComparisonIso e

/-- The whole original free-I left component is recovered through the actual counit. -/
theorem cofibrantFactorizationData_mapped_i
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (f : CategoryTheory.Arrow C) :
    e.functor.map ((cofibrantFactorizationData e).i.app f) ≫
      (cofibrantFactorizationDataZComparisonIso e).hom.app f =
        (Native.Construction.cofibrantFactorizationData (A := A)).i.app
          (e.functor.mapArrow.obj f) :=
  (Native.Construction.cofibrantFactorizationData (A := A)).ofEquivalence_mapped_i e f

/-- The whole original free-I right component is recovered through the actual counit. -/
theorem cofibrantFactorizationData_mapped_p
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (f : CategoryTheory.Arrow C) :
    (cofibrantFactorizationDataZComparisonIso e).hom.app f ≫
      (Native.Construction.cofibrantFactorizationData (A := A)).p.app (e.functor.mapArrow.obj f) =
        e.functor.map ((cofibrantFactorizationData e).p.app f) :=
  (Native.Construction.cofibrantFactorizationData (A := A)).ofEquivalence_mapped_p e f

/-- The whole original free-J left component is recovered through the actual counit. -/
theorem fibrantFactorizationData_mapped_i
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (f : CategoryTheory.Arrow C) :
    e.functor.map ((fibrantFactorizationData e).i.app f) ≫
      (fibrantFactorizationDataZComparisonIso e).hom.app f =
        (Native.Construction.fibrantFactorizationData (A := A)).i.app (e.functor.mapArrow.obj f) :=
  (Native.Construction.fibrantFactorizationData (A := A)).ofEquivalence_mapped_i e f

/-- The whole original free-J right component is recovered through the actual counit. -/
theorem fibrantFactorizationData_mapped_p
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (f : CategoryTheory.Arrow C) :
    (fibrantFactorizationDataZComparisonIso e).hom.app f ≫
      (Native.Construction.fibrantFactorizationData (A := A)).p.app (e.functor.mapArrow.obj f) =
        e.functor.map ((fibrantFactorizationData e).p.app f) :=
  (Native.Construction.fibrantFactorizationData (A := A)).ofEquivalence_mapped_p e f

/-- The actual source free-I components lie in the two ORIGINAL model classes. -/
theorem cofibrantFactorizationData_classes
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (f : CategoryTheory.Arrow C) :
    let _ : ModelCategory C := modelCategory e
    cofibrations C ((cofibrantFactorizationData e).i.app f) ∧
      trivialFibrations C ((cofibrantFactorizationData e).p.app f) :=
  ⟨(cofibrantFactorizationData e).hi f, (cofibrantFactorizationData e).hp f⟩

/-- The actual source free-J components lie in the two ORIGINAL model classes. -/
theorem fibrantFactorizationData_classes
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (f : CategoryTheory.Arrow C) :
    let _ : ModelCategory C := modelCategory e
    trivialCofibrations C ((fibrantFactorizationData e).i.app f) ∧
      fibrations C ((fibrantFactorizationData e).p.app f) :=
  ⟨(fibrantFactorizationData e).hi f, (fibrantFactorizationData e).hp f⟩

end HomotopicalAlgebra.EnrichedProjective.NativePresentation.Construction
