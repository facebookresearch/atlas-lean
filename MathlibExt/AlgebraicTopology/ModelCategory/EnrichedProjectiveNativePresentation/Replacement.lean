/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Zero
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Factorization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.BifibrantReplacement

/-!
# Original presentation replacements from the same transported cardinal data

The original given carrier inverse transports the actual native I/J data.
The source zero-arrow functors retain the actual counit comparisons, so the
whole source replacements and all four original natural arrows compare with
the native replacements without choosing a different factorization.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
variable {C : Type uC} [Category.{vC} C]

attribute [local instance] Native.modelCategory

/-- Use the actual original source I middle functor on the actual full source zero arrow. -/
def cofibrantReplacement (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : C ⥤ C :=
  Zero.fromZeroArrow e ⋙ (NativePresentation.cofibrantFactorizationData e).Z

/-- Use the same original source J middle functor on the actual source arrow to zero. -/
def fibrantReplacement (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : C ⥤ C :=
  Zero.toZeroArrow e ⋙ (NativePresentation.fibrantFactorizationData e).Z

/-- The first map of the original I factorization of the source zero arrow. -/
def initialToCofibrantReplacement (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (Functor.const C).obj (Zero.object e) ⟶ cofibrantReplacement e :=
  Functor.whiskerLeft (Zero.fromZeroArrow e) (NativePresentation.cofibrantFactorizationData e).i

/-- The second map of the original I factorization as the whole source projection. -/
def cofibrantReplacementCounit (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantReplacement e ⟶ 𝟭 C :=
  Functor.whiskerLeft (Zero.fromZeroArrow e) (NativePresentation.cofibrantFactorizationData e).p

/-- The first map of the original J factorization as the whole source replacement unit. -/
def fibrantReplacementUnit (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    𝟭 C ⟶ fibrantReplacement e :=
  Functor.whiskerLeft (Zero.toZeroArrow e) (NativePresentation.fibrantFactorizationData e).i

/-- The second map of the original J factorization of the arrow to the source zero. -/
def fibrantReplacementToZero (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantReplacement e ⟶ (Functor.const C).obj (Zero.object e) :=
  Functor.whiskerLeft (Zero.toZeroArrow e) (NativePresentation.fibrantFactorizationData e).p

/-- The entire source I middle functor literally retains the actual given inverse and native data.
-/
theorem cofibrantReplacement_original_functor (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantReplacement e = Zero.fromZeroArrow e ⋙ e.functor.mapArrow ⋙
      (Native.cofibrantFactorizationData (B := B) (A := A)).Z ⋙ e.inverse := rfl

/-- The entire source J middle functor retains that same original given inverse and data. -/
theorem fibrantReplacement_original_functor (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantReplacement e = Zero.toZeroArrow e ⋙ e.functor.mapArrow ⋙
      (Native.fibrantFactorizationData (B := B) (A := A)).Z ⋙ e.inverse := rfl

/-- An arbitrary source map retains the whole original I Arrow map, not only its object. -/
theorem cofibrantReplacement_original_map (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : C} (f : X ⟶ Y) :
    (cofibrantReplacement e).map f =
      e.inverse.map ((Native.cofibrantFactorizationData (B := B) (A := A)).Z.map
        (e.functor.mapArrow.map ((Zero.fromZeroArrow e).map f))) := rfl

/-- The complete original J Arrow map is retained for every actual source map. -/
theorem fibrantReplacement_original_map (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : C} (f : X ⟶ Y) :
    (fibrantReplacement e).map f =
      e.inverse.map ((Native.fibrantFactorizationData (B := B) (A := A)).Z.map
        (e.functor.mapArrow.map ((Zero.toZeroArrow e).map f))) := rfl

theorem cofibrantReplacement_fac (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (initialToCofibrantReplacement e).app X ≫ (cofibrantReplacementCounit e).app X =
      Zero.toObject e X :=
  (NativePresentation.cofibrantFactorizationData e).fac_app

theorem fibrantReplacement_fac (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantReplacementUnit e).app X ≫ (fibrantReplacementToZero e).app X =
      Zero.fromObject e X :=
  (NativePresentation.fibrantFactorizationData e).fac_app

/-- The actual whole original carrier counit and zero-arrow comparison join source Q to native Q. -/
def cofibrantReplacementComparisonIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantReplacement e ⋙ e.functor ≅ e.functor ⋙ Native.Replacement.cofibrantReplacement :=
  Functor.isoWhiskerLeft (Zero.fromZeroArrow e)
      (NativePresentation.cofibrantFactorizationDataZComparisonIso e) ≪≫
    Functor.isoWhiskerRight (Zero.fromZeroArrowIso e) (Native.cofibrantFactorizationData (A := A)).Z

/-- The same actual two counit comparisons join the whole source R to native R. -/
def fibrantReplacementComparisonIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantReplacement e ⋙ e.functor ≅ e.functor ⋙ Native.Replacement.fibrantReplacement :=
  Functor.isoWhiskerLeft (Zero.toZeroArrow e)
      (NativePresentation.fibrantFactorizationDataZComparisonIso e) ≪≫
    Functor.isoWhiskerRight (Zero.toZeroArrowIso e) (Native.fibrantFactorizationData (A := A)).Z

/-- The complete source original I second map is recovered through those exact comparisons. -/
theorem cofibrantReplacementComparisonIso_p (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (X : C) :
    (cofibrantReplacementComparisonIso e).hom.app X ≫
      Native.Replacement.cofibrantReplacementCounit.app (e.functor.obj X) =
        e.functor.map ((cofibrantReplacementCounit e).app X) := by
  change ((NativePresentation.cofibrantFactorizationDataZComparisonIso e).hom.app
      ((Zero.fromZeroArrow e).obj X) ≫ (Native.cofibrantFactorizationData (A := A)).Z.map
        ((Zero.fromZeroArrowObjIso e X).hom)) ≫
      (Native.cofibrantFactorizationData (A := A)).p.app
        (Native.Diagrams.fromZeroArrow.obj (e.functor.obj X)) = _
  have h := (Native.cofibrantFactorizationData (A := A)).p.naturality
    (Zero.fromZeroArrowObjIso e X).hom
  change (Native.cofibrantFactorizationData (A := A)).Z.map ((Zero.fromZeroArrowObjIso e X).hom) ≫
      (Native.cofibrantFactorizationData (A := A)).p.app
        (Native.Diagrams.fromZeroArrow.obj (e.functor.obj X)) =
      (Native.cofibrantFactorizationData (A := A)).p.app
        (e.functor.mapArrow.obj ((Zero.fromZeroArrow e).obj X)) ≫ 𝟙 (e.functor.obj X) at h
  have hp :
      (Native.cofibrantFactorizationData (A := A)).Z.map ((Zero.fromZeroArrowObjIso e X).hom) ≫
        (Native.cofibrantFactorizationData (A := A)).p.app
          (Native.Diagrams.fromZeroArrow.obj (e.functor.obj X)) =
      (Native.cofibrantFactorizationData (A := A)).p.app
        (e.functor.mapArrow.obj ((Zero.fromZeroArrow e).obj X)) :=
    h.trans (Category.comp_id _)
  calc
    ((NativePresentation.cofibrantFactorizationDataZComparisonIso e).hom.app
        ((Zero.fromZeroArrow e).obj X) ≫ (Native.cofibrantFactorizationData (A := A)).Z.map
          ((Zero.fromZeroArrowObjIso e X).hom)) ≫
        (Native.cofibrantFactorizationData (A := A)).p.app
          (Native.Diagrams.fromZeroArrow.obj (e.functor.obj X)) =
      (NativePresentation.cofibrantFactorizationDataZComparisonIso e).hom.app
          ((Zero.fromZeroArrow e).obj X) ≫
        ((Native.cofibrantFactorizationData (A := A)).Z.map ((Zero.fromZeroArrowObjIso e X).hom) ≫
          (Native.cofibrantFactorizationData (A := A)).p.app
            (Native.Diagrams.fromZeroArrow.obj (e.functor.obj X))) := Category.assoc _ _ _
    _ = (NativePresentation.cofibrantFactorizationDataZComparisonIso e).hom.app
          ((Zero.fromZeroArrow e).obj X) ≫
        (Native.cofibrantFactorizationData (A := A)).p.app
          (e.functor.mapArrow.obj ((Zero.fromZeroArrow e).obj X)) :=
      congrArg (fun f => (NativePresentation.cofibrantFactorizationDataZComparisonIso e).hom.app
        ((Zero.fromZeroArrow e).obj X) ≫ f) hp
    _ = e.functor.map ((NativePresentation.cofibrantFactorizationData e).p.app
        ((Zero.fromZeroArrow e).obj X)) := NativePresentation.cofibrantFactorizationData_mapped_p e
          _

/-- The complete source original J first map is recovered through the same original comparisons. -/
theorem fibrantReplacementComparisonIso_i (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (X : C) :
    e.functor.map ((fibrantReplacementUnit e).app X) ≫
      (fibrantReplacementComparisonIso e).hom.app X =
        Native.Replacement.fibrantReplacementUnit.app (e.functor.obj X) := by
  change e.functor.map ((NativePresentation.fibrantFactorizationData e).i.app
      ((Zero.toZeroArrow e).obj X)) ≫
    ((NativePresentation.fibrantFactorizationDataZComparisonIso e).hom.app
      ((Zero.toZeroArrow e).obj X) ≫ (Native.fibrantFactorizationData (A := A)).Z.map
        ((Zero.toZeroArrowObjIso e X).hom)) = _
  rw [← Category.assoc, NativePresentation.fibrantFactorizationData_mapped_i]
  have h := (Native.fibrantFactorizationData (A := A)).i.naturality
    (Zero.toZeroArrowObjIso e X).hom
  change 𝟙 (e.functor.obj X) ≫ (Native.fibrantFactorizationData (A := A)).i.app
      (Native.Diagrams.toZeroArrow.obj (e.functor.obj X)) =
    (Native.fibrantFactorizationData (A := A)).i.app
      (e.functor.mapArrow.obj ((Zero.toZeroArrow e).obj X)) ≫
        (Native.fibrantFactorizationData (A := A)).Z.map ((Zero.toZeroArrowObjIso e X).hom) at h
  exact h.symm.trans (Category.id_comp _)

theorem cofibrantReplacementCounit_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    (cofibrantReplacement e).map f ≫ (cofibrantReplacementCounit e).app Y =
      (cofibrantReplacementCounit e).app X ≫ f :=
  (cofibrantReplacementCounit e).naturality f

theorem fibrantReplacementUnit_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    f ≫ (fibrantReplacementUnit e).app Y =
      (fibrantReplacementUnit e).app X ≫ (fibrantReplacement e).map f :=
  (fibrantReplacementUnit e).naturality f

theorem cofibrantReplacement_classes (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    cofibrations C ((initialToCofibrantReplacement e).app X) ∧
      trivialFibrations C ((cofibrantReplacementCounit e).app X) :=
  ⟨(NativePresentation.cofibrantFactorizationData e).hi _,
    (NativePresentation.cofibrantFactorizationData e).hp _⟩

theorem fibrantReplacement_classes (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    trivialCofibrations C ((fibrantReplacementUnit e).app X) ∧
      fibrations C ((fibrantReplacementToZero e).app X) :=
  ⟨(NativePresentation.fibrantFactorizationData e).hi _,
    (NativePresentation.fibrantFactorizationData e).hp _⟩

theorem isCofibrant_cofibrantReplacement
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    IsCofibrant ((cofibrantReplacement e).obj X) := by
  let _ : ModelCategory C := NativePresentation.modelCategory e
  rw [isCofibrant_iff_of_isInitial ((initialToCofibrantReplacement e).app X) (Zero.isInitial e)]
  exact (cofibration_iff _).2 (cofibrantReplacement_classes e X).1

theorem isFibrant_fibrantReplacement
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    IsFibrant ((fibrantReplacement e).obj X) := by
  let _ : ModelCategory C := NativePresentation.modelCategory e
  rw [isFibrant_iff_of_isTerminal ((fibrantReplacementToZero e).app X) (Zero.isTerminal e)]
  exact (fibration_iff _).2 (fibrantReplacement_classes e X).2

/-- Apply the same original source I and J data in the first bifibrant order. -/
def cofibrantFibrantReplacement (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : C ⥤ C :=
  cofibrantReplacement e ⋙ fibrantReplacement e

/-- Apply those same original source data in the reverse bifibrant order. -/
def fibrantCofibrantReplacement (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : C ⥤ C :=
  fibrantReplacement e ⋙ cofibrantReplacement e

/-- Compare Q followed by R using the original I/J comparisons and the given carrier counit. -/
def cofibrantFibrantReplacementComparisonIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantFibrantReplacement e ⋙ e.functor ≅ e.functor ⋙
      Native.Replacement.cofibrantFibrantReplacement :=
  Functor.isoWhiskerLeft (cofibrantReplacement e) (fibrantReplacementComparisonIso e) ≪≫
    Functor.isoWhiskerRight (cofibrantReplacementComparisonIso e)
      Native.Replacement.fibrantReplacement

/-- Compare R followed by Q using the original J/I comparisons and the given carrier counit. -/
def fibrantCofibrantReplacementComparisonIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantCofibrantReplacement e ⋙ e.functor ≅ e.functor ⋙
      Native.Replacement.fibrantCofibrantReplacement :=
  Functor.isoWhiskerLeft (fibrantReplacement e) (cofibrantReplacementComparisonIso e) ≪≫
    Functor.isoWhiskerRight (fibrantReplacementComparisonIso e)
      Native.Replacement.cofibrantReplacement

end HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement
