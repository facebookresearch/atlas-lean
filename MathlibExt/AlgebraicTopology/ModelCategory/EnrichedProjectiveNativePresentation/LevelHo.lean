/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ReplacementHo
import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Actual original-presentation and native level homotopy categories

The source model is the already constructed transport of the actual native
model through the given complete carrier equivalence. Both strict projection
functors are the original localization constructions. The actual original
unit and counit lift with their full naturality and triangle identities.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v uC vC

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
variable {C : Type uC} [CategoryTheory.Category.{vC} C]

attribute [local instance] Native.modelCategory

/-- The actual original-presentation level homotopy category. -/
abbrev HoCategory (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  (NativePresentation.weakProperty e).Localization

/-- The literal original localization projection for the constructed source model. -/
abbrev projection (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) : C ⥤ HoCategory e :=
  (NativePresentation.weakProperty e).Q

theorem category_eq_model (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    HoCategory e = HomotopyCategory C := rfl

theorem projection_eq_model (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    projection e = toHomotopyCategory C := rfl

/-- The original forward carrier functor followed by the native projection inverts the actual source
weak class. -/
theorem forward_inverts (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (NativePresentation.weakProperty e).IsInvertedBy
      (e.functor ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) :=
  fun _ _ f hf => Localization.inverts
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)) (e.functor.map f) hf

/-- The actual original inverse also preserves the exact source weak class, by its actual counit. -/
theorem inverse_map_weak (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f) :
    NativePresentation.weakProperty e (e.inverse.map f) := by
  change weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)
    (e.functor.map (e.inverse.map f))
  let iso : CategoryTheory.Arrow.mk (e.functor.map (e.inverse.map f)) ≅ CategoryTheory.Arrow.mk f :=
    CategoryTheory.Arrow.isoMk (e.counitIso.app X) (e.counitIso.app Y)
      (e.counitIso.hom.naturality f).symm
  exact ((weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).arrow_mk_iso_iff iso).2 hf

theorem inverse_inverts (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)).IsInvertedBy
      (e.inverse ⋙ projection e) :=
  fun _ _ f hf => Localization.inverts (projection e) (NativePresentation.weakProperty e)
    (e.inverse.map f) (inverse_map_weak e f hf)

/-- The actual source-to-native action on the already constructed level homotopy categories. -/
def forward (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    HoCategory e ⥤ HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Localization.Construction.lift
    (e.functor ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) (forward_inverts e)

/-- The actual native-to-source action uses exactly the original given carrier inverse. -/
def inverse (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⥤ HoCategory e :=
  Localization.Construction.lift (e.inverse ⋙ projection e) (inverse_inverts e)

theorem forward_projection (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    projection e ⋙ forward e =
      e.functor ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Localization.Construction.fac _ _

theorem inverse_projection (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ inverse e =
      e.inverse ⋙ projection e := Localization.Construction.fac _ _

theorem forward_map_projected (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : C} (f : X ⟶ Y) :
    (forward e).map ((projection e).map f) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map (e.functor.map f) :=
  Functor.congr_hom (forward_projection e) f

theorem inverse_map_projected (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    (inverse e).map ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map f) =
      (projection e).map (e.inverse.map f) :=
  Functor.congr_hom (inverse_projection e) f
/-- The localization lift of the original carrier functor with its strict projection equality. -/
@[instance_reducible]
def forwardLifting (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    Localization.Lifting (projection e) (NativePresentation.weakProperty e)
      (e.functor ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) (forward e) :=
  ⟨eqToIso (forward_projection e)⟩
/-- The localization lift of the given carrier inverse with its strict projection equality. -/
@[instance_reducible]
def inverseLifting (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    Localization.Lifting (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)) (e.inverse ⋙ projection e)
        (inverse e) :=
  ⟨eqToIso (inverse_projection e)⟩

theorem forward_inverse_projection (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    projection e ⋙ (forward e ⋙ inverse e) = (e.functor ⋙ e.inverse) ⋙ projection e := by
  calc
    projection e ⋙ (forward e ⋙ inverse e) = (projection e ⋙ forward e) ⋙ inverse e := rfl
    _ = (e.functor ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) ⋙ inverse e := by
      rw [forward_projection]
    _ = e.functor ⋙ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ inverse e) :=
      rfl
    _ = e.functor ⋙ (e.inverse ⋙ projection e) := by rw [inverse_projection]
    _ = (e.functor ⋙ e.inverse) ⋙ projection e := rfl

theorem inverse_forward_projection (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ (inverse e ⋙ forward e) =
      (e.inverse ⋙ e.functor) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) := by
  calc
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ (inverse e ⋙ forward e) =
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ⋙ inverse e) ⋙ forward e :=
          rfl
    _ = (e.inverse ⋙ projection e) ⋙ forward e := by rw [inverse_projection]
    _ = e.inverse ⋙ (projection e ⋙ forward e) := rfl
    _ = e.inverse ⋙ (e.functor ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) := by
      rw [forward_projection]
    _ = (e.inverse ⋙ e.functor) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
      rfl
/-- The lift of the original forward/inverse composite before applying the given unit. -/
@[instance_reducible]
def forwardInverseLifting (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    Localization.Lifting (projection e) (NativePresentation.weakProperty e)
      ((e.functor ⋙ e.inverse) ⋙ projection e) (forward e ⋙ inverse e) :=
  ⟨eqToIso (forward_inverse_projection e)⟩
/-- The lift of the original inverse/forward composite before applying the given counit. -/
@[instance_reducible]
def inverseForwardLifting (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    Localization.Lifting (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
      ((e.inverse ⋙ e.functor) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
      (inverse e ⋙ forward e) := ⟨eqToIso (inverse_forward_projection e)⟩

/-- The actual original carrier unit lifts to the whole source level Ho category. -/
def unitIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    𝟭 (HoCategory e) ≅ forward e ⋙ inverse e := by
  let _ := forwardInverseLifting e
  exact Localization.liftNatIso (projection e) (NativePresentation.weakProperty e)
    (projection e) ((e.functor ⋙ e.inverse) ⋙ projection e) (𝟭 (HoCategory e))
    (forward e ⋙ inverse e) (Functor.isoWhiskerRight e.unitIso (projection e))

/-- The actual original carrier counit lifts to the whole native level Ho category. -/
def counitIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    inverse e ⋙ forward e ≅ 𝟭 (HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) := by
  let _ := inverseForwardLifting e
  exact Localization.liftNatIso (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A))
    ((e.inverse ⋙ e.functor) ⋙ toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A))
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)) (inverse e ⋙ forward e)
    (𝟭 (HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)))
    (Functor.isoWhiskerRight e.counitIso (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      A)))

theorem unitIso_hom_projected (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (unitIso e).hom.app ((projection e).obj X) = (projection e).map (e.unitIso.hom.app X) := by
  rw [unitIso]
  simp only [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (𝟙 ((projection e).obj X) ≫ (projection e).map (e.unitIso.hom.app X)) ≫
      𝟙 ((projection e).obj (e.inverse.obj (e.functor.obj X))) = _
  exact (congrArg
    (fun f => f ≫ 𝟙 ((projection e).obj (e.inverse.obj (e.functor.obj X))))
    (Category.id_comp ((projection e).map (e.unitIso.hom.app X)))).trans
      (Category.comp_id ((projection e).map (e.unitIso.hom.app X)))

theorem counitIso_hom_projected (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (counitIso e).hom.app
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj X) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map (e.counitIso.hom.app X) :=
        by
  rw [counitIso]
  simp only [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (𝟙 ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj
        (e.functor.obj (e.inverse.obj X))) ≫
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map (e.counitIso.hom.app X)) ≫
      𝟙 ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj X) = _
  exact (congrArg
    (fun f => f ≫ 𝟙 ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj X))
    (Category.id_comp
      ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        (e.counitIso.hom.app X)))).trans
    (Category.comp_id
      ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        (e.counitIso.hom.app X)))

theorem unitIso_naturality (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : HoCategory e} (f : X ⟶ Y) :
    f ≫ (unitIso e).hom.app Y =
      (unitIso e).hom.app X ≫ (forward e ⋙ inverse e).map f :=
  (unitIso e).hom.naturality f

theorem counitIso_naturality (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {X Y : HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)} (f : X ⟶ Y) :
    (inverse e ⋙ forward e).map f ≫ (counitIso e).hom.app Y = (counitIso e).hom.app X ≫ f :=
  (counitIso e).hom.naturality f

theorem forward_unit_counit (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    Functor.whiskerRight (unitIso e).hom (forward e) ≫
      Functor.whiskerLeft (forward e) (counitIso e).hom = 𝟙 (forward e) := by
  apply Localization.natTrans_ext (projection e) (NativePresentation.weakProperty e)
  intro X
  change (forward e).map ((unitIso e).hom.app ((projection e).obj X)) ≫
      (counitIso e).hom.app ((forward e).obj ((projection e).obj X)) =
      𝟙 ((forward e).obj ((projection e).obj X))
  change (forward e).map ((unitIso e).hom.app ((projection e).obj X)) ≫
      (counitIso e).hom.app
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj (e.functor.obj X)) =
      𝟙 ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj (e.functor.obj X))
  rw [unitIso_hom_projected, forward_map_projected]
  change (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        (e.functor.map (e.unitIso.hom.app X)) ≫
      (counitIso e).hom.app
        ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj (e.functor.obj X)) =
      𝟙 ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj (e.functor.obj X))
  rw [counitIso_hom_projected e (e.functor.obj X),
    ← (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map_comp,
    e.functor_unitIso_comp X]
  exact (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map_id (e.functor.obj X)

/-- The complete actual original-presentation/native level Ho equivalence, retaining its actual unit
and counit. -/
def equivalence (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    HoCategory e ≌ HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) where
  functor := forward e
  inverse := inverse e
  unitIso := unitIso e
  counitIso := counitIso e
  functor_unitIso_comp X := congr_app (forward_unit_counit e) X

theorem equivalence_functor (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (equivalence e).functor = forward e := rfl

theorem equivalence_inverse (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (equivalence e).inverse = inverse e := rfl

theorem equivalence_unitIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (equivalence e).unitIso = unitIso e := rfl

theorem equivalence_counitIso (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (equivalence e).counitIso = counitIso e := rfl

end HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo
