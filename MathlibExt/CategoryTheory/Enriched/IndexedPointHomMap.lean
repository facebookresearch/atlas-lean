/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.WholePointHomMap

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uC vC uJ

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.UnitGeneratedEnrichment

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {J : Type uJ} [EnrichedCategory V J]

private theorem homTo_conjugation {X X' Y Y' : ForgetEnrichment V J}
    (hx : X = X') (hy : Y = Y') (f : X ⟶ Y) :
    ForgetEnrichment.homTo V ((eqToIso hx).inv ≫ f ≫ (eqToIso hy).hom) =
      ForgetEnrichment.homTo V f ≫
        eqToHom (congrArg₂
          (fun P Q : ForgetEnrichment V J =>
            (ForgetEnrichment.to V P ⟶[V] ForgetEnrichment.to V Q)) hx hy) := by
  cases hx
  cases hy
  simp only [eqToIso_refl, Iso.refl_inv, Iso.refl_hom, Category.id_comp,
    Category.comp_id, eqToHom_refl]

variable {C : Type uC} [Category.{vC} C]

private def copiedFunctor (F : C ⥤ ForgetEnrichment V J) (index : C → J)
    (hobj : ∀ X, F.obj X = ForgetEnrichment.of V (index X)) :
    C ⥤ ForgetEnrichment V J where
  obj X := ForgetEnrichment.of V (index X)
  map {X Y} f := (eqToIso (hobj X)).inv ≫ F.map f ≫ (eqToIso (hobj Y)).hom
  map_id X := by
    rw [F.map_id, Category.id_comp]
    exact Iso.inv_hom_id (eqToIso (hobj X))
  map_comp f g := by
    rw [F.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem copied_point_function (F : C ⥤ ForgetEnrichment V J) (index : C → J)
    (hobj : ∀ X, F.obj X = ForgetEnrichment.of V (index X)) (X Y : C) :
    (fun f : X ⟶ Y =>
      ForgetEnrichment.homTo V ((copiedFunctor F index hobj).map f)) =
        (fun f : X ⟶ Y => ForgetEnrichment.homTo V (F.map f) ≫
          eqToHom (congrArg₂
            (fun P Q : ForgetEnrichment V J =>
              (ForgetEnrichment.to V P ⟶[V] ForgetEnrichment.to V Q))
                (hobj X) (hobj Y))) := by
  funext f
  exact homTo_conjugation (hobj X) (hobj Y) (F.map f)

variable [EnrichedOrdinaryCategory V C]

/-- The entire original indexed Hom map preserves identity through the actual functor data. -/
theorem map_id_of_index_point_function (F : C ⥤ ForgetEnrichment V J) (index : C → J)
    (hobj : ∀ X, F.obj X = ForgetEnrichment.of V (index X))
    (m : ∀ X Y : C, (X ⟶[V] Y) ⟶ (index X ⟶[V] index Y))
    (hp : ∀ X Y : C,
      (fun f : X ⟶ Y => eHomEquiv V f ≫ m X Y) =
        (fun f : X ⟶ Y => ForgetEnrichment.homTo V (F.map f) ≫
          eqToHom (congrArg₂
            (fun P Q : ForgetEnrichment V J =>
              (ForgetEnrichment.to V P ⟶[V] ForgetEnrichment.to V Q))
                (hobj X) (hobj Y)))) (X : C) :
    eId V X ≫ m X X = eId V (index X) := by
  let G := copiedFunctor F index hobj
  have hG : ∀ X Y : C,
      (fun f : X ⟶ Y => eHomEquiv V f ≫ m X Y) =
        (fun f : X ⟶ Y => ForgetEnrichment.homTo V (G.map f)) := by
    intro X Y
    exact (hp X Y).trans (copied_point_function F index hobj X Y).symm
  exact map_id_of_point_function G m hG X

variable [MonoidalClosed V]

/-- Both entire indexed Hom factors preserve composition through the original functor laws. -/
theorem map_comp_of_index_point_function (F : C ⥤ ForgetEnrichment V J) (index : C → J)
    (hobj : ∀ X, F.obj X = ForgetEnrichment.of V (index X))
    (hsep : IsSeparator (𝟙_ V))
    (m : ∀ X Y : C, (X ⟶[V] Y) ⟶ (index X ⟶[V] index Y))
    (hp : ∀ X Y : C,
      (fun f : X ⟶ Y => eHomEquiv V f ≫ m X Y) =
        (fun f : X ⟶ Y => ForgetEnrichment.homTo V (F.map f) ≫
          eqToHom (congrArg₂
            (fun P Q : ForgetEnrichment V J =>
              (ForgetEnrichment.to V P ⟶[V] ForgetEnrichment.to V Q))
                (hobj X) (hobj Y)))) (X Y Z : C) :
    eComp V X Y Z ≫ m X Z =
      (m X Y ⊗ₘ m Y Z) ≫ eComp V (index X) (index Y) (index Z) := by
  let G := copiedFunctor F index hobj
  have hG : ∀ X Y : C,
      (fun f : X ⟶ Y => eHomEquiv V f ≫ m X Y) =
        (fun f : X ⟶ Y => ForgetEnrichment.homTo V (G.map f)) := by
    intro X Y
    exact (hp X Y).trans (copied_point_function F index hobj X Y).symm
  exact map_comp_of_point_function G hsep m hG X Y Z

end CategoryTheory.UnitGeneratedEnrichment
