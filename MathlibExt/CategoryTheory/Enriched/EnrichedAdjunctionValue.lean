/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.EnrichedAdjunctionFull
public import MathlibExt.CategoryTheory.Monoidal.Closed.UnitEvaluation

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uC vC

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedAdjunctionHom.UnitValue

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]

/-- Canonical unit evaluation retains every actual ordinary point of the value object. -/
theorem unitIsoSelf_point {Y : V} (f : 𝟙_ V ⟶ Y) :
    eHomEquiv V f ≫ (MonoidalClosed.unitIsoSelf (X := Y)).hom = f := by
  have h : eHomEquiv V f = f ≫ MonoidalClosed.unitNatIso.hom.app Y := by
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv]
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.curry', MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_natural_left, unitNatIso_hom_uncurry,
      leftUnitor_naturality, unitors_equal]
  change eHomEquiv V f ≫ MonoidalClosed.unitNatIso.inv.app Y = f
  apply (cancel_mono (MonoidalClosed.unitNatIso.hom.app Y)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact (Category.comp_id (eHomEquiv V f)).trans h

/-- The canonical closed-unit inverse retains every actual ordinary value point. -/
theorem unitIsoSelf_inv_point {Y : V} (f : 𝟙_ V ⟶ Y) :
    f ≫ (MonoidalClosed.unitIsoSelf (X := Y)).inv = eHomEquiv V f := by
  apply (cancel_mono (MonoidalClosed.unitIsoSelf (X := Y)).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, unitIsoSelf_point]

/-- The complete canonical unit map is natural on the entire internal Hom object. -/
@[reassoc]
theorem unitIsoSelf_naturality {X Y : V} (f : X ⟶ Y) :
    (ihom (𝟙_ V)).map f ≫ (MonoidalClosed.unitIsoSelf (X := Y)).hom =
      (MonoidalClosed.unitIsoSelf (X := X)).hom ≫ f := by
  exact MonoidalClosed.unitNatIso.inv.naturality f

variable {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]
  {L : V ⥤ C} {R : C ⥤ V} (d : EnrichedAdjunctionHom.Data L R) (adj : L ⊣ R)

/-- The entire adjunction value map retains the actual original ordinary adjunct. -/
theorem valueIso_point (hsep : IsSeparator (𝟙_ V)) (M : C) (f : L.obj (𝟙_ V) ⟶ M) :
    eHomEquiv V f ≫ (Full.valueIso d adj hsep M).hom = adj.homEquiv (𝟙_ V) M f := by
  rw [Full.valueIso_hom, ← Category.assoc, Full.forward_point, unitIsoSelf_point]

/-- The entire adjunction value inverse retains the actual original inverse adjunct. -/
theorem valueIso_inv_point (hsep : IsSeparator (𝟙_ V)) (M : C) (f : 𝟙_ V ⟶ R.obj M) :
    f ≫ (Full.valueIso d adj hsep M).inv =
      eHomEquiv V ((adj.homEquiv (𝟙_ V) M).symm f) := by
  rw [Full.valueIso_inv, ← Category.assoc, unitIsoSelf_inv_point, Full.inverse_point]

/-- Whole Hom-object target naturality agrees with the original ordinary adjunction. -/
theorem target_naturality (hsep : IsSeparator (𝟙_ V)) (X : V) {M N : C} (g : M ⟶ N) :
    eHomWhiskerLeft V (L.obj X) g ≫ Full.forward d adj X N =
      Full.forward d adj X M ≫ eHomWhiskerLeft V X (R.map g) := by
  apply hsep.def
  intro p
  let f : L.obj X ⟶ M := (eHomEquiv V).symm p
  have hp : eHomEquiv V f = p := (eHomEquiv V).apply_symm_apply p
  rw [← hp]
  calc
    eHomEquiv V f ≫ eHomWhiskerLeft V (L.obj X) g ≫ Full.forward d adj X N =
        (eHomEquiv V f ≫ eHomWhiskerLeft V (L.obj X) g) ≫ Full.forward d adj X N :=
      (Category.assoc _ _ _).symm
    _ = eHomEquiv V (f ≫ g) ≫ Full.forward d adj X N :=
      congrArg (fun z => z ≫ Full.forward d adj X N)
        (eHomEquiv_comp_eHomWhiskerLeft V C f g)
    _ = eHomEquiv V (adj.homEquiv X N (f ≫ g)) := Full.forward_point d adj X N (f ≫ g)
    _ = eHomEquiv V (adj.homEquiv X M f ≫ R.map g) :=
      congrArg (eHomEquiv V) (adj.homEquiv_naturality_right f g)
    _ = eHomEquiv V (adj.homEquiv X M f) ≫ eHomWhiskerLeft V X (R.map g) :=
      (eHomEquiv_comp_eHomWhiskerLeft V V (adj.homEquiv X M f) (R.map g)).symm
    _ = (eHomEquiv V f ≫ Full.forward d adj X M) ≫ eHomWhiskerLeft V X (R.map g) :=
      congrArg (fun z => z ≫ eHomWhiskerLeft V X (R.map g))
        (Full.forward_point d adj X M f).symm
    _ = eHomEquiv V f ≫ Full.forward d adj X M ≫ eHomWhiskerLeft V X (R.map g) :=
      Category.assoc _ _ _

/-- The complete original value isomorphism is natural on every original target map. -/
theorem valueIso_naturality (hsep : IsSeparator (𝟙_ V)) {M N : C} (g : M ⟶ N) :
    eHomWhiskerLeft V (L.obj (𝟙_ V)) g ≫ (Full.valueIso d adj hsep N).hom =
      (Full.valueIso d adj hsep M).hom ≫ R.map g := by
  rw [Full.valueIso_hom, Full.valueIso_hom]
  rw [← Category.assoc, target_naturality d adj hsep (𝟙_ V) g]
  rw [Category.assoc, MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    unitIsoSelf_naturality]
  exact (Category.assoc _ _ _).symm

/-- A genuine natural Hom-object isomorphism at every original source object. -/
@[no_expose]
def homNatIso (hsep : IsSeparator (𝟙_ V)) (X : V) :
    eCoyoneda V (L.obj X) ≅ R ⋙ ihom X :=
  NatIso.ofComponents (Full.homIso d adj hsep X) (by
    intro M N g
    rw [Full.homIso_hom, Full.homIso_hom]
    change eHomWhiskerLeft V (L.obj X) g ≫ Full.forward d adj X N =
      Full.forward d adj X M ≫ (ihom X).map (R.map g)
    rw [← MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
    exact target_naturality d adj hsep X g)

/-- Genuine natural original free/evaluation identification of entire mapping objects. -/
@[no_expose]
def valueNatIso (hsep : IsSeparator (𝟙_ V)) : eCoyoneda V (L.obj (𝟙_ V)) ≅ R :=
  NatIso.ofComponents (Full.valueIso d adj hsep) (by
    intro M N g
    exact valueIso_naturality d adj hsep g)

/-- The whole natural Hom isomorphism retains its original forward component. -/
theorem homNatIso_hom_app (hsep : IsSeparator (𝟙_ V)) (X : V) (M : C) :
    HEq ((homNatIso d adj hsep X).hom.app M) (Full.forward d adj X M) := by
  exact heq_of_eq (Full.homIso_hom d adj hsep X M)

/-- The whole natural value isomorphism retains its original value component. -/
theorem valueNatIso_hom_app (hsep : IsSeparator (𝟙_ V)) (M : C) :
    HEq ((valueNatIso d adj hsep).hom.app M) ((Full.valueIso d adj hsep M).hom) := by rfl

end CategoryTheory.EnrichedAdjunctionHom.UnitValue
