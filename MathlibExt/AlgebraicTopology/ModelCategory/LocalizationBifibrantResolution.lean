/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
import Mathlib.CategoryTheory.HomCongr

/-!
# Actual bifibrant resolutions of localization morphisms

The model factorization axioms supply a fibrant resolution and then a
cofibrant resolution of that fibrant object. Both original weak arrows
are retained. The fundamental lemma identifies the full left and right
homotopy quotients with morphisms of the given localization. The actual
bifibrant quotient retains every representative, inverse Hom function,
composition, source action and target action.
-/

set_option autoImplicit false
noncomputable section
universe u v u' v'

open CategoryTheory

namespace HomotopicalAlgebra.LocalizationBifibrantResolution

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The object is the actual chosen fibrant resolution from model factorization. -/
def fibrantObj (X : C) : C := FibrantObject.HoCat.resolutionObj X

/-- The map is the original trivial cofibration to that same chosen fibrant resolution. -/
def iFibrant (X : C) : X ⟶ fibrantObj X := FibrantObject.HoCat.iResolutionObj X

/-- The original chosen fibrant resolution is fibrant in the given model category. -/
instance fibrantObj_isFibrant (X : C) : IsFibrant (fibrantObj X) := by
  unfold fibrantObj
  infer_instance

/-- The original resolution arrow is a cofibration in the given model category. -/
instance iFibrant_cofibration (X : C) : Cofibration (iFibrant X) := by
  exact (FibrantObject.HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.1

/-- The original resolution arrow is a weak equivalence in the given model category. -/
instance iFibrant_weakEquivalence (X : C) : WeakEquivalence (iFibrant X) := by
  exact (FibrantObject.HoCat.exists_resolution X).choose_spec.choose_spec.choose_spec.2

/-- The object is the actual cofibrant resolution of the same chosen fibrant resolution. -/
def bifibrantObj (X : C) : C := CofibrantObject.HoCat.resolutionObj (fibrantObj X)

/-- The map is the original trivial fibration to the same chosen fibrant resolution. -/
def pBifibrant (X : C) : bifibrantObj X ⟶ fibrantObj X :=
  CofibrantObject.HoCat.pResolutionObj (fibrantObj X)

/-- The second original resolution is cofibrant in the given model category. -/
instance bifibrantObj_isCofibrant (X : C) : IsCofibrant (bifibrantObj X) := by
  unfold bifibrantObj
  infer_instance

/-- The second original resolution is fibrant because its original projection is a fibration. -/
instance bifibrantObj_isFibrant (X : C) : IsFibrant (bifibrantObj X) := by
  unfold bifibrantObj
  infer_instance

/-- The original second resolution arrow is a fibration in the given model category. -/
instance pBifibrant_fibration (X : C) : Fibration (pBifibrant X) := by
  exact (CofibrantObject.HoCat.exists_resolution (fibrantObj X)).choose_spec.choose_spec.choose_spec
    |>.1

/-- The original second resolution arrow is a weak equivalence in the given model category. -/
instance pBifibrant_weakEquivalence (X : C) : WeakEquivalence (pBifibrant X) := by
  exact (CofibrantObject.HoCat.exists_resolution (fibrantObj X)).choose_spec.choose_spec.choose_spec
    |>.2

/-- The actual full-subcategory object retains both proved model properties. -/
def bifibrantObject (X : C) : BifibrantObject C := BifibrantObject.mk (bifibrantObj X)

/-- The actual underlying object retains the complete two choices of model resolutions. -/
theorem bifibrantObject_obj (X : C) :
    (bifibrantObject X).obj =
      CofibrantObject.HoCat.resolutionObj (FibrantObject.HoCat.resolutionObj X) := rfl

variable {D : Type u'} [Category.{v'} D] (L : C ⥤ D)
  [L.IsLocalization (weakEquivalences C)]

/-- The same original fibrant-resolution arrow has its actual inverse in the localization. -/
def fibrantIso (X : C) : L.obj X ≅ L.obj (fibrantObj X) := by
  let _ : IsIso (L.map (iFibrant X)) :=
    Localization.inverts L (weakEquivalences C) (iFibrant X) (by
      rw [← weakEquivalence_iff]
      infer_instance)
  exact asIso (L.map (iFibrant X))

/-- The same original bifibrant projection has its actual inverse in the localization. -/
def bifibrantProjectionIso (X : C) :
    L.obj (bifibrantObj X) ≅ L.obj (fibrantObj X) := by
  let _ : IsIso (L.map (pBifibrant X)) :=
    Localization.inverts L (weakEquivalences C) (pBifibrant X) (by
      rw [← weakEquivalence_iff]
      infer_instance)
  exact asIso (L.map (pBifibrant X))

/-- Both original weak arrows give the actual isomorphism from the bifibrant image. -/
def resolutionIso (X : C) : L.obj (bifibrantObj X) ≅ L.obj X :=
  bifibrantProjectionIso L X ≪≫ (fibrantIso L X).symm

/-- The full forward resolution function uses the original projection and fibrant-unit inverse. -/
theorem resolutionIso_hom (X : C) :
    (resolutionIso L X).hom = L.map (pBifibrant X) ≫ (fibrantIso L X).inv := rfl

/-- The full inverse resolution function uses the original fibrant arrow and projection inverse. -/
theorem resolutionIso_inv (X : C) :
    (resolutionIso L X).inv = L.map (iFibrant X) ≫ (bifibrantProjectionIso L X).inv := rfl

/-- The full right homotopy quotient is identified using the genuine fundamental lemma. -/
def rightQuotientEquiv (X Y : C) :
    RightHomotopyClass (bifibrantObj X) (bifibrantObj Y) ≃ (L.obj X ⟶ L.obj Y) :=
  (Equiv.ofBijective (rightHomotopyClassToHom L)
    (bijective_rightHomotopyClassToHom L (bifibrantObj X) (bifibrantObj Y))).trans
      (Iso.homCongr (resolutionIso L X) (resolutionIso L Y))

/-- The full left homotopy quotient uses the already proved genuine fundamental-lemma API. -/
def leftQuotientEquiv (X Y : C) :
    LeftHomotopyClass (bifibrantObj X) (bifibrantObj Y) ≃ (L.obj X ⟶ L.obj Y) :=
  (Equiv.ofBijective (leftHomotopyClassToHom L) (bijective_leftHomotopyClassToHom L _ _)).trans
    (Iso.homCongr (resolutionIso L X) (resolutionIso L Y))

/-- Every original right-quotient representative retains its entire localized arrow function. -/
theorem rightQuotientEquiv_mk (X Y : C) (g : bifibrantObj X ⟶ bifibrantObj Y) :
    rightQuotientEquiv L X Y (.mk g) =
      (resolutionIso L X).inv ≫ L.map g ≫ (resolutionIso L Y).hom := rfl

/-- Every original left-quotient representative retains the same entire localized arrow function. -/
theorem leftQuotientEquiv_mk (X Y : C) (g : bifibrantObj X ⟶ bifibrantObj Y) :
    leftQuotientEquiv L X Y (.mk g) =
      (resolutionIso L X).inv ≫ L.map g ≫ (resolutionIso L Y).hom := rfl

/-- The entire bifibrant homotopy quotient retains its actual right-quotient Hom equivalence. -/
def bifibrantHomEquiv (X Y : C) :
    (BifibrantObject.toHoCat.obj (bifibrantObject X) ⟶
      BifibrantObject.toHoCat.obj (bifibrantObject Y)) ≃ (L.obj X ⟶ L.obj Y) :=
  BifibrantObject.HoCat.homEquivRight.symm.trans (rightQuotientEquiv L X Y)

/-- Each whole forward quotient input is the same localized original representative map. -/
theorem bifibrantHomEquiv_apply (X Y : C) (g : bifibrantObj X ⟶ bifibrantObj Y) :
    bifibrantHomEquiv L X Y (BifibrantObject.toHoCat.map (BifibrantObject.homMk g)) =
      (resolutionIso L X).inv ≫ L.map g ≫ (resolutionIso L Y).hom := by
  change rightQuotientEquiv L X Y
    (BifibrantObject.HoCat.homEquivRight.symm
      (BifibrantObject.toHoCat.map (BifibrantObject.homMk g))) = _
  rw [BifibrantObject.HoCat.homEquivRight_symm_apply]
  exact rightQuotientEquiv_mk L X Y g

/-- The full inverse retains the actual fundamental-lemma inverse and right homotopy quotient. -/
theorem bifibrantHomEquiv_symm_apply (X Y : C) (f : L.obj X ⟶ L.obj Y) :
    (bifibrantHomEquiv L X Y).symm f =
      BifibrantObject.HoCat.homEquivRight
        ((Equiv.ofBijective (rightHomotopyClassToHom L)
          (bijective_rightHomotopyClassToHom L (bifibrantObj X) (bifibrantObj Y))).symm
            ((resolutionIso L X).hom ≫ f ≫ (resolutionIso L Y).inv)) := rfl

/-- The same full functions also retain the actual left homotopy quotient equivalence. -/
theorem bifibrantHomEquiv_eq_left (X Y : C) :
    bifibrantHomEquiv L X Y =
      BifibrantObject.HoCat.homEquivLeft.symm.trans (leftQuotientEquiv L X Y) := by
  apply Equiv.ext
  intro f
  obtain ⟨g, rfl⟩ := BifibrantObject.toHoCat.map_surjective f
  let g' : bifibrantObj X ⟶ bifibrantObj Y := g.hom
  change rightQuotientEquiv L X Y
      (BifibrantObject.HoCat.homEquivRight.symm
        (BifibrantObject.toHoCat.map (BifibrantObject.homMk g'))) =
    leftQuotientEquiv L X Y
      (BifibrantObject.HoCat.homEquivLeft.symm
        (BifibrantObject.toHoCat.map (BifibrantObject.homMk g')))
  rw [BifibrantObject.HoCat.homEquivRight_symm_apply,
    BifibrantObject.HoCat.homEquivLeft_symm_apply]
  rfl

/-- Both full functions return every original bifibrant quotient input. -/
theorem bifibrantHomEquiv_left_triangle (X Y : C)
    (g : BifibrantObject.toHoCat.obj (bifibrantObject X) ⟶
      BifibrantObject.toHoCat.obj (bifibrantObject Y)) :
    (bifibrantHomEquiv L X Y).symm (bifibrantHomEquiv L X Y g) = g :=
  (bifibrantHomEquiv L X Y).symm_apply_apply g

/-- Both full functions return every arbitrary localization input. -/
theorem bifibrantHomEquiv_right_triangle (X Y : C) (f : L.obj X ⟶ L.obj Y) :
    bifibrantHomEquiv L X Y ((bifibrantHomEquiv L X Y).symm f) = f :=
  (bifibrantHomEquiv L X Y).apply_symm_apply f

/-- The fundamental lemma chooses an actual map between the proved bifibrant representatives. -/
def representative {X Y : C} (f : L.obj X ⟶ L.obj Y) :
    bifibrantObj X ⟶ bifibrantObj Y :=
  (map_surjective_of_isLocalization L (bifibrantObj X) (bifibrantObj Y)
    ((resolutionIso L X).hom ≫ f ≫ (resolutionIso L Y).inv)).choose

/-- Its whole localization map retains both original source and target resolution functions. -/
theorem representative_map {X Y : C} (f : L.obj X ⟶ L.obj Y) :
    L.map (representative L f) =
      (resolutionIso L X).hom ≫ f ≫ (resolutionIso L Y).inv :=
  (map_surjective_of_isLocalization L (bifibrantObj X) (bifibrantObj Y)
    ((resolutionIso L X).hom ≫ f ≫ (resolutionIso L Y).inv)).choose_spec

/-- The actual chosen representative returns the entire given localization arrow. -/
theorem representative_reconstruction {X Y : C} (f : L.obj X ⟶ L.obj Y) :
    (resolutionIso L X).inv ≫ L.map (representative L f) ≫ (resolutionIso L Y).hom = f := by
  rw [representative_map]
  exact (Iso.homCongr (resolutionIso L X) (resolutionIso L Y)).apply_symm_apply f

/-- The actual representative is precisely the inverse of the full bifibrant quotient function. -/
theorem representative_quotient {X Y : C} (f : L.obj X ⟶ L.obj Y) :
    BifibrantObject.toHoCat.map (BifibrantObject.homMk (representative L f)) =
      (bifibrantHomEquiv L X Y).symm f := by
  apply (bifibrantHomEquiv L X Y).injective
  exact (bifibrantHomEquiv_apply L X Y (representative L f)).trans
    ((representative_reconstruction L f).trans
      ((bifibrantHomEquiv L X Y).apply_symm_apply f).symm)

/-- Every identity retains both complete original resolution maps in the quotient. -/
theorem bifibrantHomEquiv_id (X : C) :
    bifibrantHomEquiv L X X (𝟙 (BifibrantObject.toHoCat.obj (bifibrantObject X))) =
      𝟙 (L.obj X) := by
  rw [← BifibrantObject.toHoCat.map_id]
  change bifibrantHomEquiv L X X
    (BifibrantObject.toHoCat.map (BifibrantObject.homMk (𝟙 (bifibrantObj X)))) = _
  rw [bifibrantHomEquiv_apply, L.map_id, Category.id_comp, Iso.inv_hom_id]

/-- The full quotient forward function preserves every composition of quotient arrows. -/
theorem bifibrantHomEquiv_comp {X Y Z : C}
    (f : BifibrantObject.toHoCat.obj (bifibrantObject X) ⟶
      BifibrantObject.toHoCat.obj (bifibrantObject Y))
    (g : BifibrantObject.toHoCat.obj (bifibrantObject Y) ⟶
      BifibrantObject.toHoCat.obj (bifibrantObject Z)) :
    bifibrantHomEquiv L X Z (f ≫ g) =
      bifibrantHomEquiv L X Y f ≫ bifibrantHomEquiv L Y Z g := by
  obtain ⟨f, rfl⟩ := BifibrantObject.toHoCat.map_surjective f
  obtain ⟨g, rfl⟩ := BifibrantObject.toHoCat.map_surjective g
  let f' : bifibrantObj X ⟶ bifibrantObj Y := f.hom
  let g' : bifibrantObj Y ⟶ bifibrantObj Z := g.hom
  change (resolutionIso L X).inv ≫ L.map (f' ≫ g') ≫ (resolutionIso L Z).hom =
    ((resolutionIso L X).inv ≫ L.map f' ≫ (resolutionIso L Y).hom) ≫
      ((resolutionIso L Y).inv ≫ L.map g' ≫ (resolutionIso L Z).hom)
  rw [L.map_comp]
  exact Iso.homCongr_comp (resolutionIso L X) (resolutionIso L Y) (resolutionIso L Z)
    (L.map f') (L.map g')

/-- Every arbitrary localization source arrow retains the full inverse quotient function. -/
theorem bifibrantHomEquiv_source_symm {X X' Y : C}
    (a : L.obj X' ⟶ L.obj X) (f : L.obj X ⟶ L.obj Y) :
    (bifibrantHomEquiv L X' Y).symm (a ≫ f) =
      (bifibrantHomEquiv L X' X).symm a ≫ (bifibrantHomEquiv L X Y).symm f := by
  apply (bifibrantHomEquiv L X' Y).injective
  rw [Equiv.apply_symm_apply, bifibrantHomEquiv_comp,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Every arbitrary localization target arrow retains the full inverse quotient function. -/
theorem bifibrantHomEquiv_target_symm {X Y Y' : C}
    (b : L.obj Y ⟶ L.obj Y') (f : L.obj X ⟶ L.obj Y) :
    (bifibrantHomEquiv L X Y').symm (f ≫ b) =
      (bifibrantHomEquiv L X Y).symm f ≫ (bifibrantHomEquiv L Y Y').symm b :=
  bifibrantHomEquiv_source_symm L f b

/-- The complete inverse quotient is characterized by its actual forward Hom function. -/
theorem bifibrantHomEquiv_characteristic (X Y : C) (f : L.obj X ⟶ L.obj Y)
    (g : BifibrantObject.toHoCat.obj (bifibrantObject X) ⟶
      BifibrantObject.toHoCat.obj (bifibrantObject Y)) :
    (bifibrantHomEquiv L X Y).symm f = g ↔ bifibrantHomEquiv L X Y g = f := by
  constructor
  · intro h
    rw [← h]
    exact bifibrantHomEquiv_right_triangle L X Y f
  · intro h
    exact (congrArg (bifibrantHomEquiv L X Y).symm h.symm).trans
      ((bifibrantHomEquiv L X Y).symm_apply_apply g)

end HomotopicalAlgebra.LocalizationBifibrantResolution
