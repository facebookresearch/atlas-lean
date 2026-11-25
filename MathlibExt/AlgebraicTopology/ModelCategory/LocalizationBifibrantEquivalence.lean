/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.LocalizationBifibrantResolution

/-!
# The actual chosen bifibrant resolution is a full homotopy-category equivalence

The same model-factorization choices and fundamental-lemma representatives
define an actual functor on every ordinary homotopy-category arrow. The
existing genuine bifibrant comparison supplies the reverse functor. Both
full comparison functions, original resolution arrows, naturalities, unit,
counit and triangles are retained. No equality of independently chosen
resolution or inverse functors is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u v u' v'

open CategoryTheory

namespace HomotopicalAlgebra.LocalizationBifibrantResolution

variable {C : Type u} [Category.{v} C] [ModelCategory C]

private abbrev H := ((weakEquivalences C).Q)
private abbrev Ho := ((weakEquivalences C).Localization)
private abbrev BHo := BifibrantObject.HoCat C
private noncomputable abbrev E : BifibrantObject.HoCat C ≌ (weakEquivalences C).Localization :=
  Localization.uniq BifibrantObject.toHoCat (BifibrantObject.ι ⋙ (weakEquivalences C).Q)
    (weakEquivalences (BifibrantObject C))
private abbrev comparison :
    BifibrantObject.toHoCat ⋙ (E (C := C)).functor ≅ BifibrantObject.ι ⋙ (weakEquivalences C).Q :=
  Localization.compUniqFunctor BifibrantObject.toHoCat (BifibrantObject.ι ⋙ (weakEquivalences C).Q)
    (weakEquivalences (BifibrantObject C))

/-- The object uses the same complete choices of fibrant and cofibrant model resolutions. -/
def hoResolutionObject (X : Ho (C := C)) : BHo (C := C) :=
  BifibrantObject.toHoCat.obj (bifibrantObject X.as.obj)

/-- Both full Hom functions use the same chosen bifibrant quotient and original weak arrows. -/
def hoResolutionHomEquiv (X Y : Ho (C := C)) :
    (hoResolutionObject X ⟶ hoResolutionObject Y) ≃ (X ⟶ Y) := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact bifibrantHomEquiv H X Y

/-- The actual inverse Hom function retains every arbitrary homotopy-category source action. -/
theorem hoResolutionHomEquiv_source_symm {X X' Y : Ho (C := C)}
    (a : X' ⟶ X) (f : X ⟶ Y) :
    (hoResolutionHomEquiv X' Y).symm (a ≫ f) =
      (hoResolutionHomEquiv X' X).symm a ≫ (hoResolutionHomEquiv X Y).symm f := by
  rcases X with ⟨⟨X⟩⟩
  rcases X' with ⟨⟨X'⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact bifibrantHomEquiv_source_symm H a f

/-- The same two complete resolution functions identify the actual quotient identity. -/
theorem hoResolutionHomEquiv_id (X : Ho (C := C)) :
    hoResolutionHomEquiv X X (𝟙 (hoResolutionObject X)) = 𝟙 X := by
  rcases X with ⟨⟨X⟩⟩
  exact bifibrantHomEquiv_id H X

/-- The full chosen resolution functor acts on every ordinary homotopy-category arrow. -/
def hoResolution : Ho (C := C) ⥤ BHo (C := C) where
  obj := hoResolutionObject
  map f := (hoResolutionHomEquiv _ _).symm f
  map_id X := (hoResolutionHomEquiv X X).injective
    (((hoResolutionHomEquiv X X).apply_symm_apply (𝟙 X)).trans
      (hoResolutionHomEquiv_id X).symm)
  map_comp f g := hoResolutionHomEquiv_source_symm f g

/-- Each object retains precisely the complete original bifibrant quotient object. -/
theorem hoResolution_obj (X : Ho (C := C)) :
    hoResolution.obj X = BifibrantObject.toHoCat.obj (bifibrantObject X.as.obj) := rfl

/-- Each full map is the actual inverse fundamental-lemma quotient function. -/
theorem hoResolution_map {X Y : Ho (C := C)} (f : X ⟶ Y) :
    hoResolution.map f = (hoResolutionHomEquiv X Y).symm f := rfl

/-- Each original source is the same actual chosen strict representative in the full quotient. -/
theorem hoResolution_map_representative {X Y : Ho (C := C)} (f : X ⟶ Y) :
    hoResolution.map f =
      BifibrantObject.toHoCat.map (BifibrantObject.homMk (representative H f)) := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact (representative_quotient H f).symm

/-- Both full inverse Hom functions prove that this actual chosen functor is fully faithful. -/
def hoResolutionFullyFaithful : hoResolution (C := C) |>.FullyFaithful where
  preimage f := hoResolutionHomEquiv _ _ f
  map_preimage f := (hoResolutionHomEquiv _ _).symm_apply_apply f
  preimage_map f := (hoResolutionHomEquiv _ _).apply_symm_apply f

/-- The actual bifibrant comparison and both original weak arrows identify each source object. -/
def hoResolutionComparisonIso (X : Ho (C := C)) :
    E.functor.obj (hoResolution.obj X) ≅ X := by
  rcases X with ⟨⟨X⟩⟩
  exact comparison.app (bifibrantObject X) ≪≫ resolutionIso H X

/-- The complete forward comparison retains the actual bifibrant comparison and resolution hom. -/
theorem hoResolutionComparisonIso_hom (X : Ho (C := C)) :
    (hoResolutionComparisonIso X).hom =
      (comparison.app (bifibrantObject X.as.obj)).hom ≫ (resolutionIso H X.as.obj).hom := by
  rcases X with ⟨⟨X⟩⟩
  rfl

/-- The full inverse retains the original resolution inverse and bifibrant comparison inverse. -/
theorem hoResolutionComparisonIso_inv (X : Ho (C := C)) :
    (hoResolutionComparisonIso X).inv =
      (resolutionIso H X.as.obj).inv ≫ (comparison.app (bifibrantObject X.as.obj)).inv := by
  rcases X with ⟨⟨X⟩⟩
  rfl

/-- The actual strict representative has its full original right resolution-map equation. -/
theorem representative_right_resolution_map {D : Type u'} [Category.{v'} D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] {X Y : C} (f : L.obj X ⟶ L.obj Y) :
    L.map (representative L f) ≫ (resolutionIso L Y).hom =
      (resolutionIso L X).hom ≫ f := by
  let eX := resolutionIso L X
  let eY := resolutionIso L Y
  have cancel : (f ≫ eY.inv) ≫ eY.hom = f :=
    (Category.assoc f eY.inv eY.hom).trans
      ((congrArg (fun g : L.obj Y ⟶ L.obj Y => f ≫ g) eY.inv_hom_id).trans
        (Category.comp_id f))
  have h : (eX.hom ≫ f ≫ eY.inv) ≫ eY.hom = eX.hom ≫ f :=
    (Category.assoc eX.hom (f ≫ eY.inv) eY.hom).trans
      (congrArg (fun g : L.obj X ⟶ L.obj Y => eX.hom ≫ g) cancel)
  exact (congrArg
    (fun g : L.obj (bifibrantObj X) ⟶ L.obj (bifibrantObj Y) => g ≫ eY.hom)
    (representative_map L f)).trans h

/-- Every ordinary homotopy-category arrow preserves the complete original object comparison. -/
theorem hoResolutionComparisonIso_naturality {X Y : Ho (C := C)} (f : X ⟶ Y) :
    E.functor.map (hoResolution.map f) ≫ (hoResolutionComparisonIso Y).hom =
      (hoResolutionComparisonIso X).hom ≫ f := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  let g : bifibrantObj X ⟶ bifibrantObj Y := representative H f
  let aX := comparison.app (bifibrantObject X)
  let aY := comparison.app (bifibrantObject Y)
  let eX := resolutionIso H X
  let eY := resolutionIso H Y
  have h₀ : E.functor.map (BifibrantObject.toHoCat.map (BifibrantObject.homMk g)) ≫ aY.hom =
      aX.hom ≫ H.map g :=
    comparison.hom.naturality (BifibrantObject.homMk g)
  have h₁ : H.map g ≫ eY.hom = eX.hom ≫ f :=
    representative_right_resolution_map H f
  have hm : E.functor.map (hoResolution.map f) =
      E.functor.map (BifibrantObject.toHoCat.map (BifibrantObject.homMk g)) :=
    E.functor.congr_map (hoResolution_map_representative f)
  have h : E.functor.map (hoResolution.map f) ≫ aY.hom = aX.hom ≫ H.map g :=
    (congrArg (fun k => k ≫ aY.hom) hm).trans h₀
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ eY.hom) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => aX.hom ≫ k) h₁).trans (Category.assoc _ _ _).symm)))

/-- The full object comparison is a natural isomorphism retaining both complete functions. -/
def hoResolutionComparison : hoResolution (C := C) ⋙ E.functor ≅ 𝟭 Ho :=
  NatIso.ofComponents hoResolutionComparisonIso (fun f => hoResolutionComparisonIso_naturality f)

/-- Every full forward component is the same original object comparison. -/
theorem hoResolutionComparison_hom_app (X : Ho (C := C)) :
    hoResolutionComparison.hom.app X = (hoResolutionComparisonIso X).hom := rfl

/-- Every full inverse component is the same original inverse object comparison. -/
theorem hoResolutionComparison_inv_app (X : Ho (C := C)) :
    hoResolutionComparison.inv.app X = (hoResolutionComparisonIso X).inv := rfl

/-- The actual fully faithful bifibrant comparison returns every original bifibrant object. -/
def hoResolutionReturnIso (X : BHo (C := C)) :
    hoResolution.obj (E.functor.obj X) ≅ X :=
  E.fullyFaithfulFunctor.preimageIso (hoResolutionComparison.app (E.functor.obj X))

/-- The entire return hom is sent to the original comparison hom at the same original object. -/
theorem hoResolutionReturnIso_hom_map (X : BHo (C := C)) :
    E.functor.map (hoResolutionReturnIso X).hom =
      hoResolutionComparison.hom.app (E.functor.obj X) :=
  E.fullyFaithfulFunctor.map_preimage _

/-- The entire return inverse is sent to the original comparison inverse at the same object. -/
theorem hoResolutionReturnIso_inv_map (X : BHo (C := C)) :
    E.functor.map (hoResolutionReturnIso X).inv =
      hoResolutionComparison.inv.app (E.functor.obj X) :=
  E.fullyFaithfulFunctor.map_preimage _

/-- Both full functions return every original bifibrant quotient object naturally. -/
def hoResolutionReturn : E.functor ⋙ hoResolution (C := C) ≅ 𝟭 BHo :=
  NatIso.ofComponents hoResolutionReturnIso (fun {X Y} f => by
    apply E.fullyFaithfulFunctor.map_injective
    let a := hoResolution.map (E.functor.map f)
    have h : E.functor.map a ≫ hoResolutionComparison.hom.app (E.functor.obj Y) =
        hoResolutionComparison.hom.app (E.functor.obj X) ≫ E.functor.map f :=
      hoResolutionComparison.hom.naturality (E.functor.map f)
    exact (E.functor.map_comp a (hoResolutionReturnIso Y).hom).trans
      ((congrArg (fun k => E.functor.map a ≫ k) (hoResolutionReturnIso_hom_map Y)).trans
        (h.trans ((congrArg (fun k => k ≫ E.functor.map f)
          (hoResolutionReturnIso_hom_map X).symm).trans
            (E.functor.map_comp (hoResolutionReturnIso X).hom f).symm))))

/-- The same choices give a full equivalence with the genuine existing comparison as inverse. -/
def hoResolutionEquivalence : Ho (C := C) ≌ BHo (C := C) where
  functor := hoResolution
  inverse := E.functor
  unitIso := hoResolutionComparison.symm
  counitIso := hoResolutionReturn
  functor_unitIso_comp X := by
    apply E.fullyFaithfulFunctor.map_injective
    let a := hoResolution.map (hoResolutionComparison.inv.app X)
    have h : E.functor.map a ≫
        hoResolutionComparison.hom.app (E.functor.obj (hoResolution.obj X)) =
          hoResolutionComparison.hom.app X ≫ hoResolutionComparison.inv.app X :=
      hoResolutionComparison.hom.naturality (hoResolutionComparison.inv.app X)
    exact (E.functor.map_comp a (hoResolutionReturnIso (hoResolution.obj X)).hom).trans
      ((congrArg (fun k => E.functor.map a ≫ k)
        (hoResolutionReturnIso_hom_map (hoResolution.obj X))).trans
          (h.trans ((hoResolutionComparison.hom_inv_id_app X).trans
            (E.functor.map_id (hoResolution.obj X)).symm)))

/-- The complete forward functor is the actual chosen original bifibrant resolution functor. -/
theorem hoResolutionEquivalence_functor :
    (hoResolutionEquivalence (C := C)).functor = hoResolution := rfl

/-- The complete inverse is the actual existing bifibrant comparison, with every original map. -/
theorem hoResolutionEquivalence_inverse :
    (hoResolutionEquivalence (C := C)).inverse = E.functor := rfl

/-- The complete unit hom is the original inverse resolution comparison at every source. -/
theorem hoResolutionEquivalence_unit_hom_app (X : Ho (C := C)) :
    hoResolutionEquivalence.unitIso.hom.app X = (hoResolutionComparisonIso X).inv := rfl

/-- The complete unit inverse is the original forward resolution comparison at every source. -/
theorem hoResolutionEquivalence_unit_inv_app (X : Ho (C := C)) :
    hoResolutionEquivalence.unitIso.inv.app X = (hoResolutionComparisonIso X).hom := rfl

/-- The original unit hom retains the whole fibrant arrow and inverse bifibrant projection. -/
theorem hoResolutionEquivalence_unit_original_maps (X : C) :
    hoResolutionEquivalence.unitIso.hom.app (H.obj X) =
      H.map (iFibrant X) ≫ (bifibrantProjectionIso H X).inv ≫
        (comparison.app (bifibrantObject X)).inv :=
  Category.assoc _ _ _

/-- The original unit inverse retains the whole bifibrant projection and fibrant inverse. -/
theorem hoResolutionEquivalence_unit_inverse_original_maps (X : C) :
    hoResolutionEquivalence.unitIso.inv.app (H.obj X) =
      (comparison.app (bifibrantObject X)).hom ≫ H.map (pBifibrant X) ≫ (fibrantIso H X).inv :=
  rfl

/-- The counit hom uses the complete actual inverse Hom function of the bifibrant comparison. -/
theorem hoResolutionEquivalence_counit_hom (X : BHo (C := C)) :
    hoResolutionEquivalence.counitIso.hom.app X =
      E.fullyFaithfulFunctor.preimage (hoResolutionComparison.hom.app (E.functor.obj X)) := rfl

/-- The counit inverse uses the complete actual inverse Hom function on the inverse comparison. -/
theorem hoResolutionEquivalence_counit_inv (X : BHo (C := C)) :
    hoResolutionEquivalence.counitIso.inv.app X =
      E.fullyFaithfulFunctor.preimage (hoResolutionComparison.inv.app (E.functor.obj X)) := rfl

/-- Every arbitrary original source arrow retains the whole forward unit naturality square. -/
theorem hoResolutionEquivalence_unit_naturality {X Y : Ho (C := C)} (f : X ⟶ Y) :
    f ≫ hoResolutionEquivalence.unitIso.hom.app Y =
      hoResolutionEquivalence.unitIso.hom.app X ≫ E.functor.map (hoResolution.map f) :=
  hoResolutionEquivalence.unitIso.hom.naturality f

/-- Every arbitrary original source arrow retains the whole inverse unit naturality square. -/
theorem hoResolutionEquivalence_unit_inverse_naturality {X Y : Ho (C := C)} (f : X ⟶ Y) :
    E.functor.map (hoResolution.map f) ≫ hoResolutionEquivalence.unitIso.inv.app Y =
      hoResolutionEquivalence.unitIso.inv.app X ≫ f :=
  hoResolutionEquivalence.unitIso.inv.naturality f

/-- Every original bifibrant quotient arrow retains the entire forward counit naturality. -/
theorem hoResolutionEquivalence_counit_naturality {X Y : BHo (C := C)} (f : X ⟶ Y) :
    hoResolution.map (E.functor.map f) ≫ hoResolutionEquivalence.counitIso.hom.app Y =
      hoResolutionEquivalence.counitIso.hom.app X ≫ f :=
  hoResolutionEquivalence.counitIso.hom.naturality f

/-- Every original bifibrant quotient arrow retains the entire inverse counit naturality. -/
theorem hoResolutionEquivalence_counit_inverse_naturality {X Y : BHo (C := C)} (f : X ⟶ Y) :
    f ≫ hoResolutionEquivalence.counitIso.inv.app Y =
      hoResolutionEquivalence.counitIso.inv.app X ≫ hoResolution.map (E.functor.map f) :=
  hoResolutionEquivalence.counitIso.inv.naturality f

/-- The actual forward functor and both complete comparison functions satisfy the first triangle. -/
theorem hoResolutionEquivalence_first_triangle (X : Ho (C := C)) :
    hoResolution.map (hoResolutionEquivalence.unitIso.hom.app X) ≫
      hoResolutionEquivalence.counitIso.hom.app (hoResolution.obj X) =
        𝟙 (hoResolution.obj X) :=
  hoResolutionEquivalence.functor_unitIso_comp X

/-- The actual inverse functor and both full comparison functions satisfy the second triangle. -/
theorem hoResolutionEquivalence_second_triangle (X : BHo (C := C)) :
    hoResolutionEquivalence.unitIso.hom.app (E.functor.obj X) ≫
      E.functor.map (hoResolutionEquivalence.counitIso.hom.app X) =
        𝟙 (E.functor.obj X) :=
  (congrArg (fun k => hoResolutionComparison.inv.app (E.functor.obj X) ≫ k)
    (hoResolutionReturnIso_hom_map X)).trans
      (hoResolutionComparison.inv_hom_id_app (E.functor.obj X))

end HomotopicalAlgebra.LocalizationBifibrantResolution
