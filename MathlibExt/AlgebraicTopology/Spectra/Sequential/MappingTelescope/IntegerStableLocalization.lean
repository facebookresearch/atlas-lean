/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStablePiHo
import
  MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerLocalization

/-!
# Original integer homotopy on the actual integer localization

The actual path and quotient category inverts the original all-degree
integer equivalences. The original integer homotopy functors descend with
their complete original objects and maps. The already constructed Ω
reflector gives a genuine equivalence with its original full subcategory
of the level homotopy category. All source maps, inverse maps, unit and
counit functions, Hom functions and integer comparison functions are
retained. This is a categorical localization construction.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.NativeKRTComparisonGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.NativeIntegerLocalizationGeometry
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStableLocalizationGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}

/-- The full category is the actual localization at the original integer testing arrows. -/
abbrev IntegerStableHomotopyCategory := integerPiStarEquivalences.{u, v}.Localization

/-- The source projection uses precisely the original all-degree integer testing class. -/
def integerStableProjection : Carrier.{u, v} ⥤ IntegerStableHomotopyCategory.{u, v} :=
  integerPiStarEquivalences.Q

private instance integerStableProjection_isLocalization :
    integerStableProjection.{u, v}.IsLocalization integerPiStarEquivalences := by
  unfold integerStableProjection
  infer_instance

/-- Every original integer testing arrow is inverted by each original integer homotopy functor. -/
theorem integerStablePiFunctor_invertsInteger (q : ℤ) :
    integerPiStarEquivalences.{u, v}.IsInvertedBy (integerStablePiFunctor q) :=
  fun _ _ f hf => (integerPiStarEquivalences_iff f).mp hf q

/-- The actual path and quotient construction retains the full original group functor. -/
def integerStablePiStableFunctor (q : ℤ) :
    IntegerStableHomotopyCategory.{u, v} ⥤ GrpCat.{v} :=
  Localization.Construction.lift (integerStablePiFunctor q)
    (integerStablePiFunctor_invertsInteger q)

/-- Every source object retains the original integer group with all original operations. -/
theorem integerStablePiStableFunctor_obj (q : ℤ) (X : Carrier.{u, v}) :
    (integerStablePiStableFunctor q).obj (integerStableProjection.obj X) =
      (integerStablePiFunctor q).obj X := rfl

/-- The whole projected original integer functor is unchanged on objects and on every map. -/
theorem integerStablePiStableFunctor_original (q : ℤ) :
    integerStableProjection ⋙ integerStablePiStableFunctor.{u, v} q =
      integerStablePiFunctor q :=
  Localization.Construction.fac (integerStablePiFunctor q)
    (integerStablePiFunctor_invertsInteger q)

/-- Every projected source morphism retains its entire original diagonal-colimit function. -/
theorem integerStablePiStableFunctor_map (q : ℤ) {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (integerStablePiStableFunctor q).map (integerStableProjection.map f) =
      (integerStablePiFunctor q).map f := by
  have h := Functor.congr_hom (integerStablePiStableFunctor_original q) f
  change (integerStablePiStableFunctor q).map (integerStableProjection.map f) =
    (𝟙 ((integerStablePiFunctor q).obj X)) ≫ (integerStablePiFunctor q).map f ≫
      (𝟙 ((integerStablePiFunctor q).obj Y)) at h
  simpa only [Category.id_comp, Category.comp_id] using h

/-- The full original group isomorphism uses the actual image of the given integer testing arrow. -/
def originalIntegerArrowGroupIso (q : ℤ) {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : integerPiStarEquivalences f) :
    (integerStablePiFunctor q).obj X ≅ (integerStablePiFunctor q).obj Y := by
  let _ := (integerPiStarEquivalences_iff f).mp hf q
  exact asIso ((integerStablePiFunctor q).map f)

/-- The whole forward group function is precisely the original diagonal-colimit map. -/
theorem originalIntegerArrowGroupIso_hom (q : ℤ) {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : integerPiStarEquivalences f) :
    (originalIntegerArrowGroupIso q f hf).hom = (integerStablePiFunctor q).map f := rfl

/-- Both full functions of each formal inverse retain the original integer group isomorphism. -/
theorem integerStablePiStableFunctor_map_wIso (q : ℤ) {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : integerPiStarEquivalences f) :
    (integerStablePiStableFunctor q).mapIso (Localization.Construction.wIso f hf) =
      originalIntegerArrowGroupIso q f hf := by
  apply Iso.ext
  exact integerStablePiStableFunctor_map q f

/-- The full formal inverse acts by the actual inverse of the original group map. -/
theorem integerStablePiStableFunctor_map_wIso_inv (q : ℤ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) (hf : integerPiStarEquivalences f) :
    (integerStablePiStableFunctor q).map (Localization.Construction.wIso f hf).inv =
      (originalIntegerArrowGroupIso q f hf).inv :=
  congrArg (fun e => e.inv) (integerStablePiStableFunctor_map_wIso q f hf)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  originalIntegerLocalization_isLocalization

private abbrev H := toHomotopyCategory Carrier.{u, v}
private abbrev Ho := HomotopyCategory Carrier.{u, v}

/-- The original proved Ω localization gives a genuine equivalence from the integer localization. -/
def integerStableOmegaEquivalence :
    IntegerStableHomotopyCategory.{u, v} ≌ omegaHoObjects.FullSubcategory := by
  let _ : originalIntegerLocalization.{u, v}.IsLocalization integerPiStarEquivalences :=
    originalIntegerLocalization_isLocalization
  exact Localization.equivalenceFromModel originalIntegerLocalization integerPiStarEquivalences

/-- The complete original Ω source functor is retained after the integer source projection. -/
theorem integerStableOmegaEquivalence_sourceFunctor :
    integerStableProjection ⋙ integerStableOmegaEquivalence.{u, v}.functor =
      originalIntegerLocalization :=
  Localization.Construction.fac originalIntegerLocalization
    (Localization.inverts originalIntegerLocalization integerPiStarEquivalences)

/-- Every original source object is precisely the original R(T(X)) object in the level category. -/
theorem integerStableOmegaEquivalence_obj (X : Carrier.{u, v}) :
    (integerStableOmegaEquivalence.functor.obj (integerStableProjection.obj X)).obj =
      H.obj (reflectionFunctor.obj X) :=
  originalIntegerLocalization_obj X

/-- Every projected original arrow uses the original two-map R-after-T image. -/
theorem integerStableOmegaEquivalence_map {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (integerStableOmegaEquivalence.functor.map (integerStableProjection.map f)).hom =
      H.map (reflectionFunctor.map f) := by
  have h := Functor.congr_hom integerStableOmegaEquivalence_sourceFunctor f
  change integerStableOmegaEquivalence.functor.map (integerStableProjection.map f) =
    (𝟙 (originalIntegerLocalization.obj X)) ≫ originalIntegerLocalization.map f ≫
      (𝟙 (originalIntegerLocalization.obj Y)) at h
  have hm : integerStableOmegaEquivalence.functor.map (integerStableProjection.map f) =
      originalIntegerLocalization.map f := by
    simpa only [Category.id_comp, Category.comp_id] using h
  exact (congrArg (fun a : originalIntegerLocalization.obj X ⟶
      originalIntegerLocalization.obj Y => a.hom) hm).trans
    (originalIntegerLocalization_map f)

/-- Every original integer arrow retains both original Ω image functions after localization. -/
theorem integerStableOmegaEquivalence_map_wIso {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : integerPiStarEquivalences f) :
    integerStableOmegaEquivalence.functor.mapIso (Localization.Construction.wIso f hf) =
      Localization.isoOfHom originalIntegerLocalization integerPiStarEquivalences f hf := by
  apply Iso.ext
  change integerStableOmegaEquivalence.functor.map (integerStableProjection.map f) =
    originalIntegerLocalization.map f
  have h := Functor.congr_hom integerStableOmegaEquivalence_sourceFunctor f
  change integerStableOmegaEquivalence.functor.map (integerStableProjection.map f) =
    (𝟙 (originalIntegerLocalization.obj X)) ≫ originalIntegerLocalization.map f ≫
      (𝟙 (originalIntegerLocalization.obj Y)) at h
  simpa only [Category.id_comp, Category.comp_id] using h

/-- Every original formal inverse retains the actual inverse of the complete Ω source image. -/
theorem integerStableOmegaEquivalence_map_wIso_inv {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : integerPiStarEquivalences f) :
    integerStableOmegaEquivalence.functor.map (Localization.Construction.wIso f hf).inv =
      (Localization.isoOfHom originalIntegerLocalization integerPiStarEquivalences f hf).inv :=
  congrArg (fun e => e.inv) (integerStableOmegaEquivalence_map_wIso f hf)

/-- The full Hom functions retain the actual equivalence functor, inverse, unit and counit. -/
def integerStableOmegaHomEquiv (X Y : IntegerStableHomotopyCategory.{u, v}) :
    (X ⟶ Y) ≃
      (integerStableOmegaEquivalence.functor.obj X ⟶
        integerStableOmegaEquivalence.functor.obj Y) :=
  integerStableOmegaEquivalence.fullyFaithfulFunctor.homEquiv

/-- Every whole forward Hom function is the actual constructed Ω equivalence functor map. -/
theorem integerStableOmegaHomEquiv_apply (X Y : IntegerStableHomotopyCategory.{u, v})
    (f : X ⟶ Y) :
    integerStableOmegaHomEquiv X Y f = integerStableOmegaEquivalence.functor.map f := rfl

/-- Every whole inverse uses the actual inverse functor and both original equivalence-unit maps. -/
theorem integerStableOmegaHomEquiv_symm_apply
    (X Y : IntegerStableHomotopyCategory.{u, v})
    (g : integerStableOmegaEquivalence.functor.obj X ⟶
      integerStableOmegaEquivalence.functor.obj Y) :
    (integerStableOmegaHomEquiv X Y).symm g =
      integerStableOmegaEquivalence.unitIso.hom.app X ≫
        integerStableOmegaEquivalence.inverse.map g ≫
          integerStableOmegaEquivalence.unitIso.inv.app Y := rfl

/-- Both complete Hom functions return every original integer-localization arrow. -/
theorem integerStableOmegaHomEquiv_left_triangle
    (X Y : IntegerStableHomotopyCategory.{u, v}) (f : X ⟶ Y) :
    (integerStableOmegaHomEquiv X Y).symm (integerStableOmegaEquivalence.functor.map f) = f :=
  (integerStableOmegaHomEquiv X Y).symm_apply_apply f

/-- Both complete Hom functions return every original Ω full-subcategory arrow. -/
theorem integerStableOmegaHomEquiv_right_triangle
    (X Y : IntegerStableHomotopyCategory.{u, v})
    (g : integerStableOmegaEquivalence.functor.obj X ⟶
      integerStableOmegaEquivalence.functor.obj Y) :
    integerStableOmegaEquivalence.functor.map ((integerStableOmegaHomEquiv X Y).symm g) = g :=
  (integerStableOmegaHomEquiv X Y).apply_symm_apply g

/-- The full inverse is characterized by its image under the actual original Ω equivalence. -/
theorem integerStableOmegaHomEquiv_characteristic
    (X Y : IntegerStableHomotopyCategory.{u, v})
    (g : integerStableOmegaEquivalence.functor.obj X ⟶
      integerStableOmegaEquivalence.functor.obj Y) (f : X ⟶ Y) :
    (integerStableOmegaHomEquiv X Y).symm g = f ↔
      integerStableOmegaEquivalence.functor.map f = g := by
  constructor
  · intro h
    rw [← h]
    exact integerStableOmegaHomEquiv_right_triangle X Y g
  · intro h
    exact (congrArg (integerStableOmegaHomEquiv X Y).symm h.symm).trans
      ((integerStableOmegaHomEquiv X Y).symm_apply_apply f)

/-- Arbitrary integer-localization source arrows retain the entire forward Hom naturality. -/
theorem integerStableOmegaHomEquiv_source
    {X X' Y : IntegerStableHomotopyCategory.{u, v}} (a : X' ⟶ X) (f : X ⟶ Y) :
    integerStableOmegaHomEquiv X' Y (a ≫ f) =
      integerStableOmegaEquivalence.functor.map a ≫ integerStableOmegaHomEquiv X Y f :=
  integerStableOmegaEquivalence.functor.map_comp a f

/-- Arbitrary integer-localization source arrows retain the complete inverse Hom naturality. -/
theorem integerStableOmegaHomEquiv_source_symm
    {X X' Y : IntegerStableHomotopyCategory.{u, v}} (a : X' ⟶ X)
    (g : integerStableOmegaEquivalence.functor.obj X ⟶
      integerStableOmegaEquivalence.functor.obj Y) :
    (integerStableOmegaHomEquiv X' Y).symm
      (integerStableOmegaEquivalence.functor.map a ≫ g) =
        a ≫ (integerStableOmegaHomEquiv X Y).symm g := by
  apply (integerStableOmegaHomEquiv X' Y).injective
  rw [Equiv.apply_symm_apply, integerStableOmegaHomEquiv_source, Equiv.apply_symm_apply]

/-- Arbitrary integer-localization target arrows retain the complete forward Hom naturality. -/
theorem integerStableOmegaHomEquiv_target
    {X Y Y' : IntegerStableHomotopyCategory.{u, v}} (b : Y ⟶ Y') (f : X ⟶ Y) :
    integerStableOmegaHomEquiv X Y' (f ≫ b) =
      integerStableOmegaHomEquiv X Y f ≫ integerStableOmegaEquivalence.functor.map b :=
  integerStableOmegaEquivalence.functor.map_comp f b

/-- Arbitrary integer-localization target arrows retain the complete inverse Hom naturality. -/
theorem integerStableOmegaHomEquiv_target_symm
    {X Y Y' : IntegerStableHomotopyCategory.{u, v}} (b : Y ⟶ Y')
    (g : integerStableOmegaEquivalence.functor.obj X ⟶
      integerStableOmegaEquivalence.functor.obj Y) :
    (integerStableOmegaHomEquiv X Y').symm
      (g ≫ integerStableOmegaEquivalence.functor.map b) =
        (integerStableOmegaHomEquiv X Y).symm g ≫ b := by
  apply (integerStableOmegaHomEquiv X Y').injective
  rw [Equiv.apply_symm_apply, integerStableOmegaHomEquiv_target, Equiv.apply_symm_apply]

/-- The Ω restriction uses every original group and map on the same original level-Ho objects. -/
def integerStablePiOmegaFunctor (q : ℤ) : omegaHoObjects.FullSubcategory ⥤ GrpCat.{v} :=
  omegaHoObjects.ι ⋙ integerStablePiHoFunctor.{u, v} q

/-- The original level projection and R-after-T functor retain their full source identity. -/
theorem reflectionHoFunctor_original : H ⋙ reflectionHoFunctor.{u, v} =
    reflectionFunctor ⋙ H :=
  Localization.Construction.fac (reflectionFunctor ⋙ H)
    (Functor.CoaugmentedLocalization.inverts (weakEquivalences Carrier.{u, v}) reflectionFunctor
      (fun ⦃X Y⦄ f hf => reflection_preservesLevelWeak (X := X) (Y := Y) f hf))

/-- The complete Ω source functor and integer restriction give the original RT integer functor. -/
theorem integerStablePiOmegaFunctor_source (q : ℤ) :
    originalIntegerLocalization ⋙ integerStablePiOmegaFunctor.{u, v} q =
      reflectionFunctor ⋙ integerStablePiFunctor q := by
  change (H ⋙ reflectionHoFunctor) ⋙ integerStablePiHoFunctor q = _
  calc
    _ = (reflectionFunctor ⋙ H) ⋙ integerStablePiHoFunctor q :=
      congrArg (fun F => F ⋙ integerStablePiHoFunctor q) reflectionHoFunctor_original
    _ = reflectionFunctor ⋙ (H ⋙ integerStablePiHoFunctor q) := rfl
    _ = reflectionFunctor ⋙ integerStablePiFunctor q :=
      congrArg (fun F => reflectionFunctor ⋙ F) (integerStablePiHoFunctor_original q)

/-- The full Ω equivalence followed by integer restriction retains every original RT group map. -/
theorem integerStableOmegaPiFunctor_source (q : ℤ) :
    integerStableProjection ⋙
      (integerStableOmegaEquivalence.functor ⋙ integerStablePiOmegaFunctor.{u, v} q) =
        reflectionFunctor ⋙ integerStablePiFunctor q := by
  calc
    _ = (integerStableProjection ⋙ integerStableOmegaEquivalence.functor) ⋙
        integerStablePiOmegaFunctor q := rfl
    _ = originalIntegerLocalization ⋙ integerStablePiOmegaFunctor q :=
      congrArg (fun F => F ⋙ integerStablePiOmegaFunctor q)
        integerStableOmegaEquivalence_sourceFunctor
    _ = _ := integerStablePiOmegaFunctor_source q

/-- The complete RT integer unit gives both full comparison functions on the localization. -/
def integerStableOmegaPiNatIso (q : ℤ) : integerStablePiStableFunctor.{u, v} q ≅
    integerStableOmegaEquivalence.functor ⋙ integerStablePiOmegaFunctor q := by
  let _ : Localization.Lifting integerStableProjection integerPiStarEquivalences
      (integerStablePiFunctor q) (integerStablePiStableFunctor q) :=
    ⟨eqToIso (integerStablePiStableFunctor_original q)⟩
  let _ : Localization.Lifting integerStableProjection integerPiStarEquivalences
      (reflectionFunctor ⋙ integerStablePiFunctor q)
      (integerStableOmegaEquivalence.functor ⋙ integerStablePiOmegaFunctor q) :=
    ⟨eqToIso (integerStableOmegaPiFunctor_source q)⟩
  exact Localization.liftNatIso integerStableProjection integerPiStarEquivalences
    (integerStablePiFunctor q) (reflectionFunctor ⋙ integerStablePiFunctor q)
    (integerStablePiStableFunctor q)
    (integerStableOmegaEquivalence.functor ⋙ integerStablePiOmegaFunctor q)
    (reflectionUnitIntegerPiNatIso q)

/-- Each entire original forward integer comparison is the original two-map RT unit image. -/
theorem integerStableOmegaPiNatIso_hom_app (q : ℤ) (X : Carrier.{u, v}) :
    (integerStableOmegaPiNatIso q).hom.app (integerStableProjection.obj X) =
      (reflectionUnitIntegerPiIso q X).hom := by
  unfold integerStableOmegaPiNatIso
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (𝟙 ((integerStablePiFunctor q).obj X)) ≫
    (reflectionUnitIntegerPiIso q X).hom ≫
      (𝟙 ((integerStablePiFunctor q).obj (reflectionFunctor.obj X))) = _
  rw [Category.id_comp, Category.comp_id]

/-- Each entire original inverse integer comparison retains both original RT inverse functions. -/
theorem integerStableOmegaPiNatIso_inv_app (q : ℤ) (X : Carrier.{u, v}) :
    (integerStableOmegaPiNatIso q).inv.app (integerStableProjection.obj X) =
      (reflectionUnitIntegerPiIso q X).inv := by
  unfold integerStableOmegaPiNatIso
  rw [Localization.liftNatIso_inv, Localization.liftNatTrans_app]
  change (𝟙 ((integerStablePiFunctor q).obj (reflectionFunctor.obj X))) ≫
    (reflectionUnitIntegerPiIso q X).inv ≫ (𝟙 ((integerStablePiFunctor q).obj X)) = _
  rw [Category.id_comp, Category.comp_id]

/-- Every integer-localization arrow retains the entire forward original RT integer naturality. -/
theorem integerStableOmegaPiNatIso_naturality (q : ℤ)
    {X Y : IntegerStableHomotopyCategory.{u, v}} (f : X ⟶ Y) :
    (integerStablePiStableFunctor q).map f ≫ (integerStableOmegaPiNatIso q).hom.app Y =
      (integerStableOmegaPiNatIso q).hom.app X ≫
        (integerStablePiOmegaFunctor q).map (integerStableOmegaEquivalence.functor.map f) :=
  (integerStableOmegaPiNatIso q).hom.naturality f

/-- Every integer-localization arrow retains the full inverse original RT integer naturality. -/
theorem integerStableOmegaPiNatIso_inverse_naturality (q : ℤ)
    {X Y : IntegerStableHomotopyCategory.{u, v}} (f : X ⟶ Y) :
    (integerStablePiOmegaFunctor q).map (integerStableOmegaEquivalence.functor.map f) ≫
      (integerStableOmegaPiNatIso q).inv.app Y =
      (integerStableOmegaPiNatIso q).inv.app X ≫ (integerStablePiStableFunctor q).map f :=
  (integerStableOmegaPiNatIso q).inv.naturality f

end PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStableLocalizationGeometry
