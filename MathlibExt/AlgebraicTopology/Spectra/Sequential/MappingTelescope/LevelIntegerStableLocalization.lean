/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStableLocalization

/-!
# Original level homotopy and integer localization

The original level projection factors through the integer localization
because each level equivalence satisfies the original integer tests.
The complete functor retains original arrows and their formal inverses.
Both original RT and native Q/K units become natural isomorphisms after
this projection. The genuine Ω factorization identifies its entire
localization class and every integer group functor.
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
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStableLocalizationGeometry
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.LevelIntegerStableLocalizationGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  originalIntegerLocalization_isLocalization
  reflectionOmegaHoFunctor_isOriginalIntegerHoLocalization

private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev H := toHomotopyCategory Carrier.{u, v}
private abbrev Ho := HomotopyCategory Carrier.{u, v}
private abbrev family : NativeStabilizationFamily.{u, v}
    (CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne.{u, v}) ℕ :=
  PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}

/-- Each original level equivalence is inverted by the original integer projection. -/
theorem integerStableProjection_invertsLevelWeak :
    (weakEquivalences Carrier.{u, v}).IsInvertedBy integerStableProjection :=
  fun _ _ f hf => integerPiStarEquivalences.Q_inverts f
    (levelWeak_le_integerPiStarEquivalences f hf)

/-- The actual localization construction factors the original level projection. -/
def levelToIntegerStableHo : Ho.{u, v} ⥤ IntegerStableHomotopyCategory.{u, v} :=
  Localization.Construction.lift integerStableProjection
    integerStableProjection_invertsLevelWeak

/-- The full source projection identity retains all original objects and maps. -/
theorem levelToIntegerStableHo_original : H ⋙ levelToIntegerStableHo.{u, v} =
    integerStableProjection :=
  Localization.Construction.fac integerStableProjection integerStableProjection_invertsLevelWeak

/-- Each original source object is unchanged by factoring through the level category. -/
theorem levelToIntegerStableHo_obj (X : Carrier.{u, v}) :
    levelToIntegerStableHo.obj (H.obj X) = integerStableProjection.obj X := rfl

/-- Each original source arrow retains its original integer-localization map. -/
theorem levelToIntegerStableHo_map {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    levelToIntegerStableHo.map (H.map f) = integerStableProjection.map f := by
  have h := Functor.congr_hom levelToIntegerStableHo_original f
  change levelToIntegerStableHo.map (H.map f) =
    (𝟙 (integerStableProjection.obj X)) ≫ integerStableProjection.map f ≫
      (𝟙 (integerStableProjection.obj Y)) at h
  simpa only [Category.id_comp, Category.comp_id] using h

/-- The full original weak-arrow isomorphism retains the same arrow in the integer localization. -/
theorem levelToIntegerStableHo_map_wIso {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences Carrier.{u, v} f) :
    levelToIntegerStableHo.mapIso (Localization.Construction.wIso f hf) =
      Localization.Construction.wIso f (levelWeak_le_integerPiStarEquivalences f hf) := by
  apply Iso.ext
  exact levelToIntegerStableHo_map f

/-- The inverse of each original level equivalence remains the inverse of that same source arrow. -/
theorem levelToIntegerStableHo_map_wIso_inv {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences Carrier.{u, v} f) :
    levelToIntegerStableHo.map (Localization.Construction.wIso f hf).inv =
      (Localization.Construction.wIso f (levelWeak_le_integerPiStarEquivalences f hf)).inv :=
  congrArg (fun e => e.inv) (levelToIntegerStableHo_map_wIso f hf)

/-- Every original integer group functor retains its full level-Ho object and map functions. -/
theorem levelToIntegerStableHo_integerFunctor (q : ℤ) :
    levelToIntegerStableHo ⋙ integerStablePiStableFunctor.{u, v} q =
      integerStablePiHoFunctor q := by
  apply Localization.Construction.uniq
  calc
    _ = (H ⋙ levelToIntegerStableHo) ⋙ integerStablePiStableFunctor q := rfl
    _ = integerStableProjection ⋙ integerStablePiStableFunctor q :=
      congrArg (fun F => F ⋙ integerStablePiStableFunctor q) levelToIntegerStableHo_original
    _ = integerStablePiFunctor q := integerStablePiStableFunctor_original q
    _ = H ⋙ integerStablePiHoFunctor q := (integerStablePiHoFunctor_original q).symm

/-- The original Ω factorization agrees on every level-Ho object and every level-Ho arrow. -/
theorem levelToIntegerStableHo_omegaFunctor :
    levelToIntegerStableHo ⋙ integerStableOmegaEquivalence.{u, v}.functor =
      reflectionOmegaHoFunctor := by
  apply Localization.Construction.uniq
  calc
    _ = (H ⋙ levelToIntegerStableHo) ⋙ integerStableOmegaEquivalence.functor := rfl
    _ = integerStableProjection ⋙ integerStableOmegaEquivalence.functor :=
      congrArg (fun F => F ⋙ integerStableOmegaEquivalence.functor)
        levelToIntegerStableHo_original
    _ = originalIntegerLocalization := integerStableOmegaEquivalence_sourceFunctor
    _ = H ⋙ reflectionOmegaHoFunctor := rfl

/-- The actual Ω equivalence inverse gives the complete original level-to-integer factorization. -/
def omegaIntegerStableFactorIso :
    reflectionOmegaHoFunctor.{u, v} ⋙ integerStableOmegaEquivalence.inverse ≅
      levelToIntegerStableHo :=
  Functor.isoWhiskerRight (eqToIso levelToIntegerStableHo_omegaFunctor).symm
      integerStableOmegaEquivalence.inverse ≪≫
    Functor.associator levelToIntegerStableHo integerStableOmegaEquivalence.functor
      integerStableOmegaEquivalence.inverse ≪≫
    Functor.isoWhiskerLeft levelToIntegerStableHo integerStableOmegaEquivalence.unitIso.symm ≪≫
    Functor.rightUnitor levelToIntegerStableHo

/-- The factorization keeps the actual original Ω-equivalence unit inverse at every object. -/
theorem omegaIntegerStableFactorIso_hom_app (X : Ho.{u, v}) :
    omegaIntegerStableFactorIso.hom.app X =
      integerStableOmegaEquivalence.inverse.map
          ((eqToIso levelToIntegerStableHo_omegaFunctor).inv.app X) ≫
        integerStableOmegaEquivalence.unitIso.inv.app (levelToIntegerStableHo.obj X) := by
  simp only [omegaIntegerStableFactorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Category.id_comp]
  change integerStableOmegaEquivalence.inverse.map
      ((eqToIso levelToIntegerStableHo_omegaFunctor).inv.app X) ≫
    (integerStableOmegaEquivalence.unitIso.inv.app (levelToIntegerStableHo.obj X) ≫
      𝟙 (levelToIntegerStableHo.obj X)) = _
  exact congrArg (fun f :
      integerStableOmegaEquivalence.inverse.obj
          (integerStableOmegaEquivalence.functor.obj (levelToIntegerStableHo.obj X)) ⟶
        levelToIntegerStableHo.obj X =>
      integerStableOmegaEquivalence.inverse.map
        ((eqToIso levelToIntegerStableHo_omegaFunctor).inv.app X) ≫ f)
    (Category.comp_id
      (integerStableOmegaEquivalence.unitIso.inv.app (levelToIntegerStableHo.obj X)))

/-- This same original functor categorically localizes the original integer image class. -/
theorem levelToIntegerStableHo_isOriginalIntegerLocalization :
    levelToIntegerStableHo.{u, v}.IsLocalization originalIntegerHoClass :=
  Functor.IsLocalization.of_equivalence_target reflectionOmegaHoFunctor originalIntegerHoClass
    levelToIntegerStableHo integerStableOmegaEquivalence.symm omegaIntegerStableFactorIso

/-- The original RT unit is inverted on every level-Ho object by the integer projection. -/
theorem reflectionHoUnit_integerStable_isIso (X : Ho.{u, v}) :
    IsIso (levelToIntegerStableHo.map (reflectionHoUnit.app X)) := by
  rcases X with ⟨⟨X⟩⟩
  change IsIso (levelToIntegerStableHo.map (reflectionHoUnit.app (H.obj X)))
  have h : levelToIntegerStableHo.map (reflectionHoUnit.app (H.obj X)) =
      integerStableProjection.map (reflectionUnit.app X) :=
    (levelToIntegerStableHo.congr_map (reflectionHoUnit_app X)).trans
      (levelToIntegerStableHo_map (reflectionUnit.app X))
  exact h.symm ▸ (Localization.Construction.wIso (reflectionUnit.app X)
    (reflectionUnit_integerPiStar X)).isIso_hom

/-- Both full RT-unit functions are retained after the original integer projection. -/
def reflectionHoIntegerStableUnitIso (X : Ho.{u, v}) :
    levelToIntegerStableHo.obj X ≅ levelToIntegerStableHo.obj (reflectionHoFunctor.obj X) := by
  let _ := reflectionHoUnit_integerStable_isIso X
  exact asIso (levelToIntegerStableHo.map (reflectionHoUnit.app X))

/-- The whole RT-unit forward function is the original descended unit map. -/
theorem reflectionHoIntegerStableUnitIso_hom (X : Ho.{u, v}) :
    (reflectionHoIntegerStableUnitIso X).hom =
      levelToIntegerStableHo.map (reflectionHoUnit.app X) := rfl

/-- Every original source input retains the same complete original two-map unit isomorphism. -/
theorem reflectionHoIntegerStableUnitIso_original (X : Carrier.{u, v}) :
    reflectionHoIntegerStableUnitIso (H.obj X) =
      Localization.Construction.wIso (reflectionUnit.app X)
        (reflectionUnit_integerPiStar X) := by
  apply Iso.ext
  exact (levelToIntegerStableHo.congr_map (reflectionHoUnit_app X)).trans
    (levelToIntegerStableHo_map (reflectionUnit.app X))

/-- The inverse retains the actual formal inverse of that same original source RT unit. -/
theorem reflectionHoIntegerStableUnitIso_original_inv (X : Carrier.{u, v}) :
    (reflectionHoIntegerStableUnitIso (H.obj X)).inv =
      (Localization.Construction.wIso (reflectionUnit.app X)
        (reflectionUnit_integerPiStar X)).inv :=
  congrArg (fun e => e.inv) (reflectionHoIntegerStableUnitIso_original X)

/-- The complete original RT unit is a natural isomorphism on all level-Ho arrows. -/
def reflectionHoIntegerStableNatIso : levelToIntegerStableHo.{u, v} ≅
    reflectionHoFunctor ⋙ levelToIntegerStableHo :=
  NatIso.ofComponents reflectionHoIntegerStableUnitIso (fun f => by
    rw [reflectionHoIntegerStableUnitIso_hom, reflectionHoIntegerStableUnitIso_hom]
    exact (Functor.whiskerRight reflectionHoUnit levelToIntegerStableHo).naturality f)

/-- Its entire forward transformation retains precisely the original unit image. -/
theorem reflectionHoIntegerStableNatIso_hom :
    reflectionHoIntegerStableNatIso.{u, v}.hom =
      Functor.whiskerRight reflectionHoUnit levelToIntegerStableHo := by
  apply NatTrans.ext
  funext X
  exact reflectionHoIntegerStableUnitIso_hom X

/-- Every arbitrary level-Ho arrow retains the complete forward RT naturality square. -/
theorem reflectionHoIntegerStableNatIso_naturality {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    levelToIntegerStableHo.map f ≫ reflectionHoIntegerStableNatIso.hom.app Y =
      reflectionHoIntegerStableNatIso.hom.app X ≫
        levelToIntegerStableHo.map (reflectionHoFunctor.map f) :=
  reflectionHoIntegerStableNatIso.hom.naturality f

/-- Every arbitrary level-Ho arrow retains the complete inverse RT naturality square. -/
theorem reflectionHoIntegerStableNatIso_inverse_naturality {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    levelToIntegerStableHo.map (reflectionHoFunctor.map f) ≫
      reflectionHoIntegerStableNatIso.inv.app Y =
      reflectionHoIntegerStableNatIso.inv.app X ≫ levelToIntegerStableHo.map f :=
  reflectionHoIntegerStableNatIso.inv.naturality f

/-- Both original native Q/K unit functions are retained through the original RT comparison. -/
def nativeQKHoIntegerStableNatIso : levelToIntegerStableHo.{u, v} ≅
    NativeK.localReplacementHo family ⋙ levelToIntegerStableHo :=
  reflectionHoIntegerStableNatIso ≪≫
    (Functor.isoWhiskerRight nativeQKRTHoIso levelToIntegerStableHo).symm

/-- The complete forward native comparison retains the original RT unit and Q/K-to-RT inverse. -/
theorem nativeQKHoIntegerStableNatIso_hom_app (X : Ho.{u, v}) :
    nativeQKHoIntegerStableNatIso.hom.app X =
      levelToIntegerStableHo.map (reflectionHoUnit.app X) ≫
        levelToIntegerStableHo.map (nativeQKRTHoIso.inv.app X) := rfl

/-- The entire forward native comparison is the actual original Q-inverse/K-unit image. -/
theorem nativeQKHoIntegerStableNatIso_originalUnit (X : Ho.{u, v}) :
    nativeQKHoIntegerStableNatIso.hom.app X =
      levelToIntegerStableHo.map ((NativeK.localReplacementHoUnit family).app X) := by
  rw [nativeQKHoIntegerStableNatIso_hom_app, ← Functor.map_comp]
  apply levelToIntegerStableHo.congr_map
  apply (cancel_mono (nativeQKRTHoIso.hom.app X)).mp
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact (congr_app nativeQKRTHoIso_wholeUnit X).symm

/-- Every actual native unit is invertible after the original integer projection. -/
theorem nativeQKHoUnit_integerStable_isIso (X : Ho.{u, v}) :
    IsIso (levelToIntegerStableHo.map ((NativeK.localReplacementHoUnit family).app X)) := by
  rw [← nativeQKHoIntegerStableNatIso_originalUnit]
  exact (nativeQKHoIntegerStableNatIso.app X).isIso_hom

/-- Every arbitrary level-Ho arrow retains the full forward native unit naturality. -/
theorem nativeQKHoIntegerStableNatIso_naturality {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    levelToIntegerStableHo.map f ≫ nativeQKHoIntegerStableNatIso.hom.app Y =
      nativeQKHoIntegerStableNatIso.hom.app X ≫
        levelToIntegerStableHo.map ((NativeK.localReplacementHo family).map f) :=
  nativeQKHoIntegerStableNatIso.hom.naturality f

/-- Every arbitrary level-Ho arrow retains the full inverse native unit naturality. -/
theorem nativeQKHoIntegerStableNatIso_inverse_naturality {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    levelToIntegerStableHo.map ((NativeK.localReplacementHo family).map f) ≫
      nativeQKHoIntegerStableNatIso.inv.app Y =
      nativeQKHoIntegerStableNatIso.inv.app X ≫ levelToIntegerStableHo.map f :=
  nativeQKHoIntegerStableNatIso.inv.naturality f

/-- The original native image class retains the same full native K-local-test source arrows. -/
def nativeOriginalLocalTestHoClass : MorphismProperty Ho.{u, v} :=
  (NativeK.localTestEquivalences family).map H

/-- Both image classes retain precisely their original all-source integer testing arrows. -/
theorem nativeOriginalLocalTestHoClass_eq_integer :
    nativeOriginalLocalTestHoClass.{u, v} = originalIntegerHoClass := by
  unfold nativeOriginalLocalTestHoClass originalIntegerHoClass
  rw [nativeLocalTestEquivalences_eq_originalIntegerPiStar]

/-- The original level projection localizes the original native K-local-test image class. -/
theorem levelToIntegerStableHo_isNativeLocalTestHoLocalization :
    levelToIntegerStableHo.{u, v}.IsLocalization nativeOriginalLocalTestHoClass := by
  rw [nativeOriginalLocalTestHoClass_eq_integer]
  exact levelToIntegerStableHo_isOriginalIntegerLocalization

end PointedCGWH.SequentialSpectrum.MappingTelescope.LevelIntegerStableLocalizationGeometry
