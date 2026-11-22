/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.LocalizationBifibrantResolution
import
  MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStableAdjunction

/-!
# Original integer homotopy detects all ordinary level-homotopy arrows

The genuine level model and fundamental lemma supply actual bifibrant
representatives of every ordinary homotopy-category arrow. Their full
resolution maps and left/right homotopy quotient functions are retained.
The same original integer group functors therefore detect the original
RT and native Q/K images on every arrow. The original integer image class
is exactly this all-degree class, with the original units unchanged.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.LocalizationBifibrantResolution
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.NativeKRTComparisonGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.NativeIntegerLocalizationGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStableLocalizationGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.LevelIntegerStableLocalizationGeometry
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoDetectionGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev H := toHomotopyCategory Carrier.{u, v}
private abbrev Ho := HomotopyCategory Carrier.{u, v}
private abbrev family : NativeStabilizationFamily.{u, v}
    (CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne.{u, v}) ℕ :=
  PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}

/-- The full bifibrant quotient object uses the genuine original level model resolutions. -/
def originalBifibrantHoObject (X : Ho.{u, v}) : BifibrantObject.HoCat Carrier.{u, v} :=
  BifibrantObject.toHoCat.obj (bifibrantObject X.as.obj)

/-- Both original level-resolution functions identify the bifibrant image with the given object. -/
def originalBifibrantHoIso (X : Ho.{u, v}) :
    H.obj (bifibrantObj X.as.obj) ≅ X := by
  rcases X with ⟨⟨X⟩⟩
  exact resolutionIso H X

/-- The actual fundamental lemma chooses a strict map representing every ordinary-Ho input. -/
def originalHoBifibrantRepresentative {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    bifibrantObj X.as.obj ⟶ bifibrantObj Y.as.obj := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact representative H f

/-- Every whole chosen representative retains both original source and target resolution maps. -/
theorem originalHoBifibrantRepresentative_map {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    H.map (originalHoBifibrantRepresentative f) =
      (originalBifibrantHoIso X).hom ≫ f ≫ (originalBifibrantHoIso Y).inv := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact representative_map H f

/-- Both resolution maps and the strict representative return the entire given original Ho arrow. -/
theorem originalHoBifibrantRepresentative_reconstruction {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (originalBifibrantHoIso X).inv ≫ H.map (originalHoBifibrantRepresentative f) ≫
      (originalBifibrantHoIso Y).hom = f := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact representative_reconstruction H f

/-- The same actual resolution functions give an isomorphism of the complete original arrows. -/
def originalHoBifibrantArrowIso {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    Arrow.mk (H.map (originalHoBifibrantRepresentative f)) ≅ Arrow.mk f :=
  Arrow.isoMk (originalBifibrantHoIso X) (originalBifibrantHoIso Y) (by
    let eX := originalBifibrantHoIso X
    let eY := originalBifibrantHoIso Y
    have cancel : (f ≫ eY.inv) ≫ eY.hom = f :=
      (Category.assoc f eY.inv eY.hom).trans
        ((congrArg (fun g : Y ⟶ Y => f ≫ g) eY.inv_hom_id).trans (Category.comp_id f))
    have h : (eX.hom ≫ f ≫ eY.inv) ≫ eY.hom = eX.hom ≫ f :=
      (Category.assoc eX.hom (f ≫ eY.inv) eY.hom).trans
        (congrArg (fun g : X ⟶ Y => eX.hom ≫ g) cancel)
    exact ((congrArg
      (fun g : H.obj (bifibrantObj X.as.obj) ⟶ H.obj (bifibrantObj Y.as.obj) => g ≫ eY.hom)
      (originalHoBifibrantRepresentative_map f)).trans h).symm)

/-- The whole source function of the Arrow isomorphism is the actual original resolution hom. -/
theorem originalHoBifibrantArrowIso_hom_left {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (originalHoBifibrantArrowIso f).hom.left = (originalBifibrantHoIso X).hom := rfl

/-- The whole target function of the Arrow isomorphism is the actual original resolution hom. -/
theorem originalHoBifibrantArrowIso_hom_right {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (originalHoBifibrantArrowIso f).hom.right = (originalBifibrantHoIso Y).hom := rfl

/-- The full inverse source function is the same original inverse resolution function. -/
theorem originalHoBifibrantArrowIso_inv_left {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (originalHoBifibrantArrowIso f).inv.left = (originalBifibrantHoIso X).inv := rfl

/-- The full inverse target function is the same original inverse resolution function. -/
theorem originalHoBifibrantArrowIso_inv_right {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (originalHoBifibrantArrowIso f).inv.right = (originalBifibrantHoIso Y).inv := rfl

/-- The full Hom functions retain the original bifibrant quotient and both resolution functions. -/
def originalBifibrantHoHomEquiv (X Y : Ho.{u, v}) :
    (originalBifibrantHoObject X ⟶ originalBifibrantHoObject Y) ≃ (X ⟶ Y) := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact bifibrantHomEquiv H X Y

/-- Every original quotient representative has its actual two-sided resolution formula. -/
theorem originalBifibrantHoHomEquiv_apply (X Y : Ho.{u, v})
    (g : bifibrantObj X.as.obj ⟶ bifibrantObj Y.as.obj) :
    originalBifibrantHoHomEquiv X Y
      (BifibrantObject.toHoCat.map (BifibrantObject.homMk g)) =
        (originalBifibrantHoIso X).inv ≫ H.map g ≫ (originalBifibrantHoIso Y).hom := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact bifibrantHomEquiv_apply H X Y g

/-- The entire inverse is the actual chosen representative in the same bifibrant quotient. -/
theorem originalBifibrantHoHomEquiv_symm_apply {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (originalBifibrantHoHomEquiv X Y).symm f =
      BifibrantObject.toHoCat.map
        (BifibrantObject.homMk (originalHoBifibrantRepresentative f)) := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact (representative_quotient H f).symm

/-- Every arbitrary ordinary-Ho source arrow retains the whole inverse quotient naturality. -/
theorem originalBifibrantHoHomEquiv_source_symm {X X' Y : Ho.{u, v}}
    (a : X' ⟶ X) (f : X ⟶ Y) :
    (originalBifibrantHoHomEquiv X' Y).symm (a ≫ f) =
      (originalBifibrantHoHomEquiv X' X).symm a ≫
        (originalBifibrantHoHomEquiv X Y).symm f := by
  rcases X with ⟨⟨X⟩⟩
  rcases X' with ⟨⟨X'⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact bifibrantHomEquiv_source_symm H a f

/-- Every arbitrary ordinary-Ho target arrow retains the whole inverse quotient naturality. -/
theorem originalBifibrantHoHomEquiv_target_symm {X Y Y' : Ho.{u, v}}
    (b : Y ⟶ Y') (f : X ⟶ Y) :
    (originalBifibrantHoHomEquiv X Y').symm (f ≫ b) =
      (originalBifibrantHoHomEquiv X Y).symm f ≫
        (originalBifibrantHoHomEquiv Y Y').symm b :=
  originalBifibrantHoHomEquiv_source_symm f b

/-- Each arbitrary source action retains the complete forward function of the quotient. -/
theorem originalBifibrantHoHomEquiv_source {X X' Y : Ho.{u, v}}
    (a : X' ⟶ X) (g : originalBifibrantHoObject X ⟶ originalBifibrantHoObject Y) :
    originalBifibrantHoHomEquiv X' Y ((originalBifibrantHoHomEquiv X' X).symm a ≫ g) =
      a ≫ originalBifibrantHoHomEquiv X Y g := by
  rcases X with ⟨⟨X⟩⟩
  rcases X' with ⟨⟨X'⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  exact (bifibrantHomEquiv_comp H ((bifibrantHomEquiv H X' X).symm a) g).trans
    (congrArg (fun h => h ≫ bifibrantHomEquiv H X Y g)
      ((bifibrantHomEquiv H X' X).apply_symm_apply a))

/-- Each arbitrary target action retains the complete forward function of the quotient. -/
theorem originalBifibrantHoHomEquiv_target {X Y Y' : Ho.{u, v}}
    (b : Y ⟶ Y') (g : originalBifibrantHoObject X ⟶ originalBifibrantHoObject Y) :
    originalBifibrantHoHomEquiv X Y' (g ≫ (originalBifibrantHoHomEquiv Y Y').symm b) =
      originalBifibrantHoHomEquiv X Y g ≫ b := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  rcases Y' with ⟨⟨Y'⟩⟩
  exact (bifibrantHomEquiv_comp H g ((bifibrantHomEquiv H Y Y').symm b)).trans
    (congrArg (fun h => bifibrantHomEquiv H X Y g ≫ h)
      ((bifibrantHomEquiv H Y Y').apply_symm_apply b))

/-- Both full Hom functions return every original quotient arrow. -/
theorem originalBifibrantHoHomEquiv_left_triangle (X Y : Ho.{u, v})
    (g : originalBifibrantHoObject X ⟶ originalBifibrantHoObject Y) :
    (originalBifibrantHoHomEquiv X Y).symm (originalBifibrantHoHomEquiv X Y g) = g :=
  (originalBifibrantHoHomEquiv X Y).symm_apply_apply g

/-- Both full Hom functions return every arbitrary ordinary-Ho arrow. -/
theorem originalBifibrantHoHomEquiv_right_triangle {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    originalBifibrantHoHomEquiv X Y ((originalBifibrantHoHomEquiv X Y).symm f) = f :=
  (originalBifibrantHoHomEquiv X Y).apply_symm_apply f

/-- Each integer resolution isomorphism uses the complete original descended group functor. -/
def originalIntegerBifibrantIso (q : ℤ) (X : Ho.{u, v}) :
    (integerStablePiHoFunctor q).obj (H.obj (bifibrantObj X.as.obj)) ≅
      (integerStablePiHoFunctor q).obj X :=
  (integerStablePiHoFunctor q).mapIso (originalBifibrantHoIso X)

/-- Every original integer forward resolution function is the actual original Ho-map image. -/
theorem originalIntegerBifibrantIso_hom (q : ℤ) (X : Ho.{u, v}) :
    (originalIntegerBifibrantIso q X).hom =
      (integerStablePiHoFunctor q).map (originalBifibrantHoIso X).hom := rfl

/-- Every original integer inverse resolution function is the actual original inverse Ho image. -/
theorem originalIntegerBifibrantIso_inv (q : ℤ) (X : Ho.{u, v}) :
    (originalIntegerBifibrantIso q X).inv =
      (integerStablePiHoFunctor q).map (originalBifibrantHoIso X).inv := rfl

/-- Every integer map of an arbitrary Ho arrow retains the entire representative conjugation. -/
theorem originalBifibrantIntegerRepresentative_map (q : ℤ) {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (integerStablePiHoFunctor q).map (H.map (originalHoBifibrantRepresentative f)) =
      (originalIntegerBifibrantIso q X).hom ≫ (integerStablePiHoFunctor q).map f ≫
        (originalIntegerBifibrantIso q Y).inv := by
  change (integerStablePiHoFunctor q).map (H.map (originalHoBifibrantRepresentative f)) =
    (integerStablePiHoFunctor q).map (originalBifibrantHoIso X).hom ≫
      (integerStablePiHoFunctor q).map f ≫
        (integerStablePiHoFunctor q).map (originalBifibrantHoIso Y).inv
  simpa only [Functor.map_comp] using
    (integerStablePiHoFunctor q).congr_map (originalHoBifibrantRepresentative_map f)

/-- Every original all-degree group function is reconstructed from the whole original strict map. -/
theorem originalBifibrantIntegerRepresentative_reconstruction
    (q : ℤ) {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (originalIntegerBifibrantIso q X).inv ≫
      (integerStablePiFunctor q).map (originalHoBifibrantRepresentative f) ≫
        (originalIntegerBifibrantIso q Y).hom = (integerStablePiHoFunctor q).map f := by
  let P := integerStablePiHoFunctor q
  let eX := originalIntegerBifibrantIso q X
  let eY := originalIntegerBifibrantIso q Y
  let g := originalHoBifibrantRepresentative f
  have hm : P.map (H.map g) = (integerStablePiFunctor q).map g :=
    integerStablePiHoFunctor_map q g
  have h : eX.inv ≫ P.map (H.map g) ≫ eY.hom = P.map f :=
    (congrArg
      (fun m : P.obj (H.obj (bifibrantObj X.as.obj)) ⟶
          P.obj (H.obj (bifibrantObj Y.as.obj)) => eX.inv ≫ m ≫ eY.hom)
      (originalBifibrantIntegerRepresentative_map q f)).trans
        ((Iso.homCongr eX eY).apply_symm_apply (P.map f))
  exact (congrArg
    (fun m : P.obj (H.obj (bifibrantObj X.as.obj)) ⟶
        P.obj (H.obj (bifibrantObj Y.as.obj)) => eX.inv ≫ m ≫ eY.hom) hm.symm).trans h

/-- Every original positive-tail quotient representative retains the actual strict spectrum map. -/
theorem originalBifibrantIntegerRepresentative_map_apply (q : ℤ)
    {X Y : Ho.{u, v}} (f : X ⟶ Y) (n : ℕ)
    (a : PointedCGWH.piN (DiagonalHomotopyGeometry.integerTailPositiveIndex q + n + 1)
      ((bifibrantObj X.as.obj).level (DiagonalHomotopyGeometry.integerTailLevel q + n))) :
    ((integerStablePiHoFunctor q).map (H.map (originalHoBifibrantRepresentative f))).hom
      (GrpCat.FilteredColimits.G.mk
        ((DiagonalHomotopyGeometry.integerDiagonalDiagramFunctor q).obj (bifibrantObj X.as.obj))
          ⟨n, a⟩) =
      GrpCat.FilteredColimits.G.mk
        ((DiagonalHomotopyGeometry.integerDiagonalDiagramFunctor q).obj (bifibrantObj Y.as.obj))
          ⟨n, PointedCGWH.piNMap (DiagonalHomotopyGeometry.integerTailPositiveIndex q + n + 1)
            (PointedCGWH.SequentialSpectrum.levelMap (originalHoBifibrantRepresentative f)
              (DiagonalHomotopyGeometry.integerTailLevel q + n)) a⟩ :=
  integerStablePiHoFunctor_map_apply q (originalHoBifibrantRepresentative f) n a

private instance integerPiHoEquivalences_respectsIso :
    integerPiHoEquivalences.{u, v}.RespectsIso := by
  unfold integerPiHoEquivalences
  infer_instance

/-- The original all-degree Ho tests are exactly the actual bifibrant representative tests. -/
theorem integerPiHoEquivalences_iff_bifibrantRepresentative
    {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    integerPiHoEquivalences f ↔
      integerPiStarEquivalences (originalHoBifibrantRepresentative f) :=
  ((integerPiHoEquivalences.arrow_mk_iso_iff (originalHoBifibrantArrowIso f)).symm).trans
    (integerPiHoEquivalences_projected (originalHoBifibrantRepresentative f))

/-- Genuine bifibrant representatives extend the original RT detector to every ordinary-Ho arrow. -/
theorem integerPiHoEquivalences_iff_reflection_isIso {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    integerPiHoEquivalences f ↔ IsIso (reflectionHoFunctor.map f) := by
  let g := originalHoBifibrantRepresentative f
  have h : integerPiStarEquivalences g ↔ IsIso (reflectionHoFunctor.map (H.map g)) := by
    rw [reflectionHoFunctor_map]
    exact (integerPiStar_iff_reflectionLevelWeak g).trans
      (weakEquivalence_iff_isIso_toHomotopyCategory_map (reflectionFunctor.map g))
  exact (integerPiHoEquivalences_iff_bifibrantRepresentative f).trans
    (h.trans (((MorphismProperty.isomorphisms Ho.{u, v}).inverseImage
      reflectionHoFunctor).arrow_mk_iso_iff (originalHoBifibrantArrowIso f)))

/-- The same original native Q/K functor detects every integer test on every ordinary-Ho arrow. -/
theorem integerPiHoEquivalences_iff_nativeQK_isIso {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    integerPiHoEquivalences f ↔ IsIso ((NativeK.localReplacementHo family).map f) :=
  (integerPiHoEquivalences_iff_reflection_isIso f).trans
    (NatIso.isIso_map_iff nativeQKRTHoIso f).symm

/-- Every original ordinary-Ho source and Omega target retains the full Hom test function. -/
theorem integerPiHoEquivalences_iff_originalOmegaHomTests
    {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    integerPiHoEquivalences f ↔
      ∀ Z, omegaHoObjects Z → Function.Bijective (fun g : Y ⟶ Z => f ≫ g) :=
  (integerPiHoEquivalences_iff_reflection_isIso f).trans
    (reflectionHoMap_isIso_iff_omegaHomTests f)

/-- The original integer image class equals the full all-degree Ho class on every actual arrow. -/
theorem originalIntegerHoClass_iff_integerPiHo {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    originalIntegerHoClass f ↔ integerPiHoEquivalences f := by
  constructor
  · intro hf
    rcases hf with ⟨X', Y', g, hg, ⟨e⟩⟩
    exact (integerPiHoEquivalences.arrow_mk_iso_iff e).mp
      ((integerPiHoEquivalences_projected g).mpr hg)
  · intro hf
    exact ⟨bifibrantObj X.as.obj, bifibrantObj Y.as.obj, originalHoBifibrantRepresentative f,
      (integerPiHoEquivalences_iff_bifibrantRepresentative f).mp hf,
      ⟨originalHoBifibrantArrowIso f⟩⟩

/-- The complete original image and degree-testing classes retain all source and target inputs. -/
theorem originalIntegerHoClass_eq_integerPiHo :
    originalIntegerHoClass.{u, v} = integerPiHoEquivalences := by
  funext X Y f
  exact propext (originalIntegerHoClass_iff_integerPiHo f)

/-- The entire original native K-local-test image class is the same all-degree Ho testing class. -/
theorem nativeOriginalLocalTestHoClass_eq_integerPiHo :
    nativeOriginalLocalTestHoClass.{u, v} = integerPiHoEquivalences :=
  nativeOriginalLocalTestHoClass_eq_integer.trans originalIntegerHoClass_eq_integerPiHo

/-- The actual original integer projection localizes the full all-degree ordinary-Ho class. -/
theorem levelToIntegerStableHo_isIntegerPiHoLocalization :
    levelToIntegerStableHo.{u, v}.IsLocalization integerPiHoEquivalences := by
  rw [← originalIntegerHoClass_eq_integerPiHo]
  exact levelToIntegerStableHo_isOriginalIntegerLocalization

/-- The same original RT unit has an invertible image under the original native Q/K functor. -/
theorem reflectionHoUnit_nativeQKMap_isIso (X : Ho.{u, v}) :
    IsIso ((NativeK.localReplacementHo family).map (reflectionHoUnit.app X)) :=
  (integerPiHoEquivalences_iff_nativeQK_isIso (reflectionHoUnit.app X)).mp
    (reflectionHoUnit_integerPiHo X)

/-- The same original Q-inverse/K-unit has an invertible image under the original RT functor. -/
theorem nativeQKHoUnit_reflectionMap_isIso (X : Ho.{u, v}) :
    IsIso (reflectionHoFunctor.map ((NativeK.localReplacementHoUnit family).app X)) :=
  (integerPiHoEquivalences_iff_reflection_isIso
    ((NativeK.localReplacementHoUnit family).app X)).mp (nativeQKHoUnit_integerPiHo X)

end PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoDetectionGeometry
