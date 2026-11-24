/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeSpectrumHoClosedModels

/-!
# Canonical unit comparison to the original native nonconnective K spectrum

The localizing functor extends the actual full coherent IK invariant.
Its source equivalence is a whole natural equivalence on Catperf.
The comparison map curries the image of the original complete motive
end evaluation, precomposes with the original sphere K class and native
stage-zero tower inclusion, and uses the same source equivalence at A.

The target is always the original S/loop/Sigma tower colimit. Neither
that spectrum nor its maps are defined from the motive comparison.
The spectrum equivalence of BGT Theorem 9.8 is a separate Wanted result.

Sources: BGT arXiv:1001.2282v4 Sections 8.3/9.2, Theorem 9.8;
HSS Sections 2.2/3.1--3.4. Native source pins and licenses remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeIKCorepresentabilityModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open MathlibExt.SpectraSource
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels StableInfinityMappingSpaces
open StableInfinityFilteredColimits NativeDiagramFamilies NativeSpectrumConeSources NativeSpectrumBoundarySources
open NativeKParametrizedSource NativeSpectraSimplicialSource NativeEnrichedSpectrumReplacements
open NativeDerivedSpectrumModels StableSpectraInfinitySource StableInfinityKSpectra
open NativeMotivePresheafSources NativeMotiveGenerators NativeMotiveLocalizationModels
open NativeMotiveTensorModels NativeSpectrumHoClosedModels NativeK0ComparisonModels
open NativeIKFunctorSources BGTNativeNonconnectiveModels NativeCompactSourceModels StableInfinityMappingSpaceMaps
open NativeSpectralPresheafModels
open scoped Simplicial Cardinal MonoidalClosed

def perfectSourceObject {A : StableCategoryEnrichment} {k : Cardinal.{0}}
    (T : SpectralCompactSource A k) (c : T.index) : PerfectInfinityCategory.{0} :=
  letI := A.enrichment
  letI := T.skeleton.enrichment
  ⟨T.represented c, T.skeleton.perfect c⟩

/-- The compact source object is the actual Spomega model, with full exact equivalences. -/
structure SphereIndexSource {A : StableCategoryEnrichment} {k : Cardinal.{0}}
    (T : SpectralCompactSource A k) (S : SpectrumInfinitySource) where
  source : CompactSpectraSource S
  index : T.index
  toSource : ExactFunctor (T.represented index) source.small.toStableInfinityCategory
  fromSource : ExactFunctor source.small.toStableInfinityCategory (T.represented index)
  source_inverse : NaturallyEquivalentMaps (toSource.map ≫ fromSource.map) (𝟙 (T.represented index).toSSet)
  target_inverse : NaturallyEquivalentMaps (fromSource.map ≫ toSource.map) (𝟙 source.small.toStableInfinityCategory.toSSet)

def SphereIndexSource.sphere {A : StableCategoryEnrichment} {k : Cardinal.{0}}
    {T : SpectralCompactSource A k} {S : SpectrumInfinitySource} (P : SphereIndexSource T S) :
    (T.represented P.index).toSSet _⦋0⦌ := P.fromSource.map.app (op ⦋0⦌) P.source.sphere

variable {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource}
    {Z : SpectrumZeroSource S} {ki : UncountableRegularCardinal}
    {K : ParametrizedKSource A N} {R : EnrichedSpectrumReplacements N S}
    {L : SpectrumCoherentLocalization N S} {P : SigmaKappaSystem ki}
    {B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C}
    (I : NativeIKSource K R L P B)
    {km : UncountableRegularCardinal} {T : SpectralCompactSource A km.value}
    (V : MotivePresheafSetup T S) (U : ReducedYonedaSource V)
    {Q : LocalizingGeneratorFamily U} {F : FilteredComparisonFamily U}
    (M : localizingMotive V U Q F)

/-- BGT8.7 extends the same original IK functor. This source equivalence retains
all natural-transformation parameters on the entire perfect-category source. -/
structure IKInvariantExtension where
  models : MotiveFunctorModels V M
  equivalence : (mapping (perfectCategories A) S.category.toSSet) _⦋1⦌
  weak : IsEquivalenceEdge _ equivalence
  source : letI := T.enrichment; letI := V.colimits
    (mapping _ _).δ 1 equivalence = mappingZero _ _
    (((stableCategories A).fullEnhancedSubcategory (IsPerfectCategoryVertex A)).ι ≫
      U.coherent ≫ M.reflector ≫ models.functor)
  target : (mapping _ _).δ 0 equivalence = mappingZero _ _ I.perfectFunctor

variable {I V U M}

/-- A value comparison is a source-equivalence component with the native cofibrant/fibrant augmentations. -/
structure InvariantObjectComparison (H : IKInvariantExtension I V U M) (C : PerfectInfinityCategory.{0}) where
  map : letI := T.enrichment; letI := V.colimits
    R.replacements.cofibrant.obj (H.models.model (U.presheaf C.toStableInfinityCategory)) ⟶
    R.replacements.fibrant.obj (I.spectrum C.toStableInfinityCategory)
  middle : S.category.toSSet _⦋1⦌
  first : S.category.toSSet _⦋2⦌
  first_source : letI := T.enrichment; letI := V.colimits
    S.category.toSSet.δ 2 first =
    S.edge (R.replacements.cofibrant_augmentation.app (H.models.model (U.presheaf C.toStableInfinityCategory)))
  first_target : S.category.toSSet.δ 0 first =
    (evaluateAt (perfectCategories A) S.category.toSSet (perfectCategoryVertex A C)).app (op ⦋1⦌) H.equivalence
  first_composite : S.category.toSSet.δ 1 first = middle
  second : S.category.toSSet _⦋2⦌
  second_source : S.category.toSSet.δ 2 second = middle
  second_target : S.category.toSSet.δ 0 second =
    S.edge (R.replacements.fibrant_augmentation.app (I.spectrum C.toStableInfinityCategory))
  second_composite : S.category.toSSet.δ 1 second = S.edge map
  weak : IsStableWeak S map

def objectComparisonHo {H : IKInvariantExtension I V U M} {C : PerfectInfinityCategory.{0}}
    (D : InvariantObjectComparison H C) :
    (spectrumQ S).obj (H.models.model (U.presheaf C.toStableInfinityCategory)) ⟶
      (spectrumQ S).obj (I.spectrum C.toStableInfinityCategory) := by
  let a := R.replacements.cofibrant_augmentation.app (H.models.model (U.presheaf C.toStableInfinityCategory))
  let b := R.replacements.fibrant_augmentation.app (I.spectrum C.toStableInfinityCategory)
  letI : IsIso ((spectrumQ S).map a) := (stableWeak S).Q_inverts _ (R.replacements.cofibrant_weak _)
  letI : IsIso ((spectrumQ S).map b) := (stableWeak S).Q_inverts _ (R.replacements.fibrant_weak _)
  exact inv ((spectrumQ S).map a) ≫ (spectrumQ S).map D.map ≫ inv ((spectrumQ S).map b)

theorem objectComparisonHo_isIso {H : IKInvariantExtension I V U M} {C : PerfectInfinityCategory.{0}}
    (D : InvariantObjectComparison H C) : IsIso (objectComparisonHo D) := by
  have : IsIso ((spectrumQ S).map D.map) := (stableWeak S).Q_inverts _ D.weak
  unfold objectComparisonHo
  infer_instance

/-- Stage zero is the original universal IK cocone, followed only by its native fibrant augmentation. -/
structure IKStageZeroMap (I : NativeIKSource K R L P B) (C : StableInfinityCategory.{0}) where
  map : cofibrantK K R C ⟶ R.replacements.fibrant.obj (I.spectrum C)
  triangle : S.category.toSSet _⦋2⦌
  first : S.category.toSSet.δ 2 triangle =
    (coconeDiagram S.category.toSSet
      (stableSequenceDiagram S (nonconnectiveTower K R L P B C)) (I.colimits C).cocone).app (op ⦋1⦌)
      (ULift.up (nerve.edgeMk (WithTerminal.homFrom (0 : ℕ))).edge)
  second : S.category.toSSet.δ 0 triangle = S.edge (R.replacements.fibrant_augmentation.app (I.spectrum C))
  composite : S.category.toSSet.δ 1 triangle = S.edge map

def nativeIKFunctorUnit (D : SpectrumHoClosedSource S R.replacements) (E : FreeZeroSphereSource)
    (H : IKInvariantExtension I V U M) (W : SphereIndexSource T S)
    (J : InvariantObjectComparison H (perfectSourceObject T W.index))
    (T₀ : IKStageZeroMap I (T.represented W.index)) :
    letI := D.monoidal
    (𝟙_ (spectrumHo S)) ⟶ (spectrumQ S).obj (H.models.model (U.presheaf (T.represented W.index))) := by
  letI := D.monoidal
  let a := R.replacements.cofibrant_augmentation.app (connectiveK K.construction (T.represented W.index))
  let b := R.replacements.fibrant_augmentation.app (I.spectrum (T.represented W.index))
  letI : IsIso ((spectrumQ S).map a) := (stableWeak S).Q_inverts _ (R.replacements.cofibrant_weak _)
  letI : IsIso ((spectrumQ S).map b) := (stableWeak S).Q_inverts _ (R.replacements.fibrant_weak _)
  letI : IsIso (objectComparisonHo J) := objectComparisonHo_isIso J
  exact D.unit.hom ≫ (spectrumQ S).map E.iso.inv ≫
    (spectrumQ S).map (objectSphereMap K.construction (T.represented W.index) W.sphere) ≫
    inv ((spectrumQ S).map a) ≫ (spectrumQ S).map T₀.map ≫
    inv ((spectrumQ S).map b) ≫ inv (objectComparisonHo J)

/-- The canonical comparison uses full native end evaluation, spectral linearity,
the source sphere K class, the actual IK tower cocone and the original invariant equivalence. -/
def canonicalIKComparison (D : SpectrumHoClosedSource S R.replacements) (E : FreeZeroSphereSource)
    (H : IKInvariantExtension I V U M) (W : SphereIndexSource T S)
    (J : InvariantObjectComparison H (perfectSourceObject T W.index))
    (T₀ : IKStageZeroMap I (T.represented W.index)) (C : PerfectInfinityCategory.{0})
    (J_C : InvariantObjectComparison H C)
    (D_S : SpectrumTensorSource S R.replacements) (D_M : MotiveTensorSource V R.replacements M)
    (N : MotiveFunctorLinearity H.models D_S D_M)
    (Q_E : MotiveEvaluationSource D_M (U.presheaf (T.represented W.index)) (U.presheaf C.toStableInfinityCategory))
    (Q_F : FunctorEvaluationSource H.models D_S D_M N
      (U.presheaf (T.represented W.index)) (U.presheaf C.toStableInfinityCategory) Q_E) :
    letI := T.enrichment; letI := V.colimits
    (spectrumQ S).obj (M.mappingSpectrum (U.presheaf (T.represented W.index)) (U.presheaf C.toStableInfinityCategory)) ⟶
      (spectrumQ S).obj (I.spectrum C.toStableInfinityCategory) := by
  letI := T.enrichment
  letI := V.colimits
  letI := D.monoidal
  letI := D.symmetric
  letI := D.closed
  let X := M.mappingSpectrum (U.presheaf (T.represented W.index)) (U.presheaf C.toStableInfinityCategory)
  let FE := H.models.model (U.presheaf (T.represented W.index))
  let FF := H.models.model (U.presheaf C.toStableInfinityCategory)
  let a := R.replacements.fibrant_augmentation.app FF
  letI : IsIso ((spectrumQ S).map a) := (stableWeak S).Q_inverts _ (R.replacements.fibrant_weak FF)
  let evaluation : (spectrumQ S).obj X ⊗ (spectrumQ S).obj FE ⟶ (spectrumQ S).obj FF :=
    (D.tensor X FE).hom ≫ (spectrumQ S).map Q_F.map ≫ inv ((spectrumQ S).map a)
  let f : (spectrumQ S).obj X ⟶ (ihom ((spectrumQ S).obj FE)).obj ((spectrumQ S).obj FF) :=
    MonoidalClosed.curry ((β_ ((spectrumQ S).obj FE) ((spectrumQ S).obj X)).hom ≫ evaluation)
  exact f ≫ (MonoidalClosed.pre (nativeIKFunctorUnit D E H W J T₀)).app ((spectrumQ S).obj FF) ≫
    (MonoidalClosed.unitIsoSelf (X := (spectrumQ S).obj FF)).hom ≫ objectComparisonHo J_C

/-- Point-set rectification is an output between genuine cofibrant/fibrant native models. -/
structure IKComparisonRectification (D : SpectrumHoClosedSource S R.replacements) (E : FreeZeroSphereSource)
    (H : IKInvariantExtension I V U M) (W : SphereIndexSource T S)
    (J : InvariantObjectComparison H (perfectSourceObject T W.index))
    (T₀ : IKStageZeroMap I (T.represented W.index)) (C : PerfectInfinityCategory.{0})
    (J_C : InvariantObjectComparison H C)
    (D_S : SpectrumTensorSource S R.replacements) (D_M : MotiveTensorSource V R.replacements M)
    (N : MotiveFunctorLinearity H.models D_S D_M)
    (Q_E : MotiveEvaluationSource D_M (U.presheaf (T.represented W.index)) (U.presheaf C.toStableInfinityCategory))
    (Q_F : FunctorEvaluationSource H.models D_S D_M N
      (U.presheaf (T.represented W.index)) (U.presheaf C.toStableInfinityCategory) Q_E) where
  map : letI := T.enrichment; letI := V.colimits
    R.replacements.cofibrant.obj
      (M.mappingSpectrum (U.presheaf (T.represented W.index)) (U.presheaf C.toStableInfinityCategory)) ⟶
    R.replacements.fibrant.obj (I.spectrum C.toStableInfinityCategory)
  normalized : letI := T.enrichment; letI := V.colimits
    (spectrumQ S).map map =
    (spectrumQ S).map (R.replacements.cofibrant_augmentation.app
      (M.mappingSpectrum (U.presheaf (T.represented W.index)) (U.presheaf C.toStableInfinityCategory))) ≫
    canonicalIKComparison D E H W J T₀ C J_C D_S D_M N Q_E Q_F ≫
    (spectrumQ S).map (R.replacements.fibrant_augmentation.app (I.spectrum C.toStableInfinityCategory))

end MathlibExt.AlgebraicTopology.NativeIKCorepresentabilityModels
