/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeMotiveGenerators
public import MathlibExt.AlgebraicTopology.NativeK0ComparisonModels

/-!
# Full exact-functor K presheaves and native canonical comparison maps

K is always the original S-construction spectrum. Each presheaf value is
K of the full exact-functor infinity category, retaining noninvertible
natural transformations. The source composition and the full K parameter
action fix every native coefficient action as a spectrum map.

The raw-Yoneda-to-K arrow is the native free-zero extension of the entire
core-to-zero-fold map followed by the original level-zero S assembly.
Its zero cocone is the original strictly commuting presheaf cocone, not
an independent nullhomotopy. Reduced and reflected comparison maps keep
that whole cocone and the original reflector unit.

BGT arXiv:1001.2282v4 Theorem 7.13 has target
K(Fun_exact(B, Idem(A))). The first comparison theorem here explicitly
uses perfect A. No raw non-idempotent A is silently substituted.
Native source pins and licenses remain in the imported ports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeKCorepresentabilityModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open MathlibExt.SpectraSource
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels StableInfinityMappingSpaces
open StableInfinityFilteredColimits
open StableInfinitySParametrizedAction StableInfinityMultiSConstruction StableInfinityKSpectra
open NativeSZeroFoldModels NativeKParametrizedSource NativeCompactSourceModels
open NativeSpectrumFunctionEvaluation NativeSpectrumConeSources NativeSpectrumBoundarySources
open NativeSpectralPresheafModels NativeMotivePresheafSources NativeMotiveLocalizationModels
open NativeMotiveGenerators NativeK0ComparisonModels NativeSpectraSimplicialSource
open StableSpectraInfinitySource NativeDerivedSpectrumModels
open scoped Simplicial MonoidalClosed

/-- The non-idempotent variant is still the entire full exact-functor category. -/
structure FullStableExactFunctorInput (B A : StableInfinityCategory.{0}) where
  category : StableInfinityCategory.{0}
  normalized : category.toSSet = exactFunctorCategory B A

def FullExactFunctorInput.stableInput {B : StableInfinityCategory.{0}} {A : PerfectInfinityCategory.{0}}
    (F : FullExactFunctorInput B A) : FullStableExactFunctorInput B A.toStableInfinityCategory :=
  ⟨F.category.toStableInfinityCategory, F.normalized⟩

def exactFunctorInclusion (B A : StableInfinityCategory.{0}) :
    exactFunctorCategory B A ⟶ mapping B.toSSet A.toSSet :=
  ((mapping B.toSSet A.toSSet).fullEnhancedSubcategory (IsExactVertex B A)).ι

def exactCoreToMapping (B A : StableInfinityCategory.{0}) :
    ExactFunctorCore B A ⟶ mapping B.toSSet A.toSSet :=
  (coreSubcomplex (exactFunctorCategory B A)).ι ≫ exactFunctorInclusion B A

variable {A : StableCategoryEnrichment} {k : Cardinal.{0}} {T : SpectralCompactSource A k}
  {S : SpectrumInfinitySource} (V : MotivePresheafSetup T S)

/-- Precomposition is normalized on every simplex of the FULL exact-functor category.
The test variable x retains arbitrary natural transformations, before taking any core. -/
structure FullExactPresheafInput (D : StableInfinityCategory.{0}) where
  input : ∀ c : T.index, FullStableExactFunctorInput (T.represented c) D
  parameter : ∀ c d : T.index,
    ExactFunctorCore (T.represented c) (T.represented d) ⟶
      ExactFunctorCore (input d).category (input c).category
  normalization : ∀ (c d : T.index) (n : SimplexCategoryᵒᵖ)
    (p : (ExactFunctorCore (T.represented c) (T.represented d)).obj n)
    (x : (input d).category.toSSet.obj n),
    ((eqToHom (input c).normalized).app n
      ((MonoidalClosed.uncurry (parameter c d ≫ exactCoreToMapping (input d).category (input c).category)).app n
        (x, p))).val =
      (SimplicialCategory.sHomComp (T.represented c).toSSet (T.represented d).toSSet D.toSSet).app n
        (p.val.val, ((eqToHom (input d).normalized).app n x).val)

variable {V}

def sourceExactSpectrumMap (T : SpectralCompactSource A k) (c d : T.index) :
    letI := T.enrichment
    (c ⟶[SymmetricSpectrum] d) ⟶
      suspensionPlus.obj (ExactFunctorCore (T.represented c) (T.represented d)) :=
  letI := T.enrichment
  T.representationMap c d ≫
    suspensionPlus.map (eqToHom (A.hom_normalization (T.represented c) (T.represented d)))

variable {D : StableInfinityCategory.{0}} {N : SpectrumSimplicialEnrichment}
  (K : ParametrizedKSource A N) (J : FullExactPresheafInput (T := T) D)

/-- This coefficient action uses the original full precomposition parameter followed
by the original all-level S/K action and the native free-zero adjunction. -/
def kPrecompositionSpectrum (c d : T.index) :
    suspensionPlus.obj (ExactFunctorCore (T.represented c) (T.represented d)) ⟶
      (Mod.internalHom (connectiveK K.construction (J.input d).category)).obj
        (connectiveK K.construction (J.input c).category) :=
  letI := A.enrichment
  letI := N.ordinary
  ((SymmetricSpectrum.freeAddBasepointAdjunction 0).homEquiv _ _).symm
    (J.parameter c d ≫ eqToHom (A.hom_normalization (J.input d).category (J.input c).category).symm ≫
      K.maps.hom (J.input d).category (J.input c).category ≫
      eqToHom (N.hom_normalization _ _))

/-- Actual K values and full homogeneous coefficient actions, independent of any motive comparison. -/
structure KPresheafSource where
  presheaf : letI := T.enrichment; RawPresheaf T.index
  objects : letI := T.enrichment
    ∀ c : T.index, value T.index presheaf c = connectiveK K.construction (J.input c).category
  action : letI := T.enrichment
    ∀ c d : T.index,
    NativeSpectralPresheafModels.action T.index presheaf c d ≫ eqToHom (objects c) =
      (eqToHom (objects d) ⊗ₘ (sourceExactSpectrumMap T c d ≫ kPrecompositionSpectrum K J c d)) ≫
        (ihom.ev (connectiveK K.construction (J.input d).category)).app
          (connectiveK K.construction (J.input c).category)

/-- The entire actual core is the zero-fold diagram, with both native inverse laws.
This source construction contains no K or corepresentability input. -/
structure CoreToZeroFold (C : StableInfinityCategory.{0}) where
  evaluation : ZeroFoldEvaluationComparison C
  map : core C.toSSet ⟶ multiSDiagonal C 0
  left_inverse : map ≫ evaluation.map = 𝟙 _
  right_inverse : evaluation.map ≫ map = 𝟙 _

/-- The canonical map is fixed by the original full zero-fold source and native S assembly. -/
def objectClassSpectrum (C : StableInfinityCategory.{0}) (F : CoreToZeroFold C) :
    suspensionPlus.obj (core C.toSSet) ⟶ connectiveK K.construction C :=
  ((SymmetricSpectrum.freeAddBasepointAdjunction 0).homEquiv _ _).symm
    (F.map ≫ ((K.construction.assembly C).comparison 0).right)

variable (V) (E : KPresheafSource K J)

/-- Every component is the exact native free-zero extension. The displayed strict zero
equality fixes the complete source zero cocone rather than leaving a nullhomotopy unspecified. -/
structure RawYonedaToKSource where
  zeroFold : ∀ c : T.index, CoreToZeroFold (J.input c).category
  map : letI := T.enrichment; V.rawYoneda D ⟶ E.presheaf
  components : letI := T.enrichment
    ∀ c : T.index,
    mapComponent T.index map c ≫ eqToHom (E.objects c) =
      eqToHom (V.yoneda.object D c) ≫
      suspensionPlus.map (eqToHom (A.hom_normalization (T.represented c) D)) ≫
      suspensionPlus.map (eqToHom (congrArg core (J.input c).normalized).symm) ≫
      objectClassSpectrum K (J.input c).category (zeroFold c)
  zero_equality : letI := T.enrichment
    V.yonedaMap (zeroExactFunctor (V.zeroCategory.fromZero D)) ≫ map =
      V.zeroPresheaf.terminal.from (V.rawYoneda V.zeroCategory.category.toStableInfinityCategory) ≫
        V.zeroPresheaf.initial.to E.presheaf

variable {V K J E}

def rawKZeroCocone (F : RawYonedaToKSource V K J E) : letI := T.enrichment
    PushoutCocone (V.yonedaMap (zeroExactFunctor (V.zeroCategory.fromZero D)))
      (V.zeroPresheaf.terminal.from (V.rawYoneda V.zeroCategory.category.toStableInfinityCategory)) :=
  letI := T.enrichment
  PushoutCocone.mk F.map (V.zeroPresheaf.initial.to E.presheaf) F.zero_equality

/-- This is the original complete ordinary source cocone, whose nerve gives its canonical coherent nullhomotopy. -/
def rawKZeroDiagram (F : RawYonedaToKSource V K J E) : letI := T.enrichment
    WithTerminal WalkingSpan ⥤ RawPresheaf T.index :=
  letI := T.enrichment
  let c := rawKZeroCocone F
  WithTerminal.lift (Z := c.pt)
    (span (V.yonedaMap (zeroExactFunctor (V.zeroCategory.fromZero D)))
      (V.zeroPresheaf.terminal.from (V.rawYoneda V.zeroCategory.category.toStableInfinityCategory)))
    (fun p => c.ι.app p) (by
    intro x y f
    exact c.w f)

/-- Reduction uses the universal map of this exact same original cocone. -/
structure ReducedKFactor (R : ReducedYonedaSource V) (F : RawYonedaToKSource V K J E) where
  target : letI := T.enrichment
    PresheafCocone V.presheaves
      (V.yonedaMap (zeroExactFunctor (V.zeroCategory.fromZero D)))
      (V.zeroPresheaf.terminal.from (V.rawYoneda V.zeroCategory.category.toStableInfinityCategory))
  target_presheaf : letI := T.enrichment; target.presheaf = E.presheaf
  target_diagram : letI := T.enrichment
    coconeDiagram V.presheaves.category.toSSet
      (presheafSpan V.presheaves (V.yonedaMap (zeroExactFunctor (V.zeroCategory.fromZero D)))
        (V.zeroPresheaf.terminal.from (V.rawYoneda V.zeroCategory.category.toStableInfinityCategory)))
      target.cocone = liftedNerveMap (rawKZeroDiagram F) ≫ V.presheaves.source
  extension : letI := T.enrichment
    PresheafCofiberExtension V.presheaves (R.cofibers D) target

def ReducedKFactor.map {R : ReducedYonedaSource V} {F : RawYonedaToKSource V K J E}
    (B : ReducedKFactor R F) : letI := T.enrichment; R.presheaf D ⟶ E.presheaf :=
  letI := T.enrichment
  B.extension.map ≫ eqToHom B.target_presheaf

/-- Reflection factors the same reduced source map into the actual fibrant K presheaf.
The normalization is an equality of arrows in the full native presheaf localization. -/
structure ReflectedKFactor (U : ReducedYonedaSource V) (F : RawYonedaToKSource V K J E)
    (B : ReducedKFactor U F) (G : letI := T.enrichment; Set (RawMotiveGenerator (C := T.index)))
    (M : letI := T.enrichment; letI := V.colimits;
      MotiveLocalization V.presheaves V.ends V.replacements G) where
  map : letI := T.enrichment; letI := V.colimits
    M.rawReflector.obj (U.presheaf D) ⟶ V.replacements.fibrant.obj E.presheaf
  normalized : letI := T.enrichment; letI := V.colimits
    SameArrow V.presheaves.category.toSSet
      (presheafEdge V.presheaves (M.rawUnit.app (U.presheaf D) ≫ map))
      (presheafEdge V.presheaves (B.map ≫ V.replacements.fibrant_augmentation.app E.presheaf))

def endCofibrantAugmentation (V : MotivePresheafSetup T S) (c : T.index)
    (F : letI := T.enrichment; RawPresheaf T.index) :
    letI := T.enrichment; letI := V.colimits
    rawHom T.index (V.rawYoneda (T.represented c)) F ⟶
      rawHom T.index (V.replacements.cofibrant.obj (V.rawYoneda (T.represented c))) F :=
  letI := T.enrichment
  letI := V.colimits
  rawPrecomposition T.index
    (V.replacements.cofibrant_augmentation.app (V.rawYoneda (T.represented c))) F
    (V.ends.pre _ _ _ _)

/-- The evaluation is the original native full end projection, the native identity, and closed counit. -/
def restrictedYonedaEndEvaluation (V : MotivePresheafSetup T S) (c : T.index)
    (Y : RestrictedRepresentable V.yoneda c) (F : letI := T.enrichment; RawPresheaf T.index) :
    letI := T.enrichment
    rawHom T.index (V.rawYoneda (T.represented c)) F ⟶ value T.index F c :=
  letI := T.enrichment
  rawPrecomposition T.index (eqToHom Y.normalized) F (V.ends.pre _ _ _ _) ≫
    yonedaEvaluation T.index Y.source F

/-- This is the explicit canonical map between entire native spectra in their literal
stable-weak localization: two source-unit precompositions, native postcomposition,
the replacement comparison, spectral Yoneda evaluation, and original fibrant augmentations. -/
def canonicalKComparison (U : ReducedYonedaSource V) (F : RawYonedaToKSource V K J E)
    (B : ReducedKFactor U F) (G : letI := T.enrichment; Set (RawMotiveGenerator (C := T.index)))
    (M : letI := T.enrichment; letI := V.colimits;
      MotiveLocalization V.presheaves V.ends V.replacements G)
    (L : ReflectedKFactor U F B G M) (c : T.index) (Y : RestrictedRepresentable V.yoneda c)
    (h : letI := T.enrichment; letI := V.colimits;
      IsStableWeak S (endCofibrantAugmentation V c
        (V.replacements.fibrant.obj (V.replacements.fibrant.obj E.presheaf)))) :
    letI := T.enrichment; letI := V.colimits
    (spectrumQ S).obj (M.mappingSpectrum (U.presheaf (T.represented c)) (U.presheaf D)) ⟶
      (spectrumQ S).obj (connectiveK K.construction (J.input c).category) := by
  letI := T.enrichment
  letI := V.colimits
  let target := V.replacements.fibrant.obj (V.replacements.fibrant.obj E.presheaf)
  let a := endCofibrantAugmentation V c target
  let b := mapComponent T.index (V.replacements.fibrant_augmentation.app E.presheaf) c
  let d := mapComponent T.index
    (V.replacements.fibrant_augmentation.app (V.replacements.fibrant.obj E.presheaf)) c
  letI : IsIso ((spectrumQ S).map a) := (stableWeak S).Q_inverts a h
  letI : IsIso ((spectrumQ S).map b) := (stableWeak S).Q_inverts b
    (V.replacements.fibrant_weak E.presheaf c)
  letI : IsIso ((spectrumQ S).map d) := (stableWeak S).Q_inverts d
    (V.replacements.fibrant_weak (V.replacements.fibrant.obj E.presheaf) c)
  exact (spectrumQ S).map
      (derivedPrecomposition T.index S V.ends V.replacements
        (M.rawUnit.app (U.presheaf (T.represented c)))
        (M.rawReflector.obj (U.presheaf D))) ≫
    (spectrumQ S).map
      (derivedPostcomposition T.index S V.ends V.replacements
        (U.presheaf (T.represented c)) L.map) ≫
    (spectrumQ S).map
      (derivedPrecomposition T.index S V.ends V.replacements
        (U.augmentation (T.represented c)) (V.replacements.fibrant.obj E.presheaf)) ≫
    inv ((spectrumQ S).map a) ≫
    (spectrumQ S).map (restrictedYonedaEndEvaluation V c Y target) ≫
    inv ((spectrumQ S).map d) ≫ inv ((spectrumQ S).map b) ≫
    (spectrumQ S).map (eqToHom (E.objects c))

/-- An actual point-set comparison represents that exact canonical map, without asserting its equivalence. -/
structure KComparisonRectification (U : ReducedYonedaSource V) (F : RawYonedaToKSource V K J E)
    (B : ReducedKFactor U F) (G : letI := T.enrichment; Set (RawMotiveGenerator (C := T.index)))
    (M : letI := T.enrichment; letI := V.colimits;
      MotiveLocalization V.presheaves V.ends V.replacements G)
    (L : ReflectedKFactor U F B G M) (c : T.index) (Y : RestrictedRepresentable V.yoneda c)
    (h : letI := T.enrichment; letI := V.colimits;
      IsStableWeak S (endCofibrantAugmentation V c
        (V.replacements.fibrant.obj (V.replacements.fibrant.obj E.presheaf))))
    (Q : SpectrumReplacements S) where
  map : letI := T.enrichment; letI := V.colimits
    Q.cofibrant.obj (M.mappingSpectrum (U.presheaf (T.represented c)) (U.presheaf D)) ⟶
      Q.fibrant.obj (connectiveK K.construction (J.input c).category)
  normalized : letI := T.enrichment; letI := V.colimits
    (spectrumQ S).map map =
      (spectrumQ S).map (Q.cofibrant_augmentation.app
        (M.mappingSpectrum (U.presheaf (T.represented c)) (U.presheaf D))) ≫
      canonicalKComparison U F B G M L c Y h ≫
      (spectrumQ S).map (Q.fibrant_augmentation.app (connectiveK K.construction (J.input c).category))

end MathlibExt.AlgebraicTopology.NativeKCorepresentabilityModels
