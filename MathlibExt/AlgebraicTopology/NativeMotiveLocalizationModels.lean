/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeMotivePresheafSources
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Independent native spectral-presheaf motive localizations

A motive category is the full local-object subcategory of the actual
spectral-presheaf stable localization. Localness tests the native full
derived-end precomposition spectrum, including every spectrum level.
The reflector and its native raw augmentation are independent construction
outputs. The mapping spectrum is the literal derived end of the two
reflected raw presheaves, never a supplied spectral carrier.

Exact rows use an actual raw Verdier quotient followed by its idempotent
completion. That completion has its full exact-functor universal property
only at idempotent-complete targets. Split rows retain the original right
adjoints through complete native counit/comma universality.

Sources: BGT arXiv:1001.2282v4 Sections 5--6 and 8.1--8.3;
HTT Sections 2.2/5.5; HSS Sections 3.1--3.4. Native source notices remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeMotiveLocalizationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.SpectraSource
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels StableInfinityMappingSpaces
open StableInfinityFiniteDiagrams StableInfinityFilteredColimits StableInfinityMappingSpaceMaps
open NativeDiagramFamilies NativeSpectrumConeSources NativeSpectrumBoundarySources
open NativeKParametrizedSource NativeCompactSourceModels BGTVerdierQuotients
open NativeSpectralPresheafModels NativeMotivePresheafSources
open StableSpectraInfinitySource NativeDerivedSpectrumModels
open scoped Simplicial Cardinal

/-- The zero stable category has the literal one-object discrete nerve. -/
structure ZeroCategorySource where
  category : PerfectInfinityCategory.{0}
  normalized : category.toStableInfinityCategory.toSSet = nerve (Discrete PUnit)
  fromZero : ∀ D : StableInfinityCategory.{0},
    StableInfinitySParametrizedAction.ZeroExactFunctorSource category.toStableInfinityCategory D
  toZero : ∀ D : StableInfinityCategory.{0},
    StableInfinitySParametrizedAction.ZeroExactFunctorSource D category.toStableInfinityCategory

/-- Idem uses the native full exact-functor comparison at precisely perfect targets. -/
structure PerfectCompletion (C : StableInfinityCategory.{0}) where
  category : PerfectInfinityCategory.{0}
  unit : FullStableInclusion C category.toStableInfinityCategory
  universal : ∀ D : PerfectInfinityCategory.{0},
    ∃ f : exactFunctorCategory category.toStableInfinityCategory D.toStableInfinityCategory ⟶
      exactFunctorCategory C D.toStableInfinityCategory,
      f ≫ ((mapping C.toSSet D.toStableInfinityCategory.toSSet).fullEnhancedSubcategory
        (IsExactVertex C D.toStableInfinityCategory)).ι =
      ((mapping category.toStableInfinityCategory.toSSet D.toStableInfinityCategory.toSSet).fullEnhancedSubcategory
        (IsExactVertex category.toStableInfinityCategory D.toStableInfinityCategory)).ι ≫
        precomposition unit.functor.map D.toStableInfinityCategory.toSSet ∧
      CategoricalWeakEquivalence f

/-- The Morita cofiber keeps both the raw quotient and its genuine Idem unit. -/
structure PerfectExactSequence where
  left : PerfectInfinityCategory.{0}
  middle : PerfectInfinityCategory.{0}
  inclusion : FullStableInclusion left.toStableInfinityCategory middle.toStableInfinityCategory
  quotient : StableVerdierQuotient inclusion
  completion : PerfectCompletion quotient.category

def PerfectExactSequence.right (E : PerfectExactSequence) : PerfectInfinityCategory.{0} :=
  E.completion.category

def PerfectExactSequence.quotientMap (E : PerfectExactSequence) :
    ExactFunctor E.middle.toStableInfinityCategory E.right.toStableInfinityCategory :=
  E.quotient.quotient.comp E.completion.unit.functor

/-- The counit is a whole native natural transformation. Its evaluated object
is terminal in the actual pullback right-slice comma category at every target. -/
structure RightAdjointSource {C D : StableInfinityCategory.{0}}
    (f : ExactFunctor C D) (g : ExactFunctor D C) where
  counit : (mapping D.toSSet D.toSSet) _⦋1⦌
  source : (mapping D.toSSet D.toSSet).δ 1 counit = mappingZero _ _ (g.map ≫ f.map)
  target : (mapping D.toSSet D.toSSet).δ 0 counit = mappingZero _ _ (𝟙 D.toSSet)
  object : ∀ d : D.toSSet _⦋0⦌,
    (pullback (BGTContravariantPresheaves.sourceProjection D.toSSet d) f.map) _⦋0⦌
  source_object : ∀ d : D.toSSet _⦋0⦌,
    (pullback.snd (BGTContravariantPresheaves.sourceProjection D.toSSet d) f.map).app (op ⦋0⦌)
      (object d) = g.map.app (op ⦋0⦌) d
  counit_component : ∀ d : D.toSSet _⦋0⦌,
    ((pullback.fst (BGTContravariantPresheaves.sourceProjection D.toSSet d) f.map).app (op ⦋0⦌)
      (object d)).val = (evaluateAt D.toSSet D.toSSet d).app (op ⦋1⦌) counit
  universal : ∀ d : D.toSSet _⦋0⦌,
    IsTerminalObject (pullback (BGTContravariantPresheaves.sourceProjection D.toSSet d) f.map) (object d)

/-- Split exactness uses the actual adjoints and the same quotient/section maps. -/
structure SplitPerfectExactSequence (E : PerfectExactSequence) where
  retraction : ExactFunctor E.middle.toStableInfinityCategory E.left.toStableInfinityCategory
  sectionMap : ExactFunctor E.right.toStableInfinityCategory E.middle.toStableInfinityCategory
  inclusion_adjoint : RightAdjointSource E.inclusion.functor retraction
  quotient_adjoint : RightAdjointSource E.quotientMap sectionMap
  retraction_inclusion : NaturallyEquivalentMaps (E.inclusion.functor.map ≫ retraction.map)
    (𝟙 E.left.toStableInfinityCategory.toSSet)
  quotient_section : NaturallyEquivalentMaps (sectionMap.map ≫ E.quotientMap.map)
    (𝟙 E.right.toStableInfinityCategory.toSSet)

variable {C : Type} [EnrichedCategory SymmetricSpectrum C]
  {S : SpectrumInfinitySource} (P : NativeSpectralPresheafModels.PresheafInfinitySource C S)

/-- These are the original raw object and arrow images in the fixed localization. -/
def presheafVertex (E : RawPresheaf C) : P.category.toSSet _⦋0⦌ :=
  P.source.app (op ⦋0⦌) (ComposableArrows.mk₀ E)

def presheafEdge {E F : RawPresheaf C} (f : E ⟶ F) : P.category.toSSet _⦋1⦌ :=
  P.source.app (op ⦋1⦌) (nerve.edgeMk f).edge

/-- A representative is tied to the actual entire source localization, not merely to its core. -/
structure RawRepresentative (x : P.category.toSSet _⦋0⦌) where
  presheaf : RawPresheaf C
  normalized : presheafVertex P presheaf = x

/-- Every object of the localization is the image of a raw presheaf, since the source map is
bijective on objects. -/
noncomputable def rawRepresentative (x : P.category.toSSet _⦋0⦌) : RawRepresentative P x where
  presheaf := nerveEquiv (P.source_objects.2 x).choose
  normalized := by
    unfold presheafVertex
    conv_rhs => rw [← (P.source_objects.2 x).choose_spec]
    exact congrArg (P.source.app (op ⦋0⦌)) (nerveEquiv.symm_apply_apply _)

/-- The raw zero is both native categorical zero and pointwise the original zero spectrum. -/
structure PresheafZeroSource where
  presheaf : RawPresheaf C
  initial : IsInitial presheaf
  terminal : IsTerminal presheaf
  components : ∀ c : C, value C presheaf c = zeroSpectrum
  source_zero : IsZeroObject P.category.toSSet (presheafVertex P presheaf)

def presheafSpan {E F Z : RawPresheaf C} (f : E ⟶ F) (t : E ⟶ Z) :
    indexNerve.{1} WalkingSpan ⟶ P.category.toSSet :=
  liftedNerveMap (span f t) ≫ P.source

/-- The apex belongs to the same actual presheaf span, including its full nullhomotopy. -/
structure PresheafCocone {E F Z : RawPresheaf C} (f : E ⟶ F) (t : E ⟶ Z) where
  presheaf : RawPresheaf C
  cocone : (rightCones P.category.toSSet (presheafSpan P f t)) _⦋0⦌
  apex : (coconeApexMap P.category.toSSet (presheafSpan P f t)).app (op ⦋0⦌) cocone =
    presheafVertex P presheaf

structure PresheafCofiber {E F Z : RawPresheaf C} (f : E ⟶ F) (t : E ⟶ Z)
    extends PresheafCocone P f t where
  zero : IsZeroObject P.category.toSSet (presheafVertex P Z)
  universal : IsInitialObject (rightCones P.category.toSSet (presheafSpan P f t)) cocone

/-- The strict comparison represents an arrow of the whole same cocone category. -/
structure PresheafCofiberExtension {E F Z : RawPresheaf C} {f : E ⟶ F} {t : E ⟶ Z}
    (D : PresheafCofiber P f t) (T : PresheafCocone P f t) where
  edge : (rightCones P.category.toSSet (presheafSpan P f t)) _⦋1⦌
  source : (rightCones P.category.toSSet (presheafSpan P f t)).δ 1 edge = D.cocone
  target : (rightCones P.category.toSSet (presheafSpan P f t)).δ 0 edge = T.cocone
  map : D.presheaf ⟶ T.presheaf
  normalized : SameArrow P.category.toSSet (presheafEdge P map)
    ((coconeApexMap P.category.toSSet (presheafSpan P f t)).app (op ⦋1⦌) edge)

/-- Every localization generator is an actual whole raw-presheaf arrow. -/
structure RawMotiveGenerator where
  source : RawPresheaf C
  target : RawPresheaf C
  map : source ⟶ target

variable [HasInitial (RawPresheaf C)] (H : EndFunctoriality C) (R : PresheafReplacements C S)

/-- Full spectral right orthogonality includes all shifts/higher mapping parameters through the native spectrum. -/
def IsLocalVertex (G : Set (RawMotiveGenerator (C := C))) (x : P.category.toSSet _⦋0⦌) : Prop :=
  ∀ (E : RawPresheaf C), presheafVertex P E = x →
    ∀ g : RawMotiveGenerator (C := C), g ∈ G →
      IsStableWeak S (derivedPrecomposition C S H R g.map E)

def localObjects (G : Set (RawMotiveGenerator (C := C))) : SSet.{1} :=
  (P.category.toSSet.fullEnhancedSubcategory (IsLocalVertex P H R G)).toSSet

/-- A small source set presents the same full spectral orthogonality class.
The coverage proof is about the original end maps, before any reflector or K comparison. -/
structure SmallGeneratorPresentation (G : Set (RawMotiveGenerator (C := C))) where
  index : Type
  generator : index → RawMotiveGenerator (C := C)
  belongs : ∀ i : index, generator i ∈ G
  coverage : ∀ x : P.category.toSSet _⦋0⦌,
    IsLocalVertex P H R G x ↔
      ∀ (E : RawPresheaf C), presheafVertex P E = x →
        ∀ i : index, IsStableWeak S (derivedPrecomposition C S H R (generator i).map E)

/-- This construction is independent of K: actual local objects, the actual reflector,
and the original native raw unit with its full spectral universal comparison. -/
structure MotiveLocalization (G : Set (RawMotiveGenerator (C := C))) where
  category : StableInfinityCategory.{1}
  normalized : category.toSSet = localObjects P H R G
  reflector : P.category.toSSet ⟶ category.toSSet
  rawReflector : RawPresheaf C ⥤ RawPresheaf C
  rawUnit : 𝟭 (RawPresheaf C) ⟶ rawReflector
  raw_local : ∀ E : RawPresheaf C, IsLocalVertex P H R G (presheafVertex P (rawReflector.obj E))
  raw_normalization : P.source ≫ reflector ≫ eqToHom normalized ≫
    (P.category.toSSet.fullEnhancedSubcategory (IsLocalVertex P H R G)).ι =
      nerveMap rawReflector ≫ P.source
  unit : (mapping P.category.toSSet P.category.toSSet) _⦋1⦌
  unit_source : (mapping P.category.toSSet P.category.toSSet).δ 1 unit = mappingZero _ _ (𝟙 _)
  unit_target : (mapping P.category.toSSet P.category.toSSet).δ 0 unit =
    mappingZero _ _ (reflector ≫ eqToHom normalized ≫
      (P.category.toSSet.fullEnhancedSubcategory (IsLocalVertex P H R G)).ι)
  unit_raw : ∀ E : RawPresheaf C,
    (evaluateAt P.category.toSSet P.category.toSSet (presheafVertex P E)).app (op ⦋1⦌) unit =
      presheafEdge P (rawUnit.app E)
  universal : ∀ E F : RawPresheaf C, IsLocalVertex P H R G (presheafVertex P F) →
    IsStableWeak S (derivedPrecomposition C S H R (rawUnit.app E) F)

variable {P H R}

def MotiveLocalization.inclusion {G : Set (RawMotiveGenerator (C := C))}
    (M : MotiveLocalization P H R G) : M.category.toSSet ⟶ P.category.toSSet :=
  eqToHom M.normalized ≫ (P.category.toSSet.fullEnhancedSubcategory (IsLocalVertex P H R G)).ι

def MotiveLocalization.object {G : Set (RawMotiveGenerator (C := C))}
    (M : MotiveLocalization P H R G) (E : RawPresheaf C) : M.category.toSSet _⦋0⦌ :=
  M.reflector.app (op ⦋0⦌) (presheafVertex P E)

/-- Motive mapping spectra are the literal whole derived ends of those reflected raw representatives. -/
def MotiveLocalization.mappingSpectrum {G : Set (RawMotiveGenerator (C := C))}
    (M : MotiveLocalization P H R G) (E F : RawPresheaf C) : SymmetricSpectrum :=
  derivedHom C S R (M.rawReflector.obj E) (M.rawReflector.obj F)

/-- The mapping-space comparison concerns the same complete native mapping spectrum. -/
structure MotiveMappingComparison {G : Set (RawMotiveGenerator (C := C))}
    (M : MotiveLocalization P H R G) (E F : RawPresheaf C) where
  map : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj
      (level (M.mappingSpectrum E F) 0).right ⟶
    mappingSpace M.category.toSSet (M.object E) (M.object F)
  weak : WeakEquivalence map

/-- Colimit preservation tests native entire coherent diagrams and their original universal cocones. -/
def PreservesSmallColimits {X Y : SSet.{1}} (f : X ⟶ Y) : Prop :=
  ∀ (I : Type) [Category.{0} I] (d : indexNerve I ⟶ X)
    (c : (rightCones X d) _⦋0⦌), IsInitialObject (rightCones X d) c →
    ∃ c' : (rightCones Y (d ≫ f)) _⦋0⦌,
      IsInitialObject (rightCones Y (d ≫ f)) c' ∧
      coconeDiagram Y (d ≫ f) c' = coconeDiagram X d c ≫ f

def HasSmallColimits (X : SSet.{1}) : Prop :=
  ∀ (I : Type) [Category.{0} I] (d : indexNerve I ⟶ X),
    ∃ c : (rightCones X d) _⦋0⦌, IsInitialObject (rightCones X d) c

def colimitFunctorCategory (X Y : SSet.{1}) : SSet.{1} :=
  ((mapping X Y).fullEnhancedSubcategory
    (fun a => PreservesSmallColimits ((mappingZero _ _).symm a))).toSSet

def generatorInvertingFunctorCategory (P : NativeSpectralPresheafModels.PresheafInfinitySource C S)
    (G : Set (RawMotiveGenerator (C := C))) (D : StableInfinityCategory.{1}) : SSet.{1} :=
  ((mapping P.category.toSSet D.toSSet).fullEnhancedSubcategory
    (fun a => PreservesSmallColimits ((mappingZero _ _).symm a) ∧
      ∀ g : RawMotiveGenerator (C := C), g ∈ G →
        IsEquivalenceEdge D.toSSet (((mappingZero _ _).symm a).app (op ⦋1⦌)
          (presheafEdge P g.map)))).toSSet

/-- The full colimit-functor universal property is a conclusion on the independent reflector. -/
def MotiveFunctorUniversal {G : Set (RawMotiveGenerator (C := C))}
    (M : MotiveLocalization P H R G) (D : StableInfinityCategory.{1}) : Prop :=
  ∃ f : colimitFunctorCategory M.category.toSSet D.toSSet ⟶ generatorInvertingFunctorCategory P G D,
    f ≫ ((mapping P.category.toSSet D.toSSet).fullEnhancedSubcategory
      (fun a => PreservesSmallColimits ((mappingZero _ _).symm a) ∧
        ∀ g : RawMotiveGenerator (C := C), g ∈ G →
          IsEquivalenceEdge D.toSSet (((mappingZero _ _).symm a).app (op ⦋1⦌)
            (presheafEdge P g.map)))).ι =
    ((mapping M.category.toSSet D.toSSet).fullEnhancedSubcategory
      (fun a => PreservesSmallColimits ((mappingZero _ _).symm a))).ι ≫
      precomposition M.reflector D.toSSet ∧ CategoricalWeakEquivalence f

end MathlibExt.AlgebraicTopology.NativeMotiveLocalizationModels
