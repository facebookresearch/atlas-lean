/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeMotiveLocalizationModels
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Source-normalized additive and localizing motive generators

The presheaf setup contains the actual compact source, complete native
ends, projective replacements and full restricted spectral Yoneda.
Raw suspension-plus Yoneda at zero is killed explicitly. Reduced Yoneda
is its actual cofiber before any quotient-zero square is imposed.

Split generators use the original inclusion and section. Localizing
generators use the entire original exact quotient square and the native
universal cofiber extension. The final localizing set also includes the
actual filtered-colimit comparison maps of BGT Section 8.3.

Sources: BGT arXiv:1001.2282v4 Sections 5.1/6.1--6.2/8.1--8.3;
HTT Sections 5.3/5.5. Native source attribution remains in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeMotiveGenerators

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.SpectraSource
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels StableInfinityMappingSpaces
open StableInfinityFiniteDiagrams StableInfinityFilteredColimits
open NativeDiagramFamilies NativeSpectrumConeSources NativeSpectrumBoundarySources
open NativeSpectrumCoherentSquares NativeKParametrizedSource NativeCompactSourceModels
open NativeSpectralPresheafModels NativeMotivePresheafSources NativeMotiveLocalizationModels
open StableInfinitySParametrizedAction StableSpectraInfinitySource
open scoped Simplicial Cardinal


/-- A convenience source bundle; every field refers to the already fixed native carrier/map.
It contains no motive category, corepresentability or K equivalence assumption. -/
structure MotivePresheafSetup {A : StableCategoryEnrichment} {k : Cardinal.{0}}
    (T : SpectralCompactSource A k) (S : SpectrumInfinitySource) where
  colimits : letI := T.enrichment; HasColimits (RawPresheaf T.index)
  simplicial : letI := T.enrichment; PresheafSimplicialEnrichment T.index
  presheaves : letI := T.enrichment; NativeSpectralPresheafModels.PresheafInfinitySource T.index S
  coherent : letI := T.enrichment; PresheafCoherentSource T.index S simplicial presheaves
  ends : letI := T.enrichment; EndFunctoriality T.index
  replacements : letI := T.enrichment; letI := colimits; PresheafReplacements T.index S
  yoneda : RestrictedYonedaSource T simplicial
  zeroCategory : ZeroCategorySource
  zeroPresheaf : letI := T.enrichment; PresheafZeroSource presheaves

variable {A : StableCategoryEnrichment} {k : Cardinal.{0}} {T : SpectralCompactSource A k}
  {S : SpectrumInfinitySource}

def MotivePresheafSetup.rawYoneda (V : MotivePresheafSetup T S)
    (B : StableInfinityCategory.{0}) : letI := T.enrichment; RawPresheaf T.index :=
  V.yoneda.presheaf B

def MotivePresheafSetup.yonedaMap (V : MotivePresheafSetup T S)
    {B D : StableInfinityCategory.{0}} (f : ExactFunctor B D) :
    letI := T.enrichment
    V.rawYoneda B ⟶ V.rawYoneda D := V.yoneda.map f

def MotivePresheafSetup.infinityYoneda (V : MotivePresheafSetup T S) :
    letI := T.enrichment
    stableCategories A ⟶ V.presheaves.category.toSSet := V.yoneda.infinityMap V.coherent

/-- An actual source exact functor has its original full coherent category edge. -/
def sourceCategoryArrow (A : StableCategoryEnrichment)
    {B D : StableInfinityCategory.{0}} (f : ExactFunctor B D) : (stableCategories A) _⦋1⦌ :=
  letI := A.enrichment
  (SimplicialNerve.fromNerve (ForgetEnrichment SSet.{0} StableInfinityCategory.{0})).app (op ⦋1⦌)
    (nerve.edgeMk (ForgetEnrichment.homOf SSet.{0} (exactHomPoint A f))).edge

/-- The whole exact-row square retains its actual quotient-zero natural equivalence
on the original rigid two-step Hom and every parameter simplex. -/
structure SourceExactSquare (A : StableCategoryEnrichment) (Z : ZeroCategorySource)
    (E : PerfectExactSequence) where
  zero : ZeroExactFunctorSource E.left.toStableInfinityCategory E.right.toStableInfinityCategory
  path : (ExactFunctorCore E.left.toStableInfinityCategory E.right.toStableInfinityCategory) _⦋1⦌
  path_source : (ExactFunctorCore E.left.toStableInfinityCategory E.right.toStableInfinityCategory).δ 1 path =
    exactFunctorCoreVertex (zeroExactFunctor zero)
  path_target : (ExactFunctorCore E.left.toStableInfinityCategory E.right.toStableInfinityCategory).δ 0 path =
    exactFunctorCoreVertex (E.inclusion.functor.comp E.quotientMap)
  square : indexNerve.{1} SquareCorner ⟶ stableCategories A
  origin : cornerValue square .origin = stableCategoryVertex A E.left.toStableInfinityCategory
  horizontal : cornerValue square .horizontal = stableCategoryVertex A E.middle.toStableInfinityCategory
  vertical : cornerValue square .vertical = stableCategoryVertex A Z.category.toStableInfinityCategory
  final : cornerValue square .final = stableCategoryVertex A E.right.toStableInfinityCategory
  inclusion : square.app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk (homOfLE (originLE .horizontal))).edge) =
      sourceCategoryArrow A E.inclusion.functor
  quotient : square.app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk (homOfLE (finalLE .horizontal))).edge) =
      sourceCategoryArrow A E.quotientMap
  to_zero : square.app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk (homOfLE (originLE .vertical))).edge) =
      sourceCategoryArrow A (zeroExactFunctor (Z.toZero E.left.toStableInfinityCategory))
  from_zero : square.app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk (homOfLE (finalLE .vertical))).edge) =
      sourceCategoryArrow A (zeroExactFunctor (Z.fromZero E.right.toStableInfinityCategory))
  top_normalization : letI := A.enrichment
    HEq ((square.app (op ⦋2⦌) topSourceChain).map rigidFirst rigidLast)
      (refinementLine ≫ (SSet.yonedaEquiv.symm path) ≫
        eqToHom (A.hom_normalization E.left.toStableInfinityCategory E.right.toStableInfinityCategory).symm)

/-- The original lower span and final corner form the full native augmented square diagram. -/
def coconeSquareIndex : WithTerminal WalkingSpan ⥤ SquareCorner :=
  WithTerminal.lift (Z := SquareCorner.final) spanSquareIndex
    (fun p => homOfLE (finalLE (spanSquareIndex.obj p))) (by
      intro x y f
      apply Subsingleton.elim)

def presheafCofiberInclusion {C : Type} [EnrichedCategory SymmetricSpectrum C]
    {S : SpectrumInfinitySource} {P : NativeSpectralPresheafModels.PresheafInfinitySource C S}
    {E F Z : RawPresheaf C} {f : E ⟶ F} {t : E ⟶ Z} (D : PresheafCofiber P f t) :
    P.category.toSSet _⦋1⦌ :=
  (coconeDiagram P.category.toSSet (presheafSpan P f t) D.cocone).app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk (WithTerminal.homFrom WalkingSpan.left)).edge)

variable (V : MotivePresheafSetup T S)

/-- Each reduced object is the actual cofiber of Y(0) → Y(B), and its full unit
is a natural transformation of the original entire coherent source. -/
structure ReducedYonedaSource where
  cofibers : letI := T.enrichment
    ∀ B : StableInfinityCategory.{0},
    PresheafCofiber V.presheaves
      (V.yonedaMap (zeroExactFunctor (V.zeroCategory.fromZero B)))
      (V.zeroPresheaf.terminal.from (V.rawYoneda V.zeroCategory.category.toStableInfinityCategory))
  augmentation : letI := T.enrichment
    ∀ B : StableInfinityCategory.{0}, V.rawYoneda B ⟶ (cofibers B).presheaf
  augmentation_normalization : letI := T.enrichment
    ∀ B : StableInfinityCategory.{0},
    SameArrow V.presheaves.category.toSSet (presheafEdge V.presheaves (augmentation B))
      (presheafCofiberInclusion (cofibers B))
  maps : letI := T.enrichment
    ∀ {B D : StableInfinityCategory.{0}}, ExactFunctor B D → ((cofibers B).presheaf ⟶ (cofibers D).presheaf)
  coherent : letI := T.enrichment
    stableCategories A ⟶ V.presheaves.category.toSSet
  object_normalization : letI := T.enrichment
    ∀ B : StableInfinityCategory.{0}, coherent.app (op ⦋0⦌) (stableCategoryVertex A B) =
      presheafVertex V.presheaves (cofibers B).presheaf
  map_normalization : letI := T.enrichment
    ∀ (B D : StableInfinityCategory.{0}) (f : ExactFunctor B D),
    coherent.app (op ⦋1⦌) (sourceCategoryArrow A f) = presheafEdge V.presheaves (maps f)
  unit : letI := T.enrichment
    (mapping (stableCategories A) V.presheaves.category.toSSet) _⦋1⦌
  unit_source : letI := T.enrichment
    (mapping (stableCategories A) V.presheaves.category.toSSet).δ 1 unit = mappingZero _ _ V.infinityYoneda
  unit_target : letI := T.enrichment
    (mapping (stableCategories A) V.presheaves.category.toSSet).δ 0 unit = mappingZero _ _ coherent
  unit_normalization : letI := T.enrichment
    ∀ B : StableInfinityCategory.{0},
    (evaluateAt (stableCategories A) V.presheaves.category.toSSet (stableCategoryVertex A B)).app
      (op ⦋1⦌) unit = presheafEdge V.presheaves (augmentation B)
  zero : letI := T.enrichment
    IsZeroObject V.presheaves.category.toSSet
      (presheafVertex V.presheaves (cofibers V.zeroCategory.category.toStableInfinityCategory).presheaf)

variable {V}

def ReducedYonedaSource.presheaf (D : ReducedYonedaSource V) (B : StableInfinityCategory.{0}) :
    letI := T.enrichment; RawPresheaf T.index :=
  letI := T.enrichment
  (D.cofibers B).presheaf

/-- The split-row arrow is the native coproduct desc on the original inclusion and section,
preceded by the actual two cofibrant augmentations. -/
def additiveGenerator (D : ReducedYonedaSource V) (E : PerfectExactSequence)
    (Q : SplitPerfectExactSequence E) : letI := T.enrichment; letI := V.colimits
    RawMotiveGenerator (C := T.index) :=
  letI := T.enrichment
  letI := V.colimits
  { source := coprod (V.replacements.cofibrant.obj (D.presheaf E.left.toStableInfinityCategory))
      (V.replacements.cofibrant.obj (D.presheaf E.right.toStableInfinityCategory))
    target := D.presheaf E.middle.toStableInfinityCategory
    map := coprod.desc
      (V.replacements.cofibrant_augmentation.app (D.presheaf E.left.toStableInfinityCategory) ≫
        D.maps E.inclusion.functor)
      (V.replacements.cofibrant_augmentation.app (D.presheaf E.right.toStableInfinityCategory) ≫
        D.maps Q.sectionMap) }

def zeroGenerator (V : MotivePresheafSetup T S) : letI := T.enrichment
    RawMotiveGenerator (C := T.index) :=
  letI := T.enrichment
  { source := V.rawYoneda V.zeroCategory.category.toStableInfinityCategory
    target := V.zeroPresheaf.presheaf
    map := V.zeroPresheaf.terminal.from _ }

/-- Compactness is the actual coherent Catperf mapping/filtered-diagram test on all three source categories. -/
def IsCompactRow (A : StableCategoryEnrichment) (k : Cardinal.{0}) (E : PerfectExactSequence) : Prop :=
  IsCompactPerfectCategory A k E.left ∧ IsCompactPerfectCategory A k E.middle ∧
    IsCompactPerfectCategory A k E.right

def additiveGenerators (D : ReducedYonedaSource V) : letI := T.enrichment; letI := V.colimits
    Set (RawMotiveGenerator (C := T.index)) :=
  letI := T.enrichment
  letI := V.colimits
  {g | g = zeroGenerator V ∨ ∃ (E : PerfectExactSequence), IsCompactRow A k E ∧
    ∃ Q : SplitPerfectExactSequence E, g = additiveGenerator D E Q}

/-- The localizing arrow is the native universal extension into the exact-row square
after applying the full reduced Yoneda functor. Raw Y(0) is never treated as zero. -/
structure LocalizingGeneratorSource (D : ReducedYonedaSource V) (E : PerfectExactSequence)
    (Q : SourceExactSquare A V.zeroCategory E) where
  cofiber : letI := T.enrichment
    PresheafCofiber V.presheaves (D.maps E.inclusion.functor)
      (D.maps (zeroExactFunctor (V.zeroCategory.toZero E.left.toStableInfinityCategory)))
  target : letI := T.enrichment
    PresheafCocone V.presheaves (D.maps E.inclusion.functor)
      (D.maps (zeroExactFunctor (V.zeroCategory.toZero E.left.toStableInfinityCategory)))
  target_presheaf : letI := T.enrichment; target.presheaf = D.presheaf E.right.toStableInfinityCategory
  target_diagram : letI := T.enrichment
    coconeDiagram V.presheaves.category.toSSet
      (presheafSpan V.presheaves (D.maps E.inclusion.functor)
        (D.maps (zeroExactFunctor (V.zeroCategory.toZero E.left.toStableInfinityCategory)))) target.cocone =
      indexMap coconeSquareIndex ≫ Q.square ≫ D.coherent
  extension : letI := T.enrichment; PresheafCofiberExtension V.presheaves cofiber target

def LocalizingGeneratorSource.generator {D : ReducedYonedaSource V} {E : PerfectExactSequence}
    {Q : SourceExactSquare A V.zeroCategory E} (B : LocalizingGeneratorSource D E Q) :
    letI := T.enrichment; RawMotiveGenerator (C := T.index) :=
  letI := T.enrichment
  ⟨B.cofiber.presheaf, B.target.presheaf, B.extension.map⟩

structure LocalizingGeneratorFamily (D : ReducedYonedaSource V) where
  squares : ∀ E : PerfectExactSequence, SourceExactSquare A V.zeroCategory E
  generators : ∀ E : PerfectExactSequence, LocalizingGeneratorSource D E (squares E)

/-- The final BGT filtered relation retains the entire coherent filtered diagram,
its native cofinal model, all omega-compact terms, and its actual kappa-compact colimit. -/
structure FilteredPerfectPresentation (A : StableCategoryEnrichment) (k : Cardinal.{0}) where
  target : PerfectInfinityCategory.{0}
  target_compact : IsCompactPerfectCategory A k target
  index : SSet.{0}
  quasicategory : SSet.Quasicategory index
  cofinal : CofinalKappaIndex ℵ₀ index
  diagram : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj index ⟶ perfectCategories A
  compact_terms : ∀ i : index _⦋0⦌,
    IsKappaCompactVertex ℵ₀ (perfectCategories A) (diagram.app (op ⦋0⦌) (ULift.up i))
  cocone : (rightCones (perfectCategories A) (indexedDiagram cofinal diagram)) _⦋0⦌
  universal : IsInitialObject (rightCones (perfectCategories A) (indexedDiagram cofinal diagram)) cocone
  target_normalization : (coconeApexMap (perfectCategories A) (indexedDiagram cofinal diagram)).app
    (op ⦋0⦌) cocone = perfectCategoryVertex A target

def filteredPresheafDiagram (D : ReducedYonedaSource V) (F : FilteredPerfectPresentation A k) :
    letI := T.enrichment
    indexNerve.{1} F.cofinal.index ⟶ V.presheaves.category.toSSet :=
  letI := T.enrichment
  indexedDiagram F.cofinal F.diagram ≫
    ((stableCategories A).fullEnhancedSubcategory (IsPerfectCategoryVertex A)).ι ≫ D.coherent

def filteredPresheafAugmentedDiagram (D : ReducedYonedaSource V) (F : FilteredPerfectPresentation A k) :
    letI := T.enrichment
    indexNerve.{1} (WithTerminal F.cofinal.index) ⟶ V.presheaves.category.toSSet :=
  letI := T.enrichment
  coconeDiagram (perfectCategories A) (indexedDiagram F.cofinal F.diagram) F.cocone ≫
    ((stableCategories A).fullEnhancedSubcategory (IsPerfectCategoryVertex A)).ι ≫ D.coherent

/-- The presheaf source colimit is the whole native universal cocone on the original indexed diagram. -/
structure PresheafDiagramColimit {C : Type} [EnrichedCategory SymmetricSpectrum C]
    {S : SpectrumInfinitySource} (P : NativeSpectralPresheafModels.PresheafInfinitySource C S)
    {I : Type} [Category.{0} I] (d : indexNerve.{1} I ⟶ P.category.toSSet) where
  presheaf : RawPresheaf C
  cocone : (rightCones P.category.toSSet d) _⦋0⦌
  apex : (coconeApexMap P.category.toSSet d).app (op ⦋0⦌) cocone = presheafVertex P presheaf
  universal : IsInitialObject (rightCones P.category.toSSet d) cocone

/-- The final filtered comparison is the apex of the original whole cocone arrow,
whose target is the image of the actual Catperf universal cocone. -/
structure FilteredPresheafComparison (D : ReducedYonedaSource V) (F : FilteredPerfectPresentation A k) where
  colimit : letI := T.enrichment
    PresheafDiagramColimit V.presheaves (filteredPresheafDiagram D F)
  target : letI := T.enrichment
    (rightCones V.presheaves.category.toSSet (filteredPresheafDiagram D F)) _⦋0⦌
  target_normalization : letI := T.enrichment
    coconeDiagram V.presheaves.category.toSSet (filteredPresheafDiagram D F) target =
      filteredPresheafAugmentedDiagram D F
  edge : letI := T.enrichment
    (rightCones V.presheaves.category.toSSet (filteredPresheafDiagram D F)) _⦋1⦌
  source : letI := T.enrichment
    (rightCones V.presheaves.category.toSSet (filteredPresheafDiagram D F)).δ 1 edge = colimit.cocone
  destination : letI := T.enrichment
    (rightCones V.presheaves.category.toSSet (filteredPresheafDiagram D F)).δ 0 edge = target
  map : letI := T.enrichment; colimit.presheaf ⟶ D.presheaf F.target.toStableInfinityCategory
  normalized : letI := T.enrichment
    SameArrow V.presheaves.category.toSSet (presheafEdge V.presheaves map)
      ((coconeApexMap V.presheaves.category.toSSet (filteredPresheafDiagram D F)).app (op ⦋1⦌) edge)

def FilteredPresheafComparison.generator {D : ReducedYonedaSource V} {F : FilteredPerfectPresentation A k}
    (B : FilteredPresheafComparison D F) : letI := T.enrichment; RawMotiveGenerator (C := T.index) :=
  letI := T.enrichment
  ⟨B.colimit.presheaf, D.presheaf F.target.toStableInfinityCategory, B.map⟩

structure FilteredComparisonFamily (D : ReducedYonedaSource V) where
  comparisons : ∀ F : FilteredPerfectPresentation A k, FilteredPresheafComparison D F

/-- This is the final localizing localization, including the BGT Section 8.3 filtered relation. -/
def localizingGenerators (D : ReducedYonedaSource V) (L : LocalizingGeneratorFamily D)
    (F : FilteredComparisonFamily D) : letI := T.enrichment; letI := V.colimits
    Set (RawMotiveGenerator (C := T.index)) :=
  letI := T.enrichment
  letI := V.colimits
  {g | g ∈ additiveGenerators D ∨
    (∃ E : PerfectExactSequence, IsCompactRow A k E ∧ g = (L.generators E).generator) ∨
    ∃ J : FilteredPerfectPresentation A k, g = (F.comparisons J).generator}

def additiveMotive {T : SpectralCompactSource A ℵ₀} (V : MotivePresheafSetup T S)
    (D : ReducedYonedaSource V) : Type 2 :=
  letI := T.enrichment
  letI := V.colimits
  MotiveLocalization V.presheaves V.ends V.replacements (additiveGenerators D)

def localizingMotive {k : UncountableRegularCardinal} {T : SpectralCompactSource A k.value}
    (V : MotivePresheafSetup T S) (D : ReducedYonedaSource V)
    (L : LocalizingGeneratorFamily D) (F : FilteredComparisonFamily D) : Type 2 :=
  letI := T.enrichment
  letI := V.colimits
  MotiveLocalization V.presheaves V.ends V.replacements (localizingGenerators D L F)

end MathlibExt.AlgebraicTopology.NativeMotiveGenerators
