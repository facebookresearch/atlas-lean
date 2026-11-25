/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeKParametrizedSource
public import MathlibExt.AlgebraicTopology.NativeEnrichedSpectrumReplacements
public import MathlibExt.AlgebraicTopology.NativeSpectrumCoherentSquares
public import MathlibExt.AlgebraicTopology.BGTIndSigmaFunctorMaps
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The native BGT nonconnective spectrum and its canonical tower

Sigma is the actual Verdier quotient of the kappa-compact Ind cone.
At each stage the source quotient-zero natural equivalence is sent
through the full S/K action and native enriched cofibrant replacement.
The entire coherent square retains that precise function homotopy.
Its native zero-middle loop boundary supplies the tower transition.

The terms are the actual native spectra Omega^n QK(Sigma^n A).
The nonconnective spectrum is their actual universal coherent colimit.
No K spectrum, vanishing or motive equivalence defines Sigma or Ind.
In particular no all-exact-sequence connective cofiber equivalence is
asserted. The zero-middle contraction is a construction output.

Source: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4,
Definitions 9.1 and 9.6, Lemma 9.4 and Proposition 9.5, pages 57--58.
Native spectrum, enriched Hom and ordinal-sequence constructors retain
their original Mathlib/Tau Ceti source attribution in the imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.BGTNativeNonconnectiveModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels StableInfinityFilteredColimits
open StableInfinityFiniteDiagrams StableInfinityMappingSpaces NativeDiagramFamilies
open StableInfinityKSpectra BGTIndKappaModels BGTIndSigmaFunctorMaps BGTVerdierQuotients
open NativeKParametrizedSource NativeSpectraSimplicialSource NativeSpectrumFunctionEvaluation
open NativeEnrichedSpectrumReplacements NativeDerivedSpectrumModels StableSpectraInfinitySource
open NativeSpectrumConeSources NativeSpectrumBoundarySources NativeSpectrumCoherentSquares
open StableInfinitySParametrizedAction
open MathlibExt.SpectraSource
open scoped Simplicial

/-- The source suspension objects and native maps use the same original Ind/Verdier constructions. -/
structure SigmaKappaSystem (k : UncountableRegularCardinal) where
  source : ∀ C : StableInfinityCategory.{0}, SigmaKappaSource C k
  map : ∀ {C D : StableInfinityCategory.{0}} (f : ExactFunctor C D),
    SigmaKappaFunctorMap (source C) (source D) f

/-- Every suspension iterate is the original source Verdier quotient. -/
def sigmaPower {k : UncountableRegularCardinal} (P : SigmaKappaSystem k)
    (C : StableInfinityCategory.{0}) (n : ℕ) : StableInfinityCategory.{0} :=
  match n with
  | 0 => C
  | n + 1 => sigmaCategory (P.source (sigmaPower P C n))

/-- Its native map is induced by the same successive source quotient functors. -/
def sigmaPowerMap {k : UncountableRegularCardinal} (P : SigmaKappaSystem k)
    {C D : StableInfinityCategory.{0}} (f : ExactFunctor C D) (n : ℕ) :
    ExactFunctor (sigmaPower P C n) (sigmaPower P D n) :=
  match n with
  | 0 => f
  | n + 1 => (P.map (sigmaPowerMap P f n)).functor

/-- This is the original native cofibrant replacement of the source S-construction spectrum. -/
def cofibrantK {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} (K : ParametrizedKSource A N)
    (R : EnrichedSpectrumReplacements N S) (C : StableInfinityCategory.{0}) : SymmetricSpectrum :=
  R.replacements.cofibrant.obj (connectiveK K.construction C)

/-- The native exact map is taken by the original cofibrant functor, with no independent transition callback. -/
def cofibrantKMap {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} (K : ParametrizedKSource A N)
    (R : EnrichedSpectrumReplacements N S) {C D : StableInfinityCategory.{0}}
    (f : ExactFunctor C D) : cofibrantK K R C ⟶ cofibrantK K R D :=
  R.replacements.cofibrant.map (connectiveKMap K.construction f)

/-- The entire original quotient homotopy is transported through the native enriched replacement. -/
def cofibrantQuotientHomotopy {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} (K : ParametrizedKSource A N)
    (R : EnrichedSpectrumReplacements N S) (E : StableExactSequence.{0})
    {Z : ZeroExactFunctorSource E.left E.right} (Q : QuotientZeroReversePath E Z) :
    (nativeFunctionSpace (cofibrantK K R E.left) (cofibrantK K R E.right)) _⦋1⦌ :=
  (cofibrantParameterMap R (connectiveK K.construction E.left)
    (connectiveK K.construction E.right)).app (op ⦋1⦌) (nativeKQuotientReverseHomotopy K E Q)

/-- A source stage fixes the whole original S/quotient homotopy before constructing its boundary. -/
structure KBoundaryStage {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} (Z : SpectrumZeroSource S)
    (K : ParametrizedKSource A N) (R : EnrichedSpectrumReplacements N S)
    (L : SpectrumCoherentLocalization N S) {k : UncountableRegularCardinal}
    (P : SigmaKappaSystem k) (C : StableInfinityCategory.{0}) where
  zero_functor : ZeroExactFunctorSource C (sigmaCategory (P.source C))
  quotient_path : QuotientZeroReversePath (P.source C).exactSequence zero_functor
  square : CoherentZeroSquare N S Z
    (cofibrantKMap K R (P.source C).cone.inclusion.functor)
    (cofibrantKMap K R (P.source C).quotient.quotient)
    (cofibrantQuotientHomotopy K R (P.source C).exactSequence quotient_path)
  loop : SpectrumLoop S R.replacements (cofibrantK K R (sigmaCategory (P.source C)))
  boundary : SpectrumBoundary (square.stableTriangle L) loop
  rectification : PointsetBoundary boundary

/-- The native source-normalized boundary has this original point-set representative. -/
def KBoundaryStage.map {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    {K : ParametrizedKSource A N} {R : EnrichedSpectrumReplacements N S}
    {L : SpectrumCoherentLocalization N S} {k : UncountableRegularCardinal}
    {P : SigmaKappaSystem k} {C : StableInfinityCategory.{0}} (B : KBoundaryStage Z K R L P C) :
    cofibrantK K R C ⟶ (derivedLoopFunctor R.replacements).obj
      (cofibrantK K R (sigmaCategory (P.source C))) := B.rectification.map

/-- Boundary stages that are natural in the category: for every exact functor the two boundary
composites are homotopic arrows of the stable category. Each stage only fixes its loop object,
not the cone's loop coordinate, so independently chosen stages can differ, e.g. by the sign of
one loop coordinate, and then no map of nonconnective towers commutes with both boundaries. -/
def IsNaturalBoundary {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} (Z : SpectrumZeroSource S)
    (K : ParametrizedKSource A N) (R : EnrichedSpectrumReplacements N S)
    (L : SpectrumCoherentLocalization N S) {k : UncountableRegularCardinal}
    (P : SigmaKappaSystem k) (B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C) :
    Prop :=
  ∀ {C D : StableInfinityCategory.{0}} (f : ExactFunctor C D),
    SameArrow S.category.toSSet
      (S.edge ((B C).map ≫ (derivedLoopFunctor R.replacements).map
        (cofibrantKMap K R (P.map f).functor)))
      (S.edge (cofibrantKMap K R f ≫ (B D).map))

/-- The n-th native term is exactly Omega^n QK of the original n-fold Verdier suspension. -/
def towerTerm {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} (K : ParametrizedKSource A N)
    (R : EnrichedSpectrumReplacements N S) {k : UncountableRegularCardinal}
    (P : SigmaKappaSystem k) (C : StableInfinityCategory.{0}) (n : ℕ) : SymmetricSpectrum :=
  (derivedLoopPower R.replacements n).obj (cofibrantK K R (sigmaPower P C n))

/-- Every transition is the actual iterated native loop image of that stage's fixed boundary. -/
def towerTransition {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    (K : ParametrizedKSource A N) (R : EnrichedSpectrumReplacements N S)
    (L : SpectrumCoherentLocalization N S) {k : UncountableRegularCardinal}
    (P : SigmaKappaSystem k) (B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C)
    (C : StableInfinityCategory.{0}) (n : ℕ) :
    towerTerm K R P C n ⟶ towerTerm K R P C (n + 1) :=
  (derivedLoopPower R.replacements n).map (B (sigmaPower P C n)).map

/-- The entire native ordinal functor is computed from those actual transitions. -/
def nonconnectiveTower {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    (K : ParametrizedKSource A N) (R : EnrichedSpectrumReplacements N S)
    (L : SpectrumCoherentLocalization N S) {k : UncountableRegularCardinal}
    (P : SigmaKappaSystem k) (B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C)
    (C : StableInfinityCategory.{0}) : ℕ ⥤ SymmetricSpectrum :=
  Functor.ofSequence (towerTransition K R L P B C)

/-- The actual whole spectrum diagram in the fixed stable source. -/
def stableSequenceDiagram (S : SpectrumInfinitySource) (D : ℕ ⥤ SymmetricSpectrum) :
    indexNerve.{1} ℕ ⟶ S.category.toSSet := liftedNerveMap D ≫ S.source

/-- The native derived sequential colimit is the universal coherent cocone on this exact diagram. -/
structure SpectrumSequentialColimit (S : SpectrumInfinitySource) (D : ℕ ⥤ SymmetricSpectrum) where
  spectrum : SymmetricSpectrum
  cocone : (rightCones S.category.toSSet (stableSequenceDiagram S D)) _⦋0⦌
  apex : (coconeApexMap S.category.toSSet (stableSequenceDiagram S D)).app (op ⦋0⦌) cocone =
    S.vertex spectrum
  universal : IsInitialObject (rightCones S.category.toSSet (stableSequenceDiagram S D)) cocone

/-- The nonconnective spectrum is the actual colimit of the already fixed source boundary tower. -/
def nonconnectiveK {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    (K : ParametrizedKSource A N) (R : EnrichedSpectrumReplacements N S)
    (L : SpectrumCoherentLocalization N S) {k : UncountableRegularCardinal}
    (P : SigmaKappaSystem k) (B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C)
    (C : StableInfinityCategory.{0}) (T : SpectrumSequentialColimit S (nonconnectiveTower K R L P B C)) :
    SymmetricSpectrum := T.spectrum

/-- The original exact-functor component uses the same source Sigma map and native loop functor. -/
def towerComponent {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} (K : ParametrizedKSource A N)
    (R : EnrichedSpectrumReplacements N S) {k : UncountableRegularCardinal}
    (P : SigmaKappaSystem k) {C D : StableInfinityCategory.{0}} (f : ExactFunctor C D) (n : ℕ) :
    towerTerm K R P C n ⟶ towerTerm K R P D n :=
  (derivedLoopPower R.replacements n).map (cofibrantKMap K R (sigmaPowerMap P f n))

/-- A whole sequence-map arrow retains every parameter and ordinal arrow. -/
structure StableSequenceMap (S : SpectrumInfinitySource) (D E : ℕ ⥤ SymmetricSpectrum) where
  edge : (mapping (indexNerve ℕ) S.category.toSSet) _⦋1⦌
  source : (mapping (indexNerve ℕ) S.category.toSSet).δ 1 edge = mappingZero _ _ (stableSequenceDiagram S D)
  target : (mapping (indexNerve ℕ) S.category.toSSet).δ 0 edge = mappingZero _ _ (stableSequenceDiagram S E)

/-- The canonical exact-functor sequence arrow is fixed on every original native term map. -/
structure SourceTowerMap {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    (K : ParametrizedKSource A N) (R : EnrichedSpectrumReplacements N S)
    (L : SpectrumCoherentLocalization N S) {k : UncountableRegularCardinal}
    (P : SigmaKappaSystem k) (B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C)
    {C D : StableInfinityCategory.{0}} (f : ExactFunctor C D) extends
    StableSequenceMap S (nonconnectiveTower K R L P B C) (nonconnectiveTower K R L P B D) where
  component_normalization : ∀ n : ℕ,
    SameArrow S.category.toSSet
      ((evaluateAt (indexNerve ℕ) S.category.toSSet
        (ULift.up (ComposableArrows.mk₀ n))).app (op ⦋1⦌) edge)
      (S.edge (towerComponent K R P f n))

/-- A map of native derived colimits is the apex of the original whole cocone-map arrow. -/
structure SpectrumColimitMap {S : SpectrumInfinitySource} {D E : ℕ ⥤ SymmetricSpectrum}
    (a : StableSequenceMap S D E) (C : SpectrumSequentialColimit S D)
    (F : SpectrumSequentialColimit S E) where
  edge : (mapping (indexNerve (WithTerminal ℕ)) S.category.toSSet) _⦋1⦌
  source : (mapping (indexNerve (WithTerminal ℕ)) S.category.toSSet).δ 1 edge =
    mappingZero _ _ (coconeDiagram S.category.toSSet (stableSequenceDiagram S D) C.cocone)
  target : (mapping (indexNerve (WithTerminal ℕ)) S.category.toSSet).δ 0 edge =
    mappingZero _ _ (coconeDiagram S.category.toSSet (stableSequenceDiagram S E) F.cocone)
  restriction : (precomposition (indexMap (WithTerminal.incl (C := ℕ))) S.category.toSSet).app (op ⦋1⦌) edge = a.edge

/-- The colimit map is evaluated on the same original augmented coherent arrow. -/
def SpectrumColimitMap.map {S : SpectrumInfinitySource} {D E : ℕ ⥤ SymmetricSpectrum}
    {a : StableSequenceMap S D E} {C : SpectrumSequentialColimit S D}
    {F : SpectrumSequentialColimit S E} (b : SpectrumColimitMap a C F) : S.category.toSSet _⦋1⦌ :=
  (evaluateAt (indexNerve (WithTerminal ℕ)) S.category.toSSet
    (ULift.up (ComposableArrows.mk₀ WithTerminal.star))).app (op ⦋1⦌) b.edge

/-- The localizing theorem has the actual IK maps as its two original source arrows. -/
structure NonconnectiveExactSquare {S : SpectrumInfinitySource}
    (Z : SpectrumZeroSource S) {D E F : ℕ ⥤ SymmetricSpectrum}
    (a : StableSequenceMap S D E) (b : StableSequenceMap S E F)
    (C_D : SpectrumSequentialColimit S D) (C_E : SpectrumSequentialColimit S E)
    (C_F : SpectrumSequentialColimit S F)
    (m_a : SpectrumColimitMap a C_D C_E) (m_b : SpectrumColimitMap b C_E C_F) where
  square : indexNerve.{1} SquareCorner ⟶ S.category.toSSet
  origin : cornerValue square .origin = S.vertex C_D.spectrum
  horizontal : cornerValue square .horizontal = S.vertex C_E.spectrum
  vertical : cornerValue square .vertical = S.vertex zeroSpectrum
  final : cornerValue square .final = S.vertex C_F.spectrum
  first_map : square.app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk (homOfLE (originLE .horizontal))).edge) = m_a.map
  second_map : square.app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk (homOfLE (finalLE .horizontal))).edge) = m_b.map
  zero_map : square.app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk (homOfLE (originLE .vertical))).edge) =
      S.edge (toZeroSpectrum Z C_D.spectrum)
  universal : IsPushoutSquare square

end MathlibExt.AlgebraicTopology.BGTNativeNonconnectiveModels
