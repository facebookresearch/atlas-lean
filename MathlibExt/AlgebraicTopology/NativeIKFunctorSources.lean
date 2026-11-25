/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.BGTNativeNonconnectiveModels
public import MathlibExt.AlgebraicTopology.NativeKCorepresentabilityModels

/-!
# Full coherent functoriality of the original native nonconnective tower

The terms, transitions and colimits are precisely the published native
Omega^n QK(Sigma^n A) tower. Full suspension parameters extend the same
actual Ind/Verdier maps. Loop parameters are fixed by the native closed
composition map and the original enriched fibrant replacement.

The whole tower and augmented cocone are actual coherent functors. Their
term restrictions are the native full Sigma/S/loop enriched functors;
ordinary arrows are the original source tower maps. IK is evaluated at
the apex of that same augmented cocone. No motive equivalence defines it.

Sources: BGT arXiv:1001.2282v4 Definition 9.6 and Section 9.1;
HSS Sections 2.2/3.1--3.4. Published source pins/licenses remain in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeIKFunctorSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open MathlibExt.SpectraSource
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels StableInfinityMappingSpaces
open StableInfinityFiniteDiagrams
open StableInfinityFilteredColimits NativeDiagramFamilies NativeSpectrumConeSources
open NativeSpectrumBoundarySources NativeSpectraSimplicialSource NativeSpectrumFunctionEvaluation
open NativeEnrichedSpectrumReplacements NativeDerivedSpectrumModels NativeKParametrizedSource
open NativeCompactSourceModels NativeMotivePresheafSources NativeMotiveGenerators NativeMotiveLocalizationModels
open NativeKCorepresentabilityModels BGTNativeNonconnectiveModels BGTIndKappaModels
open StableInfinityKSpectra StableSpectraInfinitySource
open scoped Simplicial Cardinal MonoidalClosed

/-- The entire suspension enrichment, a coherent enriched functor extending the native
Ind/Verdier exact maps up to natural equivalence. -/
structure SigmaFunctorAction (A : StableCategoryEnrichment) {k : UncountableRegularCardinal}
    (P : SigmaKappaSystem k) where
  hom : letI := A.enrichment
    ∀ C D : StableInfinityCategory.{0}, (C ⟶[SSet.{0}] D) ⟶
      (sigmaCategory (P.source C) ⟶[SSet.{0}] sigmaCategory (P.source D))
  identity : letI := A.enrichment
    ∀ C : StableInfinityCategory.{0}, eId SSet.{0} C ≫ hom C C = eId SSet.{0} (sigmaCategory (P.source C))
  composition : letI := A.enrichment
    ∀ C D E : StableInfinityCategory.{0}, eComp SSet.{0} C D E ≫ hom C E =
      (hom C D ⊗ₘ hom D E) ≫ eComp SSet.{0}
        (sigmaCategory (P.source C)) (sigmaCategory (P.source D)) (sigmaCategory (P.source E))
  /-- On an exact functor the action agrees with the supplied Verdier map up to a natural
  equivalence: an edge of the core of exact functors joins the two vertices. The supplied maps
  are chosen separately for each functor, up to natural equivalence, so equality would be
  incompatible with the strict identity and composition laws. -/
  ordinary : letI := A.enrichment
    ∀ (C D : StableInfinityCategory.{0}) (f : ExactFunctor C D),
      ∃ e : (sigmaCategory (P.source C) ⟶[SSet.{0}] sigmaCategory (P.source D)) _⦋1⦌,
        (sigmaCategory (P.source C) ⟶[SSet.{0}] sigmaCategory (P.source D)).δ 1 e =
            SSet.unitHomEquiv _ (exactHomPoint A f ≫ hom C D) ∧
          (sigmaCategory (P.source C) ⟶[SSet.{0}] sigmaCategory (P.source D)).δ 0 e =
            SSet.unitHomEquiv _ (exactHomPoint A (P.map f).functor)

def SigmaFunctorAction.functor {A : StableCategoryEnrichment} {k : UncountableRegularCardinal}
    {P : SigmaKappaSystem k} (H : SigmaFunctorAction A P) :
    letI := A.enrichment
    EnrichedFunctor SSet.{0} StableInfinityCategory.{0} StableInfinityCategory.{0} :=
  letI := A.enrichment
  { obj := fun C => sigmaCategory (P.source C)
    map := H.hom
    map_id := H.identity
    map_comp := H.composition }

def SigmaFunctorAction.power {A : StableCategoryEnrichment} {k : UncountableRegularCardinal}
    {P : SigmaKappaSystem k} (H : SigmaFunctorAction A P) (n : ℕ) :
    letI := A.enrichment
    EnrichedFunctor SSet.{0} StableInfinityCategory.{0} StableInfinityCategory.{0} :=
  letI := A.enrichment
  match n with
  | 0 => EnrichedFunctor.id SSet.{0} _
  | n + 1 => (H.power n).comp SSet.{0} H.functor

/-- All native internal-Hom parameters are sent by the original closed composition/currying map. -/
def internalHomParameterMap (T E F : SymmetricSpectrum) :
    nativeFunctionSpace E F ⟶ nativeFunctionSpace ((Mod.internalHom T).obj E) ((Mod.internalHom T).obj F) :=
  ((SymmetricSpectrum.evaluation 0).map
    (MonoidalClosed.curry (eComp SymmetricSpectrum T E F))).right

def fibrantParameterMap {N : SpectrumSimplicialEnrichment} {S : SpectrumInfinitySource}
    (R : EnrichedSpectrumReplacements N S) (E F : SymmetricSpectrum) :
    nativeFunctionSpace E F ⟶ nativeFunctionSpace (R.replacements.fibrant.obj E) (R.replacements.fibrant.obj F) :=
  letI := N.ordinary
  eqToHom (N.hom_normalization E F).symm ≫ R.fibrant.hom E F ≫ eqToHom (N.hom_normalization _ _)

def loopParameterMap {N : SpectrumSimplicialEnrichment} {S : SpectrumInfinitySource}
    (R : EnrichedSpectrumReplacements N S) (E F : SymmetricSpectrum) :
    nativeFunctionSpace E F ⟶ nativeFunctionSpace
      ((derivedLoopFunctor R.replacements).obj E) ((derivedLoopFunctor R.replacements).obj F) :=
  fibrantParameterMap R E F ≫ internalHomParameterMap circleSpectrum _ _

def loopPowerParameterMap {N : SpectrumSimplicialEnrichment} {S : SpectrumInfinitySource}
    (R : EnrichedSpectrumReplacements N S) (n : ℕ) (E F : SymmetricSpectrum) :
    nativeFunctionSpace E F ⟶ nativeFunctionSpace
      ((derivedLoopPower R.replacements n).obj E) ((derivedLoopPower R.replacements n).obj F) :=
  match n with
  | 0 => 𝟙 _
  | n + 1 => loopParameterMap R E F ≫ loopPowerParameterMap R n _ _

/-- The generic proof source must use precisely these full native closed-loop maps. -/
structure LoopFunctorActions (N : SpectrumSimplicialEnrichment) {S : SpectrumInfinitySource}
    (R : EnrichedSpectrumReplacements N S) where
  action : ∀ n : ℕ, SpectrumFunctorAction N (derivedLoopPower R.replacements n)
  normalization : letI := N.ordinary
    ∀ (n : ℕ) (E F : SymmetricSpectrum),
      eqToHom (N.hom_normalization E F).symm ≫ (action n).hom E F ≫
        eqToHom (N.hom_normalization _ _) = loopPowerParameterMap R n E F

variable {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
  {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
  (K : ParametrizedKSource A N) (R : EnrichedSpectrumReplacements N S)
  (L : SpectrumCoherentLocalization N S) {k : UncountableRegularCardinal} (P : SigmaKappaSystem k)
  (B : ∀ C : StableInfinityCategory.{0}, KBoundaryStage Z K R L P C)

def termEnrichedFunctor (sig : SigmaFunctorAction A P) (loop : LoopFunctorActions N R) (n : ℕ) :
    letI := A.enrichment; letI := N.ordinary
    EnrichedFunctor SSet.{0} StableInfinityCategory.{0} SymmetricSpectrum :=
  letI := A.enrichment
  letI := N.ordinary
  (((sig.power n).comp SSet.{0} (nativeKEnrichedFunctor K.maps)).comp SSet.{0} R.cofibrant.functor).comp
    SSet.{0} (loop.action n).functor

def termSimplicialFunctor (sig : SigmaFunctorAction A P) (loop : LoopFunctorActions N R) (n : ℕ) :
    letI := A.enrichment; letI := N.ordinary
    EnrichedFunctor SSet.{0} (ForgetEnrichment SSet.{0} StableInfinityCategory.{0}) SymmetricSpectrum :=
  letI := A.enrichment
  letI := N.ordinary
  let F := termEnrichedFunctor K R P sig loop n
  { obj := fun C => F.obj (ForgetEnrichment.to SSet.{0} C)
    map := fun C D => F.map (ForgetEnrichment.to SSet.{0} C) (ForgetEnrichment.to SSet.{0} D)
    map_id := fun C => F.map_id _
    map_comp := fun C D E => F.map_comp _ _ _ }

def termInfinityFunctor (sig : SigmaFunctorAction A P) (loop : LoopFunctorActions N R) (n : ℕ) :
    stableCategories A ⟶ S.category.toSSet :=
  letI := A.enrichment
  letI := N.ordinary
  simplicialNerveMap (termSimplicialFunctor K R P sig loop n) ≫ L.map

/-- Full naturality is imposed on every term of the actual tower, and the whole
augmented cocone is the original universal source colimit, including all higher parameters. -/
structure NativeIKSource where
  sigma : SigmaFunctorAction A P
  loops : LoopFunctorActions N R
  colimits : ∀ C : StableInfinityCategory.{0},
    SpectrumSequentialColimit S (nonconnectiveTower K R L P B C)
  maps : ∀ {C D : StableInfinityCategory.{0}} (f : ExactFunctor C D), SourceTowerMap K R L P B f
  tower : stableCategories A ⟶ mapping (indexNerve.{1} ℕ) S.category.toSSet
  tower_objects : ∀ C : StableInfinityCategory.{0}, tower.app (op ⦋0⦌) (stableCategoryVertex A C) =
    mappingZero _ _ (stableSequenceDiagram S (nonconnectiveTower K R L P B C))
  tower_arrows : ∀ (C D : StableInfinityCategory.{0}) (f : ExactFunctor C D),
    tower.app (op ⦋1⦌) (sourceCategoryArrow A f) = (maps f).edge
  all_terms : ∀ n : ℕ,
    tower ≫ evaluateAt (indexNerve.{1} ℕ) S.category.toSSet
      (ULift.up (ComposableArrows.mk₀ n)) = termInfinityFunctor K R L P sigma loops n
  cocones : stableCategories A ⟶ mapping (indexNerve.{1} (WithTerminal ℕ)) S.category.toSSet
  restriction : cocones ≫ precomposition (indexMap (WithTerminal.incl (C := ℕ))) S.category.toSSet = tower
  cocone_objects : ∀ C : StableInfinityCategory.{0}, cocones.app (op ⦋0⦌) (stableCategoryVertex A C) =
    mappingZero _ _ (coconeDiagram S.category.toSSet
      (stableSequenceDiagram S (nonconnectiveTower K R L P B C)) (colimits C).cocone)

variable {K R L P B}

/-- This is IK of the original S/loop/Sigma tower, not a motive Hom. -/
def NativeIKSource.spectrum (I : NativeIKSource K R L P B) (C : StableInfinityCategory.{0}) : SymmetricSpectrum :=
  (I.colimits C).spectrum

def NativeIKSource.infinityFunctor (I : NativeIKSource K R L P B) :
    stableCategories A ⟶ S.category.toSSet :=
  I.cocones ≫ evaluateAt (indexNerve.{1} (WithTerminal ℕ)) S.category.toSSet
    (ULift.up (ComposableArrows.mk₀ WithTerminal.star))

def NativeIKSource.perfectFunctor (I : NativeIKSource K R L P B) :
    perfectCategories A ⟶ S.category.toSSet :=
  ((stableCategories A).fullEnhancedSubcategory (IsPerfectCategoryVertex A)).ι ≫ I.infinityFunctor

/-- Localizing-invariant properties concern that same original full coherent IK functor. -/
structure NativeIKLocalizing (I : NativeIKSource K R L P B) where
  filtered : PreservesKappaFilteredColimits ℵ₀ I.perfectFunctor
  zero : ∀ Z : ZeroCategorySource,
    IsZeroObject S.category.toSSet (I.infinityFunctor.app (op ⦋0⦌)
      (stableCategoryVertex A Z.category.toStableInfinityCategory))
  exact : ∀ (Z : ZeroCategorySource) (E : PerfectExactSequence) (Q : SourceExactSquare A Z E),
    IsPushoutSquare (Q.square ≫ I.infinityFunctor)

end MathlibExt.AlgebraicTopology.NativeIKFunctorSources
