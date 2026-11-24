/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeEtaleCoefficientSourceModels
public import MathlibExt.AlgebraicGeometry.GeneralCoefficientHyperdescentModels
public import MathlibExt.AlgebraicTopology.NativeDiagramFamilies

/-!
# The native K-injective coefficient source and full derived-family fibre

All K-injective objects are the original left-coefficient sheaf complexes.
Their full DG enrichment is the original sheaf cochain Hom in every
degree. The replacement source normalizes its entire ordinary functor
through the native simplicial source and full DG inclusion.

The fibre comparison is a map of full enhanced categories. Its source
comparison on all cochain complexes is the image of the actual native
replacement augmentation, on every parameter object and arrow. It is
not a collection of unrelated object equivalences.

Sources: Keller, *Deriving DG categories*, Section2; Lurie, Higher Algebra,
Section1.3.1; Bhatt--Mathew1807.04725v4, Notation5.8/Theorem5.13.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeEtaleDerivedFibreModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open GeneralArcCoverModels GeneralEtaleCoefficientModels GeneralEtalePullbackCoherence
open GeneralEtaleCoherentFamilies GeneralEtaleDerivedEnhancements
open GeneralCoefficientHyperdescentModels NativeEtaleCoefficientSourceModels
open MathlibExt.DGSource MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels MathlibExt.CategoryTheory.NativeDGNerveModels
open SimplicialDerivedModels
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.NativeDiagramFamilies
open MathlibExt.AlgebraicTopology.SimplicialCovariantModels
open MathlibExt.AlgebraicTopology.StableInfinityMappingSpaceMaps
open scoped Simplicial

variable (Λ : Type) [Ring Λ]
  [∀ Y : Scheme.{0}, HasSheafify Y.smallEtaleTopology (ModuleCat.{1} Λ)]
  (X : QcqsScheme) (N : CoefficientDGOrdinarySource Λ X.scheme)

/-- The original full native K-injective DG objects, with the exact coefficient enrichment. -/
def kinjectiveSimplicialCategory : Type 2 :=
  letI := N.ordinary
  letI : DGCategory LargeInt (CoefficientComplexes Λ X.scheme) := N.ordinary.toEnrichedCategory
  DGSimplicial (k := LargeInt) (DGFullSubcategory (IsKInjective (Λ := Λ) (X := X.scheme)))

instance kinjectiveCategory : Category.{1} (kinjectiveSimplicialCategory Λ X N) :=
  letI := N.ordinary
  letI : DGCategory LargeInt (CoefficientComplexes Λ X.scheme) := N.ordinary.toEnrichedCategory
  _root_.CategoryTheory.categoryForgetEnrichment (W := SSet.{1})
    (C := DGSimplicialCategory LargeInt
      (DGFullSubcategory (IsKInjective (Λ := Λ) (X := X.scheme))))

/-- The full K-injective source retains its native unit-shaped ordinary Hom. -/
instance kinjectiveSimplicial : SimplicialCategory (kinjectiveSimplicialCategory Λ X N) :=
  letI := N.ordinary
  letI : DGCategory LargeInt (CoefficientComplexes Λ X.scheme) := N.ordinary.toEnrichedCategory
  ForgetEnrichment.enrichedOrdinaryCategory (V := SSet.{1})

/-- The original full DG inclusion acts identically on every actual cochain Hom. -/
def kinjectiveInclusion : kinjectiveSimplicialCategory Λ X N ⥤ sourceSimplicialCategory Λ X.scheme N :=
  letI := N.ordinary
  letI : DGCategory LargeInt (CoefficientComplexes Λ X.scheme) := N.ordinary.toEnrichedCategory
  let E : EnrichedFunctor SSet.{1} (kinjectiveSimplicialCategory Λ X N)
      (sourceSimplicialCategory Λ X.scheme N) :=
    dgSimplicialFunctor (DGFullSubcategory.inclusion (R := LargeInt)
      (P := IsKInjective (Λ := Λ) (X := X.scheme)))
  ForgetEnrichment.equivInverse SSet.{1} (kinjectiveSimplicialCategory Λ X N) ⋙
    E.forget ⋙ ForgetEnrichment.equivFunctor SSet.{1} (sourceSimplicialCategory Λ X.scheme N)

/-- The source full coherent K-injective nerve. -/
def kinjectiveNerve : SSet.{2} :=
  letI := N.ordinary
  SimplicialNerve (kinjectiveSimplicialCategory Λ X N)

/-- A source object remains its original underlying coefficient sheaf complex. -/
def underlyingComplex (a : kinjectiveSimplicialCategory Λ X N) : CoefficientComplexes Λ X.scheme :=
  letI := N.ordinary
  ((ForgetEnrichment.to SSet.{1} a).underlying LargeInt).obj

/-- The source vertex identifies its actual original full K-injective complex. -/
def vertexComplex (a : (kinjectiveNerve Λ X N) _⦋0⦌) : CoefficientComplexes Λ X.scheme :=
  letI := N.ordinary
  underlyingComplex Λ X N (SimplicialNerve.vertexEquiv (kinjectiveSimplicialCategory Λ X N) a)

variable (F : CoefficientSimplicialFunctorSource Λ X.scheme N)

/-- Functorial native replacement has its entire source functor fixed, before localization. -/
structure KInjectiveResolutionSource where
  replacement : CoefficientComplexes Λ X.scheme ⥤ CoefficientComplexes Λ X.scheme
  augmentation : 𝟭 (CoefficientComplexes Λ X.scheme) ⟶ replacement
  kinjective : ∀ K : CoefficientComplexes Λ X.scheme, IsKInjective (Λ := Λ) (replacement.obj K)
  quasi : ∀ K : CoefficientComplexes Λ X.scheme, QuasiIso (augmentation.app K)
  native : CoefficientComplexes Λ X.scheme ⥤ kinjectiveSimplicialCategory Λ X N
  whole_normalization : native ⋙ kinjectiveInclusion Λ X N = replacement ⋙ F.functor

/-- The source map is the actual native ordinary-to-coherent comparison on the whole replacement functor. -/
def resolutionNerve (R : KInjectiveResolutionSource Λ X N F) :
    nerve (CoefficientComplexes Λ X.scheme) ⟶ kinjectiveNerve Λ X N :=
  letI := N.ordinary
  nerveMap R.native ≫ SimplicialNerve.fromNerve (kinjectiveSimplicialCategory Λ X N)

/-- The actual native cochain weak maps in the original source. -/
def InvertsCoefficientQuasi (C : SSet.{2})
    (a : (mapping (nerve (CoefficientComplexes Λ X.scheme)) C) _⦋0⦌) : Prop :=
  ∀ (K L : CoefficientComplexes Λ X.scheme) (f : K ⟶ L), QuasiIso f →
    IsEquivalenceEdge C (((mappingZero _ _).symm a).app (op ⦋1⦌) (nerve.edgeMk f).edge)

/-- The native K-injective model is normalized by the whole cochain localization, not only by object equivalences. -/
structure KInjectiveLocalizationSource (R : KInjectiveResolutionSource Λ X N F) : Prop where
  invert : ∀ (K L : CoefficientComplexes Λ X.scheme) (f : K ⟶ L), QuasiIso f →
    IsEquivalenceEdge (kinjectiveNerve Λ X N) ((resolutionNerve Λ X N F R).app (op ⦋1⦌) (nerve.edgeMk f).edge)
  universal : ∀ (C : SSet.{2}) [SSet.Quasicategory C],
    ∃ f : mapping (kinjectiveNerve Λ X N) C ⟶
      ((mapping (nerve (CoefficientComplexes Λ X.scheme)) C).fullEnhancedSubcategory
        (InvertsCoefficientQuasi Λ X C)).toSSet,
      f ≫ (SSet.Subcomplex.ι _) = precomposition (resolutionNerve Λ X N F R) C ∧
        CategoricalWeakEquivalence f

variable (S : ∀ {Y Z : Scheme.{0}} (f : Y ⟶ Z), EtalePullbackSource Λ f)
  (U : ∀ Y : Scheme.{0}, EtaleComplexesPullbackCoherence.EtaleBaseChangeUnitSource Y)
  (C : CoefficientPseudofunctorSource Λ S U) (D : DerivedCoefficientFamily Λ S U C)
  (E : CoefficientFibreEntrySource Λ S U C X)

/-- The actual full derived coefficient fibre of the original native family. -/
def coefficientFibre : SSet.{2} := fibre D.projection (schemeBaseVertex X)

/-- The original whole ordinary source is retained through the actual Grothendieck entry. -/
def ordinaryFamilySource : nerve (CoefficientComplexes Λ X.scheme) ⟶ D.total :=
  nerveMap E.functor ≫ D.source

/-- The full fibre comparison is normalized by the actual augmentation on all source parameters. -/
structure CoefficientFibreComparison (R : KInjectiveResolutionSource Λ X N F) where
  map : kinjectiveNerve Λ X N ⟶ coefficientFibre Λ X S U C D
  weak : CategoricalWeakEquivalence map
  objects : ∀ a : (kinjectiveNerve Λ X N) _⦋0⦌,
    (map ≫ pullback.fst D.projection (SSet.const (schemeBaseVertex X) : Δ[0] ⟶ BaseSet)).app (op ⦋0⦌) a =
      D.source.app (op ⦋0⦌) (ComposableArrows.mk₀ (entryObject Λ S U C X (vertexComplex Λ X N a)))
  source_comparison : (mapping (nerve (CoefficientComplexes Λ X.scheme)) D.total) _⦋1⦌
  source_equivalence : IsEquivalenceEdge _ source_comparison
  source : (mapping (nerve (CoefficientComplexes Λ X.scheme)) D.total).δ 1 source_comparison =
    mappingZero _ _ (ordinaryFamilySource Λ X S U C D E)
  target : (mapping (nerve (CoefficientComplexes Λ X.scheme)) D.total).δ 0 source_comparison =
    mappingZero _ _ (resolutionNerve Λ X N F R ≫ map ≫
      pullback.fst D.projection (SSet.const (schemeBaseVertex X) : Δ[0] ⟶ BaseSet))
  augmentation_normalization : ∀ K : CoefficientComplexes Λ X.scheme,
    (evaluateAt (nerve (CoefficientComplexes Λ X.scheme)) D.total
      (ComposableArrows.mk₀ K)).app (op ⦋1⦌) source_comparison =
        D.source.app (op ⦋1⦌) (nerve.edgeMk (E.functor.map (R.augmentation.app K))).edge

end MathlibExt.AlgebraicGeometry.NativeEtaleDerivedFibreModels
