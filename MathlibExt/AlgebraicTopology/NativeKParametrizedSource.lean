/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinitySParametrizedAction
public import MathlibExt.AlgebraicTopology.NativeSpectraSimplicialSource
public import MathlibExt.AlgebraicTopology.NativeSpectrumConeSources

/-!
# The full source-normalized enriched K functor

The stable-category Hom is the actual full exact-functor core, with
native enriched composition. K takes values in the actual native sphere
modules. Its enriched Hom map acts on every original S-diagonal by the
already fixed full parameter action and native function evaluation.

The quotient-killing homotopy is the image of the actual source natural
equivalence under this enriched functor. It is an independently defined
native function-spectrum simplex. An arbitrary natural zero triangle
would not impose this source normalization and is not used here.

Source: BGT1001.2282v4, Sections 2.1, 5.1, 7.1 and Definition 9.6.
Native enriched functors, internal function spectra and S-construction
operators retain the source revisions and licenses in their imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeKParametrizedSource

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels StableInfinitySFunctorMaps
open StableInfinitySParametrizedAction StableInfinityKSpectra
open NativeSpectraSimplicialSource NativeSpectrumFunctionEvaluation
open BGTVerdierQuotients
open NativeSpectrumConeSources
open MathlibExt.SpectraSource
open scoped Simplicial

/-- The full source enrichment uses the original exact-functor cores and native composition. -/
structure StableCategoryEnrichment where
  enrichment : EnrichedCategory SSet.{0} StableInfinityCategory.{0}
  hom_normalization : ∀ C D : StableInfinityCategory.{0},
    enrichment.Hom C D = ExactFunctorCore C D
  identity_normalization :
    letI := enrichment
    ∀ C : StableInfinityCategory.{0},
      eId SSet.{0} C ≫ eqToHom (hom_normalization C C) =
        (SSet.unitHomEquiv (ExactFunctorCore C C)).symm
          (exactFunctorCoreVertex (ExactFunctor.id C))
  composition_normalization :
    letI := enrichment
    ∀ (C D E : StableInfinityCategory.{0}) (n : SimplexCategoryᵒᵖ)
      (f : (C ⟶[SSet.{0}] D).obj n) (g : (D ⟶[SSet.{0}] E).obj n),
      (((eqToHom (hom_normalization C E)).app n
        ((eComp SSet.{0} C D E).app n (f, g))).val).val =
      (SimplicialCategory.sHomComp C.toSSet D.toSSet E.toSSet).app n
        ((((eqToHom (hom_normalization C D)).app n f).val).val,
          (((eqToHom (hom_normalization D E)).app n g).val).val)

/-- A source exact functor is its original full Hom vertex, as a native unit-shaped point. -/
def exactHomPoint (A : StableCategoryEnrichment)
    {C D : StableInfinityCategory.{0}} (f : ExactFunctor C D) :
    letI := A.enrichment
    𝟙_ SSet.{0} ⟶ C ⟶[SSet.{0}] D :=
  (SSet.unitHomEquiv (ExactFunctorCore C D)).symm (exactFunctorCoreVertex f) ≫
    eqToHom (A.hom_normalization C D).symm

/-- The enriched K maps have the original K objects, with full S-parameter normalization. -/
structure EnrichedKMaps (A : StableCategoryEnrichment) (N : SpectrumSimplicialEnrichment)
    (K : ConnectiveKConstruction) where
  hom :
    letI := A.enrichment
    letI := N.ordinary
    ∀ C D : StableInfinityCategory.{0},
      (C ⟶[SSet.{0}] D) ⟶ (connectiveK K C ⟶[SSet.{0}] connectiveK K D)
  identity :
    letI := A.enrichment
    letI := N.ordinary
    ∀ C : StableInfinityCategory.{0},
      eId SSet.{0} C ≫ hom C C = eId SSet.{0} (connectiveK K C)
  composition :
    letI := A.enrichment
    letI := N.ordinary
    ∀ C D E : StableInfinityCategory.{0},
      eComp SSet.{0} C D E ≫ hom C E =
        (hom C D ⊗ₘ hom D E) ≫
          eComp SSet.{0} (connectiveK K C) (connectiveK K D) (connectiveK K E)
  ordinary :
    letI := A.enrichment
    letI := N.ordinary
    ∀ (C D : StableInfinityCategory.{0}) (f : ExactFunctor C D),
      exactHomPoint A f ≫ hom C D = eHomEquiv SSet.{0} (connectiveKMap K f)
  zero_functor_map : ∀ (C D : StableInfinityCategory.{0})
    (Z : ZeroExactFunctorSource C D), IsPointsetZeroMap (connectiveKMap K (zeroExactFunctor Z))
  s_action : ∀ C D : StableInfinityCategory.{0}, FullSParameterAction C D
  all_parameters :
    letI := A.enrichment
    letI := N.ordinary
    ∀ (C D : StableInfinityCategory.{0}) (q : ℕ) (n : SimplexCategoryᵒᵖ)
      (x : (StableInfinityMultiSConstruction.multiSDiagonal C q).obj n)
      (f : (ExactFunctorCore C D).obj n),
      evaluatedSimplex (connectiveK K C) (connectiveK K D) q n
        ((eqToHom (N.hom_normalization (connectiveK K C) (connectiveK K D))).app n
          ((hom C D).app n ((eqToHom (A.hom_normalization C D).symm).app n f)))
        (((K.assembly C).comparison q).right.app n x) =
          (((K.assembly D).comparison q).right.app n ((s_action C D).action q |>.app n (x, f)))

/-- The actual enriched functor has exactly these original K objects and maps. -/
def nativeKEnrichedFunctor {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    {K : ConnectiveKConstruction} (H : EnrichedKMaps A N K) :
    letI := A.enrichment
    letI := N.ordinary
    EnrichedFunctor SSet.{0} StableInfinityCategory.{0} SymmetricSpectrum :=
  letI := A.enrichment
  letI := N.ordinary
  { obj := connectiveK K
    map := H.hom
    map_id := H.identity
    map_comp := H.composition }

/-- The source constructor chooses the S-assembly and its full enriched map together. -/
structure ParametrizedKSource (A : StableCategoryEnrichment) (N : SpectrumSimplicialEnrichment) where
  construction : ConnectiveKConstruction
  maps : EnrichedKMaps A N construction

/-- Every original source parameter simplex gives this exact native function-spectrum simplex. -/
def nativeKParameter {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    (K : ParametrizedKSource A N) (C D : StableInfinityCategory.{0})
    (n : SimplexCategoryᵒᵖ) (f : (ExactFunctorCore C D).obj n) :
    (nativeFunctionSpace (connectiveK K.construction C) (connectiveK K.construction D)).obj n :=
  (eqToHom (N.hom_normalization (connectiveK K.construction C)
    (connectiveK K.construction D))).app n
      ((K.maps.hom C D).app n ((eqToHom (A.hom_normalization C D).symm).app n f))

/-- The quotient homotopy is the actual enriched K image of the original quotient-zero path. -/
def nativeKQuotientHomotopy {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    (K : ParametrizedKSource A N) (E : StableExactSequence.{0})
    {Z : ZeroExactFunctorSource E.left E.right} (P : QuotientZeroPath E Z) :
    (nativeFunctionSpace (connectiveK K.construction E.left)
      (connectiveK K.construction E.right)) _⦋1⦌ :=
  nativeKParameter K E.left E.right (op ⦋1⦌) P.path

/-- The reverse source path gives the actual zero-to-composite rigid-triangle homotopy. -/
def nativeKQuotientReverseHomotopy {A : StableCategoryEnrichment} {N : SpectrumSimplicialEnrichment}
    (K : ParametrizedKSource A N) (E : StableExactSequence.{0})
    {Z : ZeroExactFunctorSource E.left E.right} (P : QuotientZeroReversePath E Z) :
    (nativeFunctionSpace (connectiveK K.construction E.left)
      (connectiveK K.construction E.right)) _⦋1⦌ :=
  nativeKParameter K E.left E.right (op ⦋1⦌) P.path

end MathlibExt.AlgebraicTopology.NativeKParametrizedSource
