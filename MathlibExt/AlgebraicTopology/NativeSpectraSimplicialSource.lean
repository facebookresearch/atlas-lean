/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeSpectrumFunctionEvaluation
public import MathlibExt.AlgebraicTopology.CategoricalSource.NerveBasic
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# The actual simplicial enrichment and coherent localization of spectra

Every enriched Hom is the native function spectrum's level-zero space.
The ordinary Hom comparison and enriched composition are normalized on
every original spectrum level and every parameter simplex by the native
closed evaluation. The coherent nerve is the native nerve of this same
enriched ordinary category.

The stable localization extends the original ordinary source map and
has its full functor-category universal property on the coherent source.
Thus parameter homotopies are transported through the actual source
coherent nerve rather than an independently selected weak equivalence.

Sources: Hovey--Shipley--Smith, Sections 2.2 and 3.1--3.4;
BGT1001.2282v4, Sections 2.1 and 2.3. Native Mathlib/Tau Ceti
enriched-category and coherent-nerve sources retain their original
revision, copyright, authors and Apache 2.0 license in the imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeSpectraSimplicialSource

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableSpectraInfinitySource NativeSpectrumFunctionEvaluation
open MathlibExt.SpectraSource
open scoped Simplicial

/-- The enrichment uses the actual full native function spaces, not H0 or supplied Hom types. -/
structure SpectrumSimplicialEnrichment where
  ordinary : EnrichedOrdinaryCategory SSet.{0} SymmetricSpectrum
  hom_normalization : ∀ E F : SymmetricSpectrum,
    ordinary.toEnrichedCategory.Hom E F = nativeFunctionSpace E F
  ordinary_normalization :
    letI := ordinary
    ∀ (E F : SymmetricSpectrum) (f : E ⟶ F) (q : ℕ) (n : SimplexCategoryᵒᵖ)
      (z : (𝟙_ SSet.{0}).obj n) (x : (level E q).right.obj n),
      evaluatedSimplex E F q n
        ((eqToHom (hom_normalization E F)).app n ((eHomEquiv SSet.{0} f).app n z)) x =
          ((SymmetricSpectrum.evaluation q).map f).right.app n x
  composition_normalization :
    letI := ordinary
    ∀ (E F G : SymmetricSpectrum) (q : ℕ) (n : SimplexCategoryᵒᵖ)
      (f : (E ⟶[SSet.{0}] F).obj n) (g : (F ⟶[SSet.{0}] G).obj n)
      (x : (level E q).right.obj n),
      evaluatedSimplex E G q n
        ((eqToHom (hom_normalization E G)).app n
          ((eComp SSet.{0} E F G).app n (f, g))) x =
        evaluatedSimplex F G q n ((eqToHom (hom_normalization F G)).app n g)
          (evaluatedSimplex E F q n ((eqToHom (hom_normalization E F)).app n f) x)

/-- The source is the literal native coherent nerve of the same spectrum enrichment. -/
def spectrumCoherentNerve (N : SpectrumSimplicialEnrichment) : SSet.{1} :=
  letI := N.ordinary
  SimplicialNerve SymmetricSpectrum

/-- The actual ordinary source inclusion uses the completed native coherent-nerve comparison. -/
def spectrumOrdinaryToCoherent (N : SpectrumSimplicialEnrichment) :
    nerve SymmetricSpectrum ⟶ spectrumCoherentNerve N :=
  letI := N.ordinary
  SimplicialNerve.fromNerve SymmetricSpectrum

/-- The original spectrum map gives its actual coherent-nerve edge. -/
def spectrumCoherentEdge (N : SpectrumSimplicialEnrichment)
    {E F : SymmetricSpectrum} (f : E ⟶ F) : (spectrumCoherentNerve N) _⦋1⦌ :=
  (spectrumOrdinaryToCoherent N).app (op ⦋1⦌) (nerve.edgeMk f).edge

/-- Inverting the stable equivalences is tested on this entire coherent source. -/
def InvertsCoherentStableEquivalences (N : SpectrumSimplicialEnrichment) (C : SSet.{1})
    (a : (mapping (spectrumCoherentNerve N) C) _⦋0⦌) : Prop :=
  ∀ (E F : SymmetricSpectrum) (f : E ⟶ F), IsStableEquivalence f →
    IsEquivalenceEdge C (((mappingZero _ _).symm a).app (op ⦋1⦌)
      (spectrumCoherentEdge N f))

/-- The coherent stable localization is fixed on the original ordinary source and all higher functors. -/
structure SpectrumCoherentLocalization (N : SpectrumSimplicialEnrichment)
    (S : SpectrumInfinitySource) where
  map : spectrumCoherentNerve N ⟶ S.category.toSSet
  ordinary_normalization : spectrumOrdinaryToCoherent N ≫ map = S.source
  invert : ∀ (E F : SymmetricSpectrum) (f : E ⟶ F), IsStableEquivalence f →
    IsEquivalenceEdge S.category.toSSet
      (map.app (op ⦋1⦌) (spectrumCoherentEdge N f))
  universal : ∀ (C : SSet.{1}) [SSet.Quasicategory C],
    ∃ f : mapping S.category.toSSet C ⟶
      ((mapping (spectrumCoherentNerve N) C).fullEnhancedSubcategory
        (InvertsCoherentStableEquivalences N C)).toSSet,
      f ≫ (SSet.Subcomplex.ι _) = precomposition map C ∧ CategoricalWeakEquivalence f

end MathlibExt.AlgebraicTopology.NativeSpectraSimplicialSource
