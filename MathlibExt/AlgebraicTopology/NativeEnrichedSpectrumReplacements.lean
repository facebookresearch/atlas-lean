/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeSpectraSimplicialSource
public import MathlibExt.AlgebraicTopology.NativeSpectrumConeSources

/-!
# Native functorial spectrum replacements on all Hom simplices

The objects and ordinary maps are those of the actual native replacement
functors. The enriched maps preserve the complete native function spaces.
Their original augmentations are natural as whole enriched Hom maps,
not only on ordinary arrows. The point-set zero preservation fixes all
level simplices, and actual derived loops retain Omega-fibrancy.

These are generic simplicial-model construction requirements used to
rectify canonical K boundaries. K vanishing, exactness and motive
comparisons are not hypotheses or fields of these replacements.

Source: Hovey--Shipley--Smith, *Symmetric spectra*, Sections 3.1--3.4;
BGT1001.2282v4, Sections 2.1 and 2.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeEnrichedSpectrumReplacements

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open NativeSpectraSimplicialSource NativeSpectrumFunctionEvaluation
open NativeDerivedSpectrumModels NativeSpectrumConeSources StableSpectraInfinitySource
open MathlibExt.SpectraSource
open scoped Simplicial

/-- An actual ordinary spectrum functor acts on the same complete native Hom objects. -/
structure SpectrumFunctorAction (N : SpectrumSimplicialEnrichment)
    (F : SymmetricSpectrum ⥤ SymmetricSpectrum) where
  hom :
    letI := N.ordinary
    ∀ E G : SymmetricSpectrum, (E ⟶[SSet.{0}] G) ⟶ (F.obj E ⟶[SSet.{0}] F.obj G)
  identity :
    letI := N.ordinary
    ∀ E : SymmetricSpectrum, eId SSet.{0} E ≫ hom E E = eId SSet.{0} (F.obj E)
  composition :
    letI := N.ordinary
    ∀ E G H : SymmetricSpectrum, eComp SSet.{0} E G H ≫ hom E H =
      (hom E G ⊗ₘ hom G H) ≫ eComp SSet.{0} (F.obj E) (F.obj G) (F.obj H)
  ordinary :
    letI := N.ordinary
    ∀ (E G : SymmetricSpectrum) (f : E ⟶ G),
      eHomEquiv SSet.{0} f ≫ hom E G = eHomEquiv SSet.{0} (F.map f)

/-- Its actual enriched functor keeps the original ordinary object function. -/
def SpectrumFunctorAction.functor {N : SpectrumSimplicialEnrichment}
    {F : SymmetricSpectrum ⥤ SymmetricSpectrum} (H : SpectrumFunctorAction N F) :
    letI := N.ordinary
    EnrichedFunctor SSet.{0} SymmetricSpectrum SymmetricSpectrum :=
  letI := N.ordinary
  { obj := F.obj
    map := H.hom
    map_id := H.identity
    map_comp := H.composition }

/-- The actual replacements and augmentations preserve all source Hom simplices. -/
structure EnrichedSpectrumReplacements (N : SpectrumSimplicialEnrichment)
    (S : SpectrumInfinitySource) where
  replacements : SpectrumReplacements S
  cofibrant : SpectrumFunctorAction N replacements.cofibrant
  fibrant : SpectrumFunctorAction N replacements.fibrant
  cofibrant_augmentation_natural :
    letI := N.ordinary
    ∀ E F : SymmetricSpectrum,
      cofibrant.hom E F ≫ eHomWhiskerLeft SSet.{0} (replacements.cofibrant.obj E)
        (replacements.cofibrant_augmentation.app F) =
      eHomWhiskerRight SSet.{0} (replacements.cofibrant_augmentation.app E) F
  fibrant_augmentation_natural :
    letI := N.ordinary
    ∀ E F : SymmetricSpectrum,
      eHomWhiskerLeft SSet.{0} E (replacements.fibrant_augmentation.app F) =
        fibrant.hom E F ≫ eHomWhiskerRight SSet.{0}
          (replacements.fibrant_augmentation.app E) (replacements.fibrant.obj F)
  cofibrant_zero : ∀ (E F : SymmetricSpectrum) (f : E ⟶ F), IsPointsetZeroMap f →
    IsPointsetZeroMap (replacements.cofibrant.map f)
  fibrant_zero : ∀ (E F : SymmetricSpectrum) (f : E ⟶ F), IsPointsetZeroMap f →
    IsPointsetZeroMap (replacements.fibrant.map f)
  loop_fibrant : ∀ E : SymmetricSpectrum,
    IsOmegaFibrant ((derivedLoopFunctor replacements).obj E)

/-- Cofibrant replacement transports the actual native function homotopy on every simplex. -/
def cofibrantParameterMap {N : SpectrumSimplicialEnrichment} {S : SpectrumInfinitySource}
    (R : EnrichedSpectrumReplacements N S) (E F : SymmetricSpectrum) :
    nativeFunctionSpace E F ⟶ nativeFunctionSpace
      (R.replacements.cofibrant.obj E) (R.replacements.cofibrant.obj F) :=
  eqToHom (N.hom_normalization E F).symm ≫ R.cofibrant.hom E F ≫
    eqToHom (N.hom_normalization (R.replacements.cofibrant.obj E)
      (R.replacements.cofibrant.obj F))

end MathlibExt.AlgebraicTopology.NativeEnrichedSpectrumReplacements
