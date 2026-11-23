/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityKSpectra
public import MathlibExt.AlgebraicTopology.StableInfinityMappingSpaceMaps
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Derived constructions on the actual Tau Ceti spectrum carrier

Cofibrancy and Omega-fibrancy are those of `StableSpectraInfinitySource`.
Replacement augmentations are weak in the actual stable infinity
localization, without a strict-bijectivity test.

The derived function spectrum is the native internal function spectrum
from a cofibrant source to a fibrant target. Derived loops use the actual
free-zero circle spectrum. Their construction and full mapping-space
comparison proofs remain explicit Wanted requests.

Sources: Hovey--Shipley--Smith, Symmetric spectra, Sections 2.2 and
3.1--3.4; Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Sections 2.1
and 2.3. The completed native Tau Ceti ports retain their exact source
revision, authors and Apache 2.0 attribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeDerivedSpectrumModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityMappingSpaces
open StableInfinityMappingSpaceMaps StableSpectraInfinitySource
open MathlibExt.SpectraSource
open scoped Simplicial

/-- Stable weakness is measured in the actual native stable localization. -/
def IsStableWeak (S : SpectrumInfinitySource) {E F : SymmetricSpectrum}
    (f : E ⟶ F) : Prop := IsEquivalenceEdge S.category.toSSet (S.edge f)

/-- The two native functorial replacements and their original augmentations. -/
structure SpectrumReplacements (S : SpectrumInfinitySource) where
  cofibrant : SymmetricSpectrum ⥤ SymmetricSpectrum
  cofibrant_augmentation : cofibrant ⟶ 𝟭 SymmetricSpectrum
  cofibrant_source : ∀ E : SymmetricSpectrum, IsCofibrant (cofibrant.obj E)
  cofibrant_weak : ∀ E : SymmetricSpectrum,
    IsStableWeak S (cofibrant_augmentation.app E)
  fibrant : SymmetricSpectrum ⥤ SymmetricSpectrum
  fibrant_augmentation : 𝟭 SymmetricSpectrum ⟶ fibrant
  fibrant_source : ∀ E : SymmetricSpectrum, IsOmegaFibrant (fibrant.obj E)
  fibrant_weak : ∀ E : SymmetricSpectrum,
    IsStableWeak S (fibrant_augmentation.app E)

/-- The derived function spectrum retains the actual full native internal Hom. -/
def derivedFunctionSpectrum {S : SpectrumInfinitySource}
    (R : SpectrumReplacements S) (E F : SymmetricSpectrum) : SymmetricSpectrum :=
  (Mod.internalHom (R.cofibrant.obj E)).obj (R.fibrant.obj F)

/-- Its degree-zero space is the actual native function-spectrum level. -/
def derivedMappingSpace {S : SpectrumInfinitySource}
    (R : SpectrumReplacements S) (E F : SymmetricSpectrum) : SSet.{0} :=
  (level (derivedFunctionSpectrum R E F) 0).right

/-- The native suspension sphere is the free-zero spectrum of the actual circle. -/
abbrev circleSpectrum : SymmetricSpectrum :=
  (SymmetricSpectrum.free 0).obj PointedSSet.circle

/-- Derived loops are the native function-spectrum right adjoint on a fibrant target. -/
def derivedLoopFunctor {S : SpectrumInfinitySource}
    (R : SpectrumReplacements S) : SymmetricSpectrum ⥤ SymmetricSpectrum :=
  R.fibrant ⋙ Mod.internalHom circleSpectrum

/-- All iterated derived loops use that same native functor. -/
def derivedLoopPower {S : SpectrumInfinitySource}
    (R : SpectrumReplacements S) (n : ℕ) :
    SymmetricSpectrum ⥤ SymmetricSpectrum :=
  match n with
  | 0 => 𝟭 SymmetricSpectrum
  | n + 1 => derivedLoopFunctor R ⋙ derivedLoopPower R n

/-- The full native localization mapping-space comparison is a construction output. -/
structure DerivedMappingComparison (S : SpectrumInfinitySource)
    (R : SpectrumReplacements S) (E F : SymmetricSpectrum) where
  map : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj
    (derivedMappingSpace R E F) ⟶
      mappingSpace S.category.toSSet (S.vertex E) (S.vertex F)
  weak : WeakEquivalence map

end MathlibExt.AlgebraicTopology.NativeDerivedSpectrumModels
