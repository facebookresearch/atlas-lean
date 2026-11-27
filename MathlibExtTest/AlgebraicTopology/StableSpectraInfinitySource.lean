/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicTopology.StableSpectraInfinitySource

/-!
# Tests for stable equivalences of symmetric spectra

A stable equivalence has a cofibrant replacement square, so the mapping-space test cannot hold
vacuously: a map without a replacement square is not a stable equivalence. For every
replacement square, the replaced map induces weak equivalences of mapping spaces into every
Omega-fibrant spectrum.
-/

open CategoryTheory MonoidalCategory
open MathlibExt.SpectraSource MathlibExt.AlgebraicTopology.StableSpectraInfinitySource
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels

/-- A stable equivalence has a cofibrant replacement square. -/
example {X Y : SymmetricSpectrum} (f : X ⟶ Y) (h : IsStableEquivalence f) :
    ∃ (X' Y' : SymmetricSpectrum) (p : X' ⟶ X) (q : Y' ⟶ Y) (f' : X' ⟶ Y'),
      IsCofibrantReplacementSquare f p q f' :=
  h.1

/-- A map without a cofibrant replacement square is not a stable equivalence. -/
example {X Y : SymmetricSpectrum} (f : X ⟶ Y)
    (h : ¬ ∃ (X' Y' : SymmetricSpectrum) (p : X' ⟶ X) (q : Y' ⟶ Y) (f' : X' ⟶ Y'),
      IsCofibrantReplacementSquare f p q f') :
    ¬ IsStableEquivalence f :=
  fun hf ↦ h hf.1

/-- Every replacement square is tested against every Omega-fibrant spectrum. -/
example {X Y X' Y' : SymmetricSpectrum} (f : X ⟶ Y) (p : X' ⟶ X) (q : Y' ⟶ Y) (f' : X' ⟶ Y')
    (h : IsStableEquivalence f) (hs : IsCofibrantReplacementSquare f p q f')
    (E : SymmetricSpectrum) (hE : IsOmegaFibrant E) :
    WeakEquivalence ((SymmetricSpectrum.evaluation 0).map ((MonoidalClosed.pre f').app E)).right :=
  h.2 X' Y' p q f' hs E hE
