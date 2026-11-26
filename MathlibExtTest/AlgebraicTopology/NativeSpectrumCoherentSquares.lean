/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicTopology.NativeSpectrumCoherentSquares

/-!
# Tests for coherent zero squares

The triangle of a coherent zero square through its zero corner is the ordinary two-simplex
`E ⟶ 0 ⟶ G`. So two squares with the same maps and the same prescribed homotopy have the
same triangle through zero: a loop on that triangle, which would change the boundary map, is
not admitted.
-/

open CategoryTheory Opposite
open MathlibExt.AlgebraicTopology.NativeSpectrumCoherentSquares
open MathlibExt.AlgebraicTopology.NativeSpectrumFunctionEvaluation
open MathlibExt.AlgebraicTopology.NativeSpectraSimplicialSource
open MathlibExt.AlgebraicTopology.NativeSpectrumConeSources
open MathlibExt.AlgebraicTopology.StableSpectraInfinitySource
open MathlibExt.SpectraSource
open scoped Simplicial

/-- The triangle through zero is the ordinary composable pair through the zero spectrum. -/
example {N : SpectrumSimplicialEnrichment} {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    {E F G : SymmetricSpectrum} {f : E ⟶ F} {g : F ⟶ G} {t : (nativeFunctionSpace E G) _⦋1⦌}
    (Q : CoherentZeroSquare N S Z f g t) :
    Q.diagram.app (op ⦋2⦌) zeroSourceChain =
      (spectrumOrdinaryToCoherent N).app (op ⦋2⦌)
        (ComposableArrows.mk₂ (toZeroSpectrum Z E) (initialSpectrumMap G)) :=
  Q.zero_triangle

/-- Two squares with the same data have the same triangle through zero. -/
example {N : SpectrumSimplicialEnrichment} {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S}
    {E F G : SymmetricSpectrum} {f : E ⟶ F} {g : F ⟶ G} {t : (nativeFunctionSpace E G) _⦋1⦌}
    (Q₁ Q₂ : CoherentZeroSquare N S Z f g t) :
    Q₁.diagram.app (op ⦋2⦌) zeroSourceChain = Q₂.diagram.app (op ⦋2⦌) zeroSourceChain :=
  Q₁.zero_triangle.trans Q₂.zero_triangle.symm
