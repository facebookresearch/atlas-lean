/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeSpectrumCoherentSquares

/-!
# Constructing the whole coherent square from its actual source homotopy

The two-step enriched Hom is normalized on the entire native rigid path
space to the prescribed function-spectrum homotopy. It is not enough to
normalize the three edge maps. The stable image is already defined.

Source: HTT Section 1.1.5; BGT1001.2282v4, Sections 7.1 and 9.1.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeSpectrumCoherentSquares

open _root_.CategoryTheory
open NativeSpectrumFunctionEvaluation NativeSpectraSimplicialSource
open NativeSpectrumConeSources StableSpectraInfinitySource
open MathlibExt.SpectraSource
open scoped Simplicial

/-- The native function homotopy zero-to-composite gives this exact complete coherent source square. -/
def_wanted native_spectrum_coherent_zero_square (N : SpectrumSimplicialEnrichment)
    (S : SpectrumInfinitySource) (Z : SpectrumZeroSource S)
    {E F G : SymmetricSpectrum} (f : E ⟶ F) (g : F ⟶ G)
    (t : (nativeFunctionSpace E G) _⦋1⦌)
    (hs : (nativeFunctionSpace E G).δ 1 t = functionVertex N (zeroMap Z E G))
    (ht : (nativeFunctionSpace E G).δ 0 t = functionVertex N (f ≫ g)) :
    CoherentZeroSquare N S Z f g t

end MathlibExt.AlgebraicTopology.NativeSpectrumCoherentSquares
