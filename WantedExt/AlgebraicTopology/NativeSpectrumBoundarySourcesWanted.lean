/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeSpectrumBoundarySources

/-!
# Boundary construction on the original coherent spectrum square

Zero-middle contraction is an independently proved property here.
The boundary output is normalized through the original whole square;
it does not assert that a connective K quotient comparison is a stable
equivalence. Cofibrancy is retained for the strict point-set representative.

Source: BGT1001.2282v4, Definition 9.6, with Schlichting Section 12.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeSpectrumBoundarySources

open StableSpectraInfinitySource NativeDerivedSpectrumModels NativeSpectrumConeSources
open StableInfinityMappingSpaces
open MathlibExt.SpectraSource

/-- Construct the contraction of an actual zero middle object and the normalized loop boundary. -/
def_wanted native_zero_middle_boundary {S : SpectrumInfinitySource}
    {Z : SpectrumZeroSource S} {R : SpectrumReplacements S}
    {E F G : SymmetricSpectrum} {f : E ⟶ F} {g : F ⟶ G}
    (Q : SpectrumZeroTriangle S Z f g) (L : SpectrumLoop S R G)
    (h : IsZeroObject S.category.toSSet (S.vertex F)) : SpectrumBoundary Q L

/-- Rectify the fixed derived boundary from an actual cofibrant source. -/
def_wanted native_pointset_boundary {S : SpectrumInfinitySource}
    {Z : SpectrumZeroSource S} {R : SpectrumReplacements S}
    {E F G : SymmetricSpectrum} {f : E ⟶ F} {g : F ⟶ G}
    {Q : SpectrumZeroTriangle S Z f g} {L : SpectrumLoop S R G}
    (B : SpectrumBoundary Q L) (hE : IsCofibrant E)
    (hL : IsOmegaFibrant ((derivedLoopFunctor R).obj G)) : PointsetBoundary B

end MathlibExt.AlgebraicTopology.NativeSpectrumBoundarySources
