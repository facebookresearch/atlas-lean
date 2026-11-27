/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeSpectrumConeSources

/-!
# Native spectrum zero, cofiber and loop construction requests

Every diagram and native function-spectrum carrier is independently
fixed in MathlibExt. No K-theory vanishing or localization conclusion
occurs among these generic source hypotheses.

Sources: Hovey--Shipley--Smith, Sections 3.1--3.4; BGT1001.2282v4,
Sections 7.1 and 9.1.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeSpectrumConeSources

open StableSpectraInfinitySource NativeDerivedSpectrumModels
open MathlibExt.SpectraSource
open scoped Simplicial

/-- Prove that the actual free-zero spectrum is zero in the source and localization. -/
def_wanted native_spectrum_zero (S : SpectrumInfinitySource) : SpectrumZeroSource S

/-- Construct the universal native coherent cocone on the fixed spectrum span. -/
def_wanted native_spectrum_cofiber (S : SpectrumInfinitySource) (Z : SpectrumZeroSource S)
    {E F : SymmetricSpectrum} (f : E ⟶ F) : SpectrumCofiber S Z f

/-- Construct the extension on the original full cocone and its nullhomotopy. -/
def_wanted native_spectrum_cofiber_extension {S : SpectrumInfinitySource}
    {Z : SpectrumZeroSource S} {E F : SymmetricSpectrum} {f : E ⟶ F}
    (P : SpectrumCofiber S Z f) (Q : SpectrumCocone S Z f) : CofiberExtension P Q

/-- Normalize actual derived circle functions to the full native zero-cospan limit. -/
def_wanted native_spectrum_loop (S : SpectrumInfinitySource) (R : SpectrumReplacements S)
    (G : SymmetricSpectrum) : SpectrumLoop S R G

/-- The terminal cone gives the map from each original coherent loop cone. -/
def_wanted native_spectrum_loop_cone_map {S : SpectrumInfinitySource}
    {R : SpectrumReplacements S} {G : SymmetricSpectrum} (L : SpectrumLoop S R G)
    (c : (StableInfinityFiniteDiagrams.leftCones S.category.toSSet (loopCospan S G))
      _⦋0⦌) : LoopConeMap L c

end MathlibExt.AlgebraicTopology.NativeSpectrumConeSources
