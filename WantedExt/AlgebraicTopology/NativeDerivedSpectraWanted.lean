/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeDerivedSpectrumModels

/-!
# Native stable-spectrum replacements and full derived Hom comparison

The replacements use actual native free-spectrum lifting tests and actual
Omega-fibrancy at every level. Weakness is in the native stable infinity
localization. The function-spectrum carrier is the native internal Hom
from the specified cofibrant source to the specified fibrant target.

Sources: Hovey--Shipley--Smith, Symmetric spectra, Sections 2.2 and
3.1--3.4; BGT arXiv:1001.2282v4, Sections 2.1 and 2.3.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeDerivedSpectrumModels

open _root_.CategoryTheory.Limits StableSpectraInfinitySource
open MathlibExt.SpectraSource

/-- Construct native functorial cofibrant and Omega-fibrant replacements. -/
def_wanted native_spectrum_replacements (S : SpectrumInfinitySource) :
  SpectrumReplacements S

/-- Compare the whole native derived function-spectrum zero space to the localization Hom fibre. -/
def_wanted native_derived_mapping_comparison (S : SpectrumInfinitySource)
    (R : SpectrumReplacements S) (E F : SymmetricSpectrum) :
  DerivedMappingComparison S R E F

end MathlibExt.AlgebraicTopology.NativeDerivedSpectrumModels
