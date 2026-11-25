/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeSpectrumHoClosedModels

/-!
# Native derived closed and sphere-unit source constructions

The literal spectrum localization, cofibrant tensor, complete function
spectrum, original braiding and native closed counit fix these outputs.
Sources: HSS Sections 2.2/3.1--3.4; BGT arXiv:1001.2282v4 Section 2.3.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeSpectrumHoClosedModels

open StableSpectraInfinitySource NativeDerivedSpectrumModels

def_wanted native_spectrum_ho_closed_source (S : SpectrumInfinitySource) (R : SpectrumReplacements S) :
    SpectrumHoClosedSource S R

def_wanted native_free_zero_regular_sphere : FreeZeroSphereSource

end MathlibExt.AlgebraicTopology.NativeSpectrumHoClosedModels
