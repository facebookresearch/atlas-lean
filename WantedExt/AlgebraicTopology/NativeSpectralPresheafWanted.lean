/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeSpectralPresheafModels

/-!
# Actual spectral presheaf source and complete spectral Yoneda construction

The native enriched functor carrier, full equalizer Hom spectrum,
component actions and exact Yoneda evaluation are already fixed.
Source constructions and generic proof requests remain independent of
K and motive corepresentability.

Sources: enriched Yoneda; HTT Sections2.2/5.5; BGT1001.2282v4
Sections7.2/9.1; HSS Sections2.2/3.1.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeSpectralPresheafModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.SpectraSource
open StableSpectraInfinitySource
open scoped MonoidalClosed

variable (C : Type) [EnrichedCategory SymmetricSpectrum C]
  (S : SpectrumInfinitySource)

def_wanted native_spectral_representable (c : C) : RepresentableSource C c

theorem_wanted native_spectral_yoneda (c : C) (Y : RepresentableSource C c) (E : RawPresheaf C) :
  IsIso (yonedaEvaluation C Y E)

def_wanted native_spectral_presheaf_source : PresheafInfinitySource C S

def_wanted native_spectral_presheaf_replacements [HasInitial (RawPresheaf C)] : PresheafReplacements C S

end MathlibExt.AlgebraicTopology.NativeSpectralPresheafModels
