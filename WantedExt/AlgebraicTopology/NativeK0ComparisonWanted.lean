/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeK0ComparisonModels

/-!
# Source-normalized native K0 relation descent and group comparison

The source sphere, complete native spectrum localization, actual object
sphere/circle, and independently defined Grothendieck relations are fixed.
Only their genuine stable-additivity, source normalization and comparison
proofs are requested here. Higher and negative K retain the original S
spectrum and boundary tower, independently of this degree-zero result.

Sources: BGT1001.2282v4 Sections7--9; HSS Sections2.2/3.1.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeK0ComparisonModels

open _root_.CategoryTheory
open StableInfinityCategoryModels StableSpectraInfinitySource NativeSpectrumConeSources
open StableInfinityKSpectra StableInfinityGrothendieckGroups
open scoped Simplicial

def_wanted native_spectrum_group_source (S : SpectrumInfinitySource) (Z : SpectrumZeroSource S) :
  SpectrumGroupSource S Z

variable {S : SpectrumInfinitySource} {Z : SpectrumZeroSource S} (G : SpectrumGroupSource S Z)
  (K : ConnectiveKConstruction) (C : StableInfinityCategory.{0})

theorem_wanted native_object_circle_normalization (x : C.toSSet _⦋0⦌) :
  spectrumObjectCircle K C x = objectCircle K C x

theorem_wanted native_k0_relation_descent : K0RelationDescent G K C

theorem_wanted native_k0_group_comparison (h : K0RelationDescent G K C) :
  Function.Bijective (k0Comparison G K C h)

theorem_wanted native_k0_exact_naturality {C D : StableInfinityCategory.{0}} (f : ExactFunctor C D)
    (hC : K0RelationDescent G K C) (hD : K0RelationDescent G K D) :
  (spectrumPi0Map G (connectiveKMap K f)).comp (k0Comparison G K C hC) =
    (k0Comparison G K D hD).comp (grothendieckMap f)

end MathlibExt.AlgebraicTopology.NativeK0ComparisonModels
