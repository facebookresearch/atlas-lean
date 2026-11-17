/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NativeRingK0Models

/-!
# Native projective ring K0 operations and enhanced Perf comparison

Every ring/module, direct-sum relation, actual tensor, source augmentation
and group-map generator is fixed. Genuine source constructions and
quotient/comparison proofs are direct Wanted requests.

Sources: Bass ChapterII; Thomason--Trobaugh; BGT1001.2282v4 Sections4/7.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.NativeRingK0Models

open OrdinarySchemeModuleFamilies OrdinaryConstantCoefficientModels GeometricPerfKFrontDoors
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

def_wanted native_projective_tensor (A : OrdinaryAlgebras) : ProjectiveTensorSource A

def_wanted native_ring_k0_structure (A : OrdinaryAlgebras) (T : ProjectiveTensorSource A) : RingK0Structure A T

variable (A : OrdinaryAlgebras) (N : ShuffleAlgebraFunctor ℤ) (C : ConstantRingSource A N)
  (J : OrdinaryModuleSource A N C) (I : RingPerfectInput A N)

def_wanted native_projective_perf_source : ProjectivePerfSource A N C J I

variable (P : ProjectivePerfSource A N C J I)

theorem_wanted native_ring_k0_relation_descent : RingRelationDescent A N C J I P

theorem_wanted native_ring_perf_k0_comparison (h : RingRelationDescent A N C J I P) :
  Function.Bijective (ringK0ToPerf A N C J I P h)

end MathlibExt.AlgebraicGeometry.NativeRingK0Models
