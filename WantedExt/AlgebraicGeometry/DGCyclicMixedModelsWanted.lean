/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Algebra.Homology.DGCyclicMixedModels

/-!
# Wanted DG Hochschild and Connes assembly

Construct the fixed direct-sum total and its computed degree -1 Connes
operator. Every term and map is already specified publicly. No Hodge
degeneration, smooth-diagonal or Calabi--Yau theorem is an input.

Sources: Kaledin, arXiv:math/0611623v4, §1.3; Loday, §1.1. The
ungraded TauCeti Connes cochain proofs are credited as background in the
public module, with their distinct cochain-versus-chain scope explicit.
-/

namespace WantedExt.AlgebraicGeometry.DGCyclicMixedModelsWanted

open MathlibExt.Algebra.Homology.DGCyclicBarModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels

universe u

/-- Assemble the actual DG mixed total from the fixed bar and Connes formulas. -/
def_wanted dg_hochschild_mixed_model (k : Type u) [CommRing k] (A : DGAlgebra k) :
  HochschildMixedModel A

end WantedExt.AlgebraicGeometry.DGCyclicMixedModelsWanted
