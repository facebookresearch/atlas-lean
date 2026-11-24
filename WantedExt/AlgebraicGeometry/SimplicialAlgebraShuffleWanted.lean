/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

/-!
# Wanted multiplication on the fixed Moore normalization

Construct the actual DG algebra and its functorial maps from the
publicly fixed shuffle degeneracies, signs, scalar unit and normalized
complex. No normalization theorem, perfect-module theory or moduli
geometricity is assumed as input.

References: Eilenberg--Zilber, On products of complexes, §2;
Toën--Vaquié, arXiv:math/0503269v5, §2.1.
-/

namespace WantedExt.AlgebraicGeometry.SimplicialAlgebraShuffleWanted

open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.Algebra.Homology.DGCyclicBarModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u

/-- Assemble the explicit shuffle product on a normalized simplicial algebra. -/
def_wanted simplicial_shuffle_dg_algebra (k : Type u) [CommRing k] (A : SAlg k) :
  Σ N : DGAlgebra k, ShuffleAlgebraModel A N

/-- Assemble the same normalization on every actual simplicial-algebra map. -/
def_wanted simplicial_shuffle_dg_algebra_functor (k : Type u) [CommRing k] :
  ShuffleAlgebraFunctor k

end WantedExt.AlgebraicGeometry.SimplicialAlgebraShuffleWanted
