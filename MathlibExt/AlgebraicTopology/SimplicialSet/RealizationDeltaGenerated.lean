/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation
public import MathlibExt.Topology.Convenient.StdSimplex

/-!
# Delta-generated topology of geometric realization

The geometric realization of every simplicial set is a delta-generated space.
Its topology is the quotient topology obtained from the family of topological
standard simplices in its realization presentation. The delta-generated topology
instance is provided for simplicial sets in every universe.
-/

@[expose] public section

universe u

namespace SSet

/--
The geometric realization of any simplicial set `T` has a delta-generated
topology, induced by its quotient presentation from topological standard simplices.
-/
noncomputable instance (T : SSet.{u}) :
    DeltaGeneratedSpace (SSet.toTop.obj T) :=
  (isQuotientMap_sigmaToTop T).isGeneratedBy

end SSet
