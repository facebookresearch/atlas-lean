/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation
public import MathlibExt.Topology.Convenient.StdSimplex

/-!
# Legacy Delta-generated specialization of geometric realization

This compatibility provider installs only the historical generated-topology
instance. Neutral realization-presentation clients should import
`RealizationPresentation` instead.
-/

@[expose] public section

universe u

namespace SSet

/-- The geometric realization of a simplicial set is delta-generated. -/
noncomputable instance (T : SSet.{u}) :
    DeltaGeneratedSpace (SSet.toTop.obj T) :=
  (isQuotientMap_sigmaToTop T).isGeneratedBy

end SSet
