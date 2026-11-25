/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedHornLeBoundaryCofibrations

@[expose] public section

/-!
# Realized-horn boundary-cofibration client test

Minimal public client for `TopCat.realizedHornInclusions_le_boundaryRLPLLP`
in every universe: realized horn inclusions lie in the boundary left class.
Restates exact `≤` type by term application only; no reproof.
No weak-equivalence, fibration, filling, product, colimit, or model-category claim.
-/

set_option autoImplicit false

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.RealizedHornLeBoundaryCofibrationsTests

theorem realizedHorn_le_boundary_client :
    TopCat.realizedHornInclusions.{u} ≤
      (TopCat.realizedBoundaryInclusions.{u}).rlp.llp :=
  TopCat.realizedHornInclusions_le_boundaryRLPLLP

example :
    TopCat.realizedHornInclusions.{1} ≤
      (TopCat.realizedBoundaryInclusions.{1}).rlp.llp :=
  TopCat.realizedHornInclusions_le_boundaryRLPLLP

example :
    TopCat.realizedHornInclusions.{0} ≤
      (TopCat.realizedBoundaryInclusions.{0}).rlp.llp :=
  TopCat.realizedHornInclusions_le_boundaryRLPLLP

/-- Both minimum one-dimensional horns are concrete clients of the symbolic
generator inclusion. -/
example (k : Fin 2) :
    (TopCat.realizedBoundaryInclusions.{u}).rlp.llp
      (SSet.toTop.{u}.map (SSet.horn.{u} 1 k).ι) :=
  TopCat.realizedHornInclusions_le_boundaryRLPLLP _
    (TopCat.horn_mem_realizedHornInclusions 1 k)

#print axioms TopCat.realizedHornInclusions_le_boundaryRLPLLP
#print axioms realizedHorn_le_boundary_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.RealizedHornLeBoundaryCofibrationsTests
