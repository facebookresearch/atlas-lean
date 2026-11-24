/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedGeneratorCardinal

@[expose] public section

/-!
# Realized generator cardinal consumer tests

Minimal public client for the repaired cardinal API: the bound itself, its
regularity, the finite/simplex/boundary/horn continuum bounds, and the two
generator-index strict bounds, plus axiom reports for the strongest bounds.
No smallness or presentability claim is made here.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.RealizedGeneratorCardinalTests

#check @realizedGeneratorCardinal
#check @isRegular_realizedGeneratorCardinal
#check @mk_realizedFinite_le
#check @mk_realizedStdSimplex_le
#check @mk_realizedBoundary_le
#check @mk_realizedHorn_le
#check @mk_nat_lt_realizedGeneratorCardinal
#check @mk_sigmaHornIndex_lt_realizedGeneratorCardinal

#print axioms mk_realizedFinite_le
#print axioms mk_nat_lt_realizedGeneratorCardinal
#print axioms mk_sigmaHornIndex_lt_realizedGeneratorCardinal

end MathlibExtTest.AlgebraicTopology.ModelCategory.RealizedGeneratorCardinalTests
