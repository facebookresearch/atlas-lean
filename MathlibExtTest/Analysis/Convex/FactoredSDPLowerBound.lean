/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.FactoredSDPLowerBound

@[expose] public section

open MathlibExt.Analysis.Convex.FactoredSDPLowerBound
open scoped Matrix ComplexOrder MatrixOrder

namespace MathlibExtTest.Analysis.Convex.FactoredSDPLowerBound

/-- The certificate bound `1/2` is attained by the rank-one
example point. -/
example : exampleW.PosSemidef ∧ ((exampleA * exampleW).trace).re = 1 / 2
    ∧ ((exampleE * exampleW).trace).re = 1
    ∧ ((exampleC * exampleW).trace).re + 0 = 1 / 2 :=
  example_bound_attained

end MathlibExtTest.Analysis.Convex.FactoredSDPLowerBound
