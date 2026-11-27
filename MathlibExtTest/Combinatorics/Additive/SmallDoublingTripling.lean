/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.Combinatorics.Additive.SmallDoublingTripling

/-! # Concrete cardinality tests for the small-doubling counterexample -/

open MathlibExt.Combinatorics.SmallDoublingTriplingAIMCombinatoricsProblem242Wanted
open scoped Pointwise

-- At the smallest positive modulus the translation subgroup is trivial.
example :
    (witness 1).card = 2 ∧ (witness 1 * witness 1).card = 2 ∧
      (witness 1 * witness 1 * witness 1).card = 2 := by decide

-- At modulus 3 the tripling factor is already larger than the doubling bound 3.
example :
    (witness 3).card = 4 ∧ (witness 3 * witness 3).card = 8 ∧
      (witness 3 * witness 3 * witness 3).card = 14 := by decide
