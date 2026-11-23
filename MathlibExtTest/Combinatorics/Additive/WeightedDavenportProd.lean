/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.WeightedDavenportProd

namespace MetaMathlibExt

/-- At the smallest admissible parameters, both blocks have length one. -/
example : ∃ s : List (ZMod 2 × ZMod 2), s.length = 2 ∧ IsWeightedZeroSumFree {1} s := by
  rw [← Finset.Icc_self (1 : ℕ)]
  exact exists_weightedZeroSumFree_zmod_prod 2 2 1 (by decide) (by decide) (by decide) (by decide)

/-- For weights up to five in the product of orders twelve and twenty-four, the nonintegral
ceiling gives a sequence of length six and hence a strict lower bound on the constant. -/
example : 6 < weightedDavenport (Finset.Icc 1 5) (ZMod 12 × ZMod 24) := by
  obtain ⟨s, hlen, hs⟩ := exists_weightedZeroSumFree_zmod_prod 3 12 2
    (by decide) (by decide) (by decide) (by decide)
  have hbound := lt_weightedDavenport hs
  rw [hlen] at hbound
  exact hbound

end MetaMathlibExt
