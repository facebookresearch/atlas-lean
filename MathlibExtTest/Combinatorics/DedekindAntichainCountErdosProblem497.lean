/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.DedekindAntichainCountErdosProblem497

/-! # Small Dedekind numbers -/

namespace MathlibExtTest.Combinatorics.DedekindAntichainCountErdosProblem497

open MathlibExt.Combinatorics.DedekindAntichainCountErdosProblem497Wanted

-- Enumerate pairs of members so the finite counts can be checked by kernel reduction.
private lemma count_by_filter (n : ℕ) : antichainCount n =
    (Finset.univ.filter fun F : Finset (Finset (Fin n)) =>
      ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ¬ a ⊆ b).card := by
  unfold antichainCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext F
  simp [IsAntichain, Set.Pairwise]

-- In dimension zero both the empty family and the singleton family of the empty set count.
example : antichainCount 0 = 2 := by rw [count_by_filter]; decide

-- Dimension two is the first with a pair of incomparable subsets.
example : antichainCount 2 = 6 := by rw [count_by_filter]; decide

end MathlibExtTest.Combinatorics.DedekindAntichainCountErdosProblem497
