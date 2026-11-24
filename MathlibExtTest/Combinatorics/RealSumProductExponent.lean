/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.RealSumProductExponent

/-! # Tests for the real sum-product exponent -/

open MathlibExt.Combinatorics.RealSumProductExponentWanted
open scoped Pointwise

example : sumProductRatio ∅ = 0 := by
  simp [sumProductRatio]

example (x : ℝ) : sumProductRatio {x} = 0 := by
  simp [sumProductRatio]

-- The sums of 0 and 1 give three distinct values, and their products give two.
example : sumProductMaxCard {0, 1} = 3 := by
  let A : Finset ℝ := {0, 1}
  have hs : A + A = {0, 1, 2} := by
    ext x
    simp [A, Finset.mem_add, eq_comm, one_add_one_eq_two, or_assoc]
  have hp : A * A = A := by
    ext x
    simp [A, Finset.mem_mul, eq_comm]
  change max (A + A).card (A * A).card = 3
  rw [hs, hp]
  norm_num [A, Finset.card_insert_of_notMem]

example : sumProductExponent ∈ Set.Icc (1 : ℝ) 2 :=
  ⟨trivialLowerBound_holds, erdosSzemerediHistoricalUpperBound_holds⟩

-- The same constant works on singletons, which forces it to be at most one.
example (ε : ℝ) (hε : 0 < ε) :
    ∃ K ∈ Set.Ioc (0 : ℝ) 1, ∀ A : Finset ℝ, A.Nonempty →
      K * (A.card : ℝ) ^ (sumProductExponent - ε) ≤ sumProductMaxCard A := by
  obtain ⟨K, hK, hbound⟩ := epsilonUniformLowerGrowthCharacterization_holds.1 ε hε
  refine ⟨K, ⟨hK, ?_⟩, hbound⟩
  simpa [sumProductMaxCard] using hbound {0} (Finset.singleton_nonempty _)

example {s : ℝ} (hs : sumProductExponent < s) : ¬ HasUniformSumProductLowerGrowth s :=
  fun h => hs.not_ge (epsilonUniformLowerGrowthCharacterization_holds.2 h)
