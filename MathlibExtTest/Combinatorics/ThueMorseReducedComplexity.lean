/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ThueMorseReducedComplexity

open MathlibExt.Combinatorics.ReducedComplexitiesWanted MetaMathlibExt InfiniteWord

-- Both single letters occur, and reducing a single letter keeps it.
private theorem rhoRed_one : rhoRed thueMorse 1 = 2 := by
  have words : (fun v => redWord (List.ofFn v)) '' factorSet thueMorse 1 =
      ({[false], [true]} : Set (List Bool)) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨v, _, rfl⟩
      simp [List.ofFn_succ, redWord]
    · intro w hw
      rcases hw with rfl | hw
      · exact ⟨factor thueMorse 1 0, ⟨0, rfl⟩, by decide +kernel⟩
      · obtain rfl : w = [true] := hw
        exact ⟨factor thueMorse 1 1, ⟨1, rfl⟩, by decide +kernel⟩
  rw [rhoRed, words, Set.ncard_pair (by decide)]

-- The least lengths in the two residue classes have four and six distinct reductions.
example : rhoRed thueMorse 2 = 4 ∧ rhoRed thueMorse 4 = 6 := by
  obtain ⟨h₄, h₂⟩ := rhoRed_thueMorse_even 0
  change rhoRed thueMorse 2 = rhoRed thueMorse 1 + 2 at h₂
  change rhoRed thueMorse 4 = rhoRed thueMorse 2 + 2 at h₄
  rw [rhoRed_one] at h₂
  exact ⟨h₂, by rw [h₄, h₂]⟩

-- At the smallest input n = 2, the signed recurrences distinguish the two lengths.
example : (minAlt 4 : ℤ) = 3 - maxAlt 3 ∧ (maxAlt 4 : ℤ) = 3 - minAlt 2 := by
  obtain ⟨hmin, hmax, _, _⟩ := minAlt_maxAlt_two_mul 2 (by decide)
  exact ⟨hmin, hmax⟩

example : (minAlt 5 : ℤ) = 4 - maxAlt 3 ∧ (maxAlt 5 : ℤ) = 4 - minAlt 3 :=
  (minAlt_maxAlt_two_mul 2 (by decide)).2.2

-- The even-length extrema occur at an odd start (minimum) and an even start (maximum).
example : alternations (factorList thueMorse 4 5) = 1 ∧
    alternations (factorList thueMorse 4 2) = 3 := by
  decide +kernel

-- For the odd length, both start parities give the same count for each desubstituted start.
example : alternations (factorList thueMorse 5 4) = 2 ∧
    alternations (factorList thueMorse 5 5) = 2 ∧
    alternations (factorList thueMorse 5 0) = 3 ∧
    alternations (factorList thueMorse 5 1) = 3 := by
  decide +kernel
