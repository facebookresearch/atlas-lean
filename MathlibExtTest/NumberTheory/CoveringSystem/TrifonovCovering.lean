/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CoveringSystem.TrifonovCovering

/-! # Tests for `MathlibExt.NumberTheory.CoveringSystem.TrifonovCovering` -/

namespace MathlibExtTest.TrifonovCovering

open MetaMathlibExt MetaMathlibExt.TrifonovCovering

-- Test section: periodic masks. `periodicMask 3 4` has its set bits at `0, 3, 6, 9`.
example : periodicMask 3 4 = 0b1001001001 := by decide

example : (periodicMask 3 4).testBit 9 = true ∧ (periodicMask 3 4).testBit 12 = false ∧
    (periodicMask 3 4).testBit 4 = false := by
  simp only [testBit_periodicMask (by norm_num : 0 < 3)]
  decide

-- Modulus `1` sets every bit below `k`, and the degenerate modulus `0` gives the empty mask.
example (k : ℕ) : periodicMask 1 k = 2 ^ k - 1 := by simp [periodicMask]

example (k : ℕ) : periodicMask 0 k = 0 := by simp [periodicMask]

-- Test section: cover masks. The classes `0 mod 2` and `0 mod 3` give the bits `0, 2, 3, 4`
-- below `6`: they miss `1` and `5`, so the mask is not full.
example : coverMask 6 [(0, 2), (0, 3)] = 0b11101 := by decide

example : coverMask 6 [(0, 2), (0, 3)] ≠ 2 ^ 6 - 1 := by decide

-- The criterion proves that the distinct covering system of the introduction of Klein's paper,
-- `{0 mod 2, 0 mod 3, 1 mod 4, 1 mod 6, 11 mod 12}`, covers the integers.
example : Int.IsCoveringSystem
    ([(0, 2), (0, 3), (1, 4), (1, 6), (11, 12)].map fun c : ℕ × ℕ => ((c.1 : ℤ), c.2)).toFinset :=
  isCoveringSystem_of_coverMask_eq (L := 12) (by norm_num) (by decide) (by decide)

-- Edge case: the criterion is sufficient, not necessary. The classes `1 mod 2` and `2 mod 2`
-- cover the integers, but `2 mod 2` contributes no bit below `2`, so residues should be reduced.
example : Int.IsCoveringSystem
      ([(1, 2), (2, 2)].map fun c : ℕ × ℕ => ((c.1 : ℤ), c.2)).toFinset ∧
    coverMask 2 [(1, 2), (2, 2)] ≠ 2 ^ 2 - 1 := by
  refine ⟨fun z => ?_, by decide⟩
  rcases Int.emod_two_eq_zero_or_one z with h | h
  · exact ⟨(2, 2), by simp, by simp [Int.ModEq, h]⟩
  · exact ⟨(1, 2), by simp, by simp [Int.ModEq, h]⟩

-- Edge case: the hypothesis `0 < L` is needed. For `L = 0` the empty list has the full mask
-- `2 ^ 0 - 1 = 0`, but it covers nothing.
example : coverMask 0 [] = 2 ^ 0 - 1 ∧
    ¬ Int.IsCoveringSystem (([] : List (ℕ × ℕ)).map fun c => ((c.1 : ℤ), c.2)).toFinset := by
  refine ⟨rfl, fun h => ?_⟩
  obtain ⟨c, hc, -⟩ := h 0
  simp at hc

-- Test section: Trifonov's covering system. It has 58 classes with strictly increasing moduli
-- from `6` to `168`, whose least common multiple is `1663200`.
example : classes.length = 58 := by decide

example : (classes.map Prod.snd).Pairwise (· < ·) := by decide

example : (classes.map Prod.snd).head? = some 6 ∧ (classes.map Prod.snd).getLast? = some 168 := by
  decide

example : (classes.map Prod.snd).foldr Nat.lcm 1 = 1663200 := by decide

-- Every residue is reduced modulo its modulus.
example : ∀ c ∈ classes, c.1 < c.2 := by decide

-- The kernel check is not vacuous: without its last class `49 mod 168` the mask is not full.
example : coverMask 1663200 classes.dropLast ≠ 2 ^ 1663200 - 1 := by decide +kernel

-- Test section: the theorem gives a distinct covering system with smallest modulus `6`.
example : ∃ classes : Finset (ℤ × ℕ), Int.IsCoveringSystem classes ∧
    Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)) ∧ (∀ c ∈ classes, 6 ≤ c.2) ∧
    ∃ c ∈ classes, c.2 = 6 := by
  obtain ⟨C, hC, hinj, hbound, hsix, -⟩ := exists_distinct_covering_min_six_max_168
  exact ⟨C, hC, hinj, fun c hc => (hbound c hc).1, hsix⟩

end MathlibExtTest.TrifonovCovering
