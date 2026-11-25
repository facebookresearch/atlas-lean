/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ZeroSumSubsequenceCount
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

/-! # Tests for counting zero-sum subsequences -/

namespace MathlibExtTest.ZeroSumSubsequenceCount

private abbrev C₂ := Multiplicative (ZMod 2)

private theorem davenportTwo :
    IsLeast {m : ℕ | ∀ s : Fin m → C₂, ∃ S : Finset (Fin m), S.Nonempty ∧
      ∏ i ∈ S, s i = 1} 2 := by
  constructor
  · change ∀ s : Fin 2 → C₂, ∃ S : Finset (Fin 2), S.Nonempty ∧ ∏ i ∈ S, s i = 1
    decide
  · intro m hm
    by_contra! h
    interval_cases m
    · exact (by decide : ¬∃ S : Finset (Fin 0), S.Nonempty ∧ ∏ _i ∈ S, (1 : C₂) = 1)
        (hm fun _ => 1)
    · exact (by decide : ¬∃ S : Finset (Fin 1), S.Nonempty ∧
          ∏ _i ∈ S, (Multiplicative.ofAdd 1 : C₂) = 1) (hm fun _ => Multiplicative.ofAdd 1)

-- Four copies of the nonidentity element have six qualifying pairs and no qualifying triples.
example : (Finset.univ.filter fun S : Finset (Fin 4) =>
    1 ≤ S.card ∧ S.card ≤ 3 ∧ ∏ _i ∈ S, (Multiplicative.ofAdd 1 : C₂) = 1).card = 6 := by
  decide

example : 4 ≤ 6 * (Finset.univ.filter fun S : Finset (Fin 4) =>
    1 ≤ S.card ∧ S.card ≤ 3 ∧ ∏ _i ∈ S, (Multiplicative.ofAdd 1 : C₂) = 1).card :=
  MetaMathlibExt.choose_le_choose_mul_card_prod_eq_one (n := 2) (hn := davenportTwo)
    (r := 4) (t := 3) (hrt := by decide) (htn := by decide) (fun _ => Multiplicative.ofAdd 1)

end MathlibExtTest.ZeroSumSubsequenceCount
