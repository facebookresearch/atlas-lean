/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisorsShortIntervalCardUnsolvableSqAddPrimePow
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.NumberTheory.DivisorsShortIntervalCardUnsolvableSqAddPrimePow

open scoped Classical

example :
    ((Finset.range (3 ^ (1 + 1))).filter fun x : ℕ =>
      ¬ ∃ y : ℤ, (x : ℤ) ^ 2 + (3 : ℤ) ^ 1 * 1 ≡ y ^ 2
        [ZMOD (3 : ℤ) ^ (1 + 1)]).card = 3 := by
  exact (MetaMathlibExt.card_unsolvable_sq_add_primePow (p := 3) (by norm_num)
    1 (by norm_num)).2.1

example {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    ((Finset.range (p ^ (2 + 1))).filter fun x : ℕ =>
      ¬ ∃ y : ℤ, (x : ℤ) ^ 2 + (p : ℤ) ^ 2 * u ≡ y ^ 2
        [ZMOD (p : ℤ) ^ (2 + 1)]).card =
      p * ((Finset.range (p ^ (0 + 1))).filter fun x : ℕ =>
        ¬ ∃ y : ℤ, (x : ℤ) ^ 2 + (p : ℤ) ^ 0 * u ≡ y ^ 2
          [ZMOD (p : ℤ) ^ (0 + 1)]).card :=
  (MetaMathlibExt.card_unsolvable_sq_add_primePow hp u hu).2.2 2 le_rfl

example :
    ((Finset.range (3 ^ (0 + 1))).filter fun x : ℕ =>
      ¬ ∃ y : ℤ, (x : ℤ) ^ 2 + (3 : ℤ) ^ 0 * 1 ≡ y ^ 2
        [ZMOD (3 : ℤ) ^ (0 + 1)]).card = 2 := by
  have h := (MetaMathlibExt.card_unsolvable_sq_add_primePow (p := 3) (by norm_num)
    1 (by norm_num)).1
  have hsym : legendreSym 3 (-1) = -1 := by
    norm_num [legendreSym.at_neg_one (by norm_num : 3 ≠ 2)]
  rw [hsym] at h
  dsimp only at h
  simp only [Nat.cast_ofNat] at h
  omega

end MathlibExtTest.NumberTheory.DivisorsShortIntervalCardUnsolvableSqAddPrimePow
