/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MahlerPopkenComplexity.Recurrence

namespace MathlibExt.NumberTheory.MahlerPopkenComplexityWanted

-- In the unary case the eventual recurrence computes classical integer complexity.
example : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ hn : 1 ≤ n, IntegerComplexity.complexity ⟨n, hn⟩ = mahlerPopkenRecursionValue 1 n := by
  obtain ⟨N, hN⟩ := mahlerPopkenComplexity_eq_recursionValue_eventually 1 (hm := le_rfl)
  refine ⟨N + 1, fun n hn ↦ ⟨by omega, ?_⟩⟩
  rw [← mahlerPopkenComplexity_one_eq]
  exact hN n (by omega)

-- The recurrence already applies to the first value above the largest leaf.
example (m : ℕ) (hm : 1 ≤ m) :
    mahlerPopkenComplexity m (m + 1) = mahlerPopkenRecursionValue m (m + 1) :=
  mahlerPopkenComplexity_eq_recursionValue_of_lt hm (Nat.lt_succ_self m)

-- At the boundary n = m = 2, the optimal expression is a single leaf.
example : mahlerPopkenComplexity 2 2 < mahlerPopkenRecursionValue 2 2 := by
  have hleaf : mahlerPopkenComplexity 2 2 ≤ 1 :=
    mahlerPopkenComplexity_min_le (.leaf 1) rfl
  refine hleaf.trans_lt ?_
  unfold mahlerPopkenRecursionValue
  change 2 ≤ sInf _
  apply le_csInf
  · exact ⟨_, Or.inr ⟨1, by decide, by decide, rfl⟩⟩
  · rintro k (⟨d, hd, hd_one, hd_two, -⟩ | ⟨η, hη, hηn, rfl⟩)
    · have hd_pos := Nat.pos_of_dvd_of_pos hd (by decide)
      have hd_le := Nat.le_of_dvd (by decide) hd
      omega
    · exact Nat.add_le_add (mahlerPopkenComplexity_pos (by decide) hη)
        (mahlerPopkenComplexity_pos (by decide) (Nat.sub_pos_of_lt hηn))

end MathlibExt.NumberTheory.MahlerPopkenComplexityWanted
