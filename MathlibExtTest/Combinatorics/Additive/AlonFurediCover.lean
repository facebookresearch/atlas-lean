/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.AlonFurediCover

@[expose] public section

open MathlibExt.Combinatorics.Additive.AlonFurediCover

namespace MathlibExtTest.Combinatorics.Additive.AlonFurediCover

-- The `n` hyperplanes `x_j = 1` cover every vertex of `{0, 1}ⁿ` except `0`: the hypotheses are
-- satisfiable with `m = n`, so the bound `n ≤ m` is tight.
theorem coordinate_hyperplanes_cover (n : ℕ) (x : Fin n → ℚ) (hx : ∀ j, x j = 0 ∨ x j = 1)
    (hx0 : x ≠ 0) : ∃ i, ∑ j, (if i = j then (1 : ℚ) else 0) * x j = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push Not at h; exact hx0 (funext h)
  refine ⟨i, ?_⟩
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact (hx i).resolve_left hi

example (n : ℕ) : n ≤ n :=
  le_card_of_covers (m := n) (fun i j => if i = j then (1 : ℚ) else 0) (fun _ => 1) 0
    (fun _ => Or.inl rfl) (fun x hx hx0 => coordinate_hyperplanes_cover n x hx hx0)
    (fun _ => by simp)

end MathlibExtTest.Combinatorics.Additive.AlonFurediCover
