/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FixedPointsKPermutations

/-!
# A recurrence for permutations counted by cycles and fixed points

Marking a fixed point gives a recurrence relating the counts on two consecutive set sizes.
-/

namespace MetaMathlibExt

/-- **Recurrence for permutations counted by cycles and fixed points.** Write $a(n, k, j)$ for the
number of permutations of an $n$-element set with exactly $k$ cycles (fixed points counted as
cycles of length one) and exactly $j$ fixed points. For all natural numbers $n$, $k$ and $j$
with $1 \le j \le k$, $j \, a(n, k, j) = n \, a(n - 1, k - 1, j - 1)$, where $n - 1$ is read as
$0$ when $n = 0$.

The paper assumes $n \ge k \ge 1$; the identity holds for all $n$.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (iii) (`integers-2024-A54-prop-3`). -/
public theorem mul_kPermFixedPointCount {n k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    j * kPermFixedPointCount n k j = n * kPermFixedPointCount (n - 1) (k - 1) (j - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ k by omega)
  rw [kPermFixedPointCount_eq_choose_mul_derangement hjk]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    rw [kPermFixedPointCount_eq_choose_mul_derangement (Nat.le_of_succ_le_succ hjk),
      ← Nat.mul_assoc (n + 1), Nat.add_one_mul_choose_eq, Nat.mul_comm _ (j + 1), Nat.mul_assoc]

end MetaMathlibExt
