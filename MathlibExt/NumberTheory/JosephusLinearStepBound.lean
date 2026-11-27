/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.JosephusFunction

/-!
# Linear steps at a low Josephus extremal point

The theorem `shift_le_iff_le_div` gives the largest admissible step count and a
condition under which at least one step is admissible.
-/

namespace MathlibExt.NumberTheory.JosephusWanted

/-- **Linear-step bound at a low extremal point.** Let $k \ge 2$ and $n$ be natural numbers, let
$J_k$ be the Josephus function, write $j = J_k(n+1)$, and suppose $j \le k - 1$. Then for every
natural number $m$, $j + km \le n + 1 + m$ holds if and only if
$m \le \lfloor (n - (j - 1)) / (k - 1) \rfloor$. Moreover, if $k - 2 + j \le n$, then
$\lfloor (n - (j - 1)) / (k - 1) \rfloor \ge 1$.

Since $1 \le J_k(n+1) \le n + 1$, the hypothesis says $j \in [1, k - 1]$, that is, $n + 1$ is a
low extremal point in the paper's sense, and none of the subtractions above is truncated.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Lemma 8. -/
public theorem shift_le_iff_le_div (k n : ℕ) (hk : 2 ≤ k)
    (hj : MetaMathlibExt.josephus k (n + 1) ≤ k - 1) :
    (∀ m : ℕ, MetaMathlibExt.josephus k (n + 1) + k * m ≤ n + 1 + m ↔
      m ≤ (n - (MetaMathlibExt.josephus k (n + 1) - 1)) / (k - 1)) ∧
    (k - 2 + MetaMathlibExt.josephus k (n + 1) ≤ n →
      1 ≤ (n - (MetaMathlibExt.josephus k (n + 1) - 1)) / (k - 1)) := by
  obtain ⟨hj_one, hj_size⟩ := MetaMathlibExt.josephus_range k (n + 1) hk (Nat.succ_pos n)
  have hk_pos : 0 < k - 1 := Nat.le_trans hj_one hj
  constructor
  · intro m
    rw [Nat.le_div_iff_mul_le hk_pos, Nat.mul_sub, Nat.mul_one, Nat.mul_comm m k]
    omega
  · intro hn
    rw [Nat.le_div_iff_mul_le hk_pos, Nat.one_mul]
    omega

end MathlibExt.NumberTheory.JosephusWanted
