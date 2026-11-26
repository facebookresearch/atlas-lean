/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.JosephusFunction

/-!
# The Josephus recurrence by number of wrap-arounds
-/

namespace MathlibExt.NumberTheory.JosephusWanted

/-- **Josephus recurrence by number of wrap-arounds.** Let $k \ge 2$ and $n \ge 1$ be natural
numbers, let $J_k$ be the Josephus function and write $p = J_k(n)$. If $\ell$ is a natural
number with $\ell(n+1) + 1 \le p + k \le (\ell+1)(n+1)$, then $J_k(n+1) = p + k - \ell(n+1)$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Theorem 2. -/
public theorem josephus_succ_eq_sub (k n ℓ : ℕ) (hk : 2 ≤ k)
    (hn : 1 ≤ n)
    (h : ℓ * (n + 1) + 1 ≤ MetaMathlibExt.josephus k n + k ∧
      MetaMathlibExt.josephus k n + k ≤ (ℓ + 1) * (n + 1)) :
    MetaMathlibExt.josephus k (n + 1) =
      MetaMathlibExt.josephus k n + k - ℓ * (n + 1) := by
  obtain ⟨hlower, hupper⟩ := h
  rw [Nat.add_mul, Nat.one_mul] at hupper
  -- Subtract one to get the zero-based remainder used by the recurrence.
  let r := MetaMathlibExt.josephus k n + k - ℓ * (n + 1) - 1
  have hr : r < n + 1 := by
    dsimp [r]
    omega
  have hsplit : MetaMathlibExt.josephus k n + k - 1 = ℓ * (n + 1) + r := by
    dsimp [r]
    omega
  rw [MetaMathlibExt.josephus_succ k n hk hn, hsplit, Nat.mul_add_mod_self_right,
    Nat.mod_eq_of_lt hr]
  dsimp [r]
  omega

end MathlibExt.NumberTheory.JosephusWanted
