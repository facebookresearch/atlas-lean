/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.JosephusFunction

namespace MathlibExt.NumberTheory.JosephusWanted

/-- **The Josephus function just after a fixed point.** Let $k \ge 2$ and $n_p \ge 1$ be natural
numbers with $J_k(n_p) = n_p$, where $J_k$ is the Josephus function. Then $J_k(n_p + 1)$ is
determined as follows: (i) if $k \le n_p + 1$, then $J_k(n_p + 1) = k - 1$; (ii) if
$k = \ell(n_p + 1) + 1$ for some natural number $\ell \ge 1$, then $J_k(n_p + 1) = n_p + 1$;
(iii) if $k = \ell(n_p + 1) + k_1$ for some natural numbers $\ell \ge 1$ and $k_1$ with
$2 \le k_1 \le n_p$, then $J_k(n_p + 1) = k_1 - 1$; (iv) if $k = (\ell + 1)(n_p + 1)$ for some
natural number $\ell \ge 1$, then $J_k(n_p + 1) = n_p$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Proposition 4. -/
public theorem josephus_fixed_succ_cases (k np : ℕ)
    (hk : 2 ≤ k) (hnp : 1 ≤ np)
    (hfix : MetaMathlibExt.josephus k np = np) :
    (k ≤ np + 1 → MetaMathlibExt.josephus k (np + 1) = k - 1) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → k = ℓ * (np + 1) + 1 →
      MetaMathlibExt.josephus k (np + 1) = np + 1) ∧
    (∀ ℓ k1 : ℕ, 1 ≤ ℓ → 2 ≤ k1 → k1 ≤ np →
      k = ℓ * (np + 1) + k1 →
        MetaMathlibExt.josephus k (np + 1) = k1 - 1) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → k = (ℓ + 1) * (np + 1) →
      MetaMathlibExt.josephus k (np + 1) = np) := by
  have survivor (q : ℕ) {j : ℕ} (hj : 1 ≤ j) (hj' : j ≤ np + 1)
      (hsum : np + k = q * (np + 1) + j) : MetaMathlibExt.josephus k (np + 1) = j := by
    rw [MetaMathlibExt.josephus_succ k np hk hnp, hfix, hsum, Nat.add_sub_assoc hj,
      Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    refine survivor 1 (by omega) (by omega) ?_
    rw [Nat.one_mul]
    omega
  · intro ℓ _ h
    apply survivor ℓ <;> omega
  · intro ℓ k1 _ hlo hhi h
    refine survivor (ℓ + 1) (by omega) (by omega) ?_
    rw [Nat.succ_mul]
    omega
  · intro ℓ _ h
    apply survivor (ℓ + 1) <;> omega

end MathlibExt.NumberTheory.JosephusWanted
