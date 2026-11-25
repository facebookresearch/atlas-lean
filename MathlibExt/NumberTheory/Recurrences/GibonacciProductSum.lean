/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! # A telescoping sum of products of two gibonacci sequences -/

namespace MetaMathlibExt

/-- **Sum of products of two gibonacci sequences.** Let $G, H \colon \mathbb{Z} \to \mathbb{R}$
satisfy $G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$. For every
natural number $n$ and all integers $k$ and $s$,
$$2 \sum_{j=1}^{n} G_{j+k} H_{j+s} = G_{n+k} H_{n+s+1} + G_{n+k+1} H_{n+s} -
G_{k+1} H_s - G_k H_{s+1}.$$

The printed statement lacks the factor $2$: it fails for the Fibonacci sequence $G = H = F$
with $k = s = 0$ and $n = 1$, where the left side is $1$ and the right side $2$. The paper's own
derivation (its display before the proposition) carries the factor $2$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 30
(`jis-2024-24.6.2-prop-30`). -/
public theorem two_mul_sum_gibonacci_mul_gibonacci
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (n : ℕ) (k s : ℤ) :
    2 * ∑ j ∈ Finset.Icc 1 n, G (j + k) * H (j + s) =
      G (n + k) * H (n + s + 1) + G (n + k + 1) * H (n + s) - G (k + 1) * H s -
        G k * H (s + 1) := by
  let cross (m : ℤ) := G (m + k) * H (m + s + 1) + G (m + k + 1) * H (m + s)
  -- The recurrence in each factor contributes one copy of the product.
  have hcross (m : ℤ) :
      cross (m + 1) - cross m = 2 * (G (m + 1 + k) * H (m + 1 + s)) := by
    dsimp only [cross]
    rw [add_right_comm m 1 k, add_right_comm m 1 s,
      add_assoc (m + k) 1 1, add_assoc (m + s) 1 1, one_add_one_eq_two, hG (m + k), hH (m + s)]
    ring
  have hsum (m : ℕ) :
      2 * ∑ j ∈ Finset.Icc 1 m, G (j + k) * H (j + s) = cross m - cross 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)), mul_add, ih,
        Nat.cast_succ, ← hcross m]
      ring
  rw [hsum]
  simp only [cross, zero_add]
  ring

end MetaMathlibExt
