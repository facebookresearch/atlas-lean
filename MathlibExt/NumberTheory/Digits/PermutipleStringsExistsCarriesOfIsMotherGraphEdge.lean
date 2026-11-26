/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.PermutipleStrings
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring

/-!
# A multigraph characterization of permutiple strings (Holt)

Every mother-graph edge admits bounded natural carries satisfying the carry equation.

Further statements from Benjamin V. Holt, *A Multigraph Characterization of Permutiple
Strings*, INTEGERS 25 (2025), Article A111 (arXiv:2505.11414).

The proof adapts the proof of `isHoeySloaneStep_hoeySloaneTransition` in
`MathlibExt.NumberTheory.Digits.PermutipleStrings`, obtaining positivity of the base from the
first digit bound instead of from `1 < n < b`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Every mother-graph edge induces a carry transition.** Let $n$ and $b$ be natural
numbers. If $(d_1, d_2)$ is an edge of the $(n, b)$-mother graph, then there are natural
numbers $c_1$ and $c_2$ with $c_1 \le n - 1$ and $c_2 \le n - 1$ such that
$b c_2 - c_1 = n d_2 - d_1$ as integers.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 6 (`integers-2025-A111-thm-6`). -/
public theorem exists_carries_of_isMotherGraphEdge (n b d₁ d₂ : ℕ)
    (h : IsMotherGraphEdge n b d₁ d₂) :
    ∃ c₁ c₂ : ℕ, c₁ ≤ n - 1 ∧ c₂ ≤ n - 1 ∧ (b : ℤ) * c₂ - c₁ = (n : ℤ) * d₂ - d₁
    := by
  let c₁ := ((d₁ : ℤ) + ((b : ℤ) - n) * d₂) % b
  let c₂ := ((n : ℤ) * d₂ - d₁ + c₁) / b
  have hd₁ : (d₁ : ℤ) < b := by exact_mod_cast h.1
  have hb : 0 < (b : ℤ) := by omega
  have hc₁ : 0 ≤ c₁ := Int.emod_nonneg _ hb.ne'
  have hc₁_le : c₁ ≤ (n : ℤ) - 1 := h.2.2
  have hdvd : (b : ℤ) ∣ (n : ℤ) * d₂ - d₁ + c₁ := by
    use (d₂ : ℤ) - (((d₁ : ℤ) + ((b : ℤ) - n) * d₂) / b)
    dsimp only [c₁]
    rw [Int.emod_def]
    ring
  have hcarry : (b : ℤ) * c₂ = n * d₂ - d₁ + c₁ := Int.mul_ediv_cancel' hdvd
  have lower : -1 < c₂ := by
    apply (mul_lt_mul_iff_right₀ hb).mp
    rw [hcarry, mul_neg_one]
    have hprod := Int.mul_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg d₂)
    omega
  have upper : c₂ < n := by
    apply (mul_lt_mul_iff_right₀ hb).mp
    rw [hcarry, mul_comm (b : ℤ) n]
    have hd₂ : (d₂ : ℤ) + 1 ≤ b := by exact_mod_cast h.2.1
    have hprod := mul_le_mul_of_nonneg_left hd₂ (Int.natCast_nonneg n)
    rw [mul_add, mul_one] at hprod
    omega
  refine ⟨c₁.toNat, c₂.toNat, by omega, by omega, ?_⟩
  rw [Int.toNat_of_nonneg hc₁, Int.toNat_of_nonneg (by omega : 0 ≤ c₂), hcarry]
  omega

end

end MetaMathlibExt
