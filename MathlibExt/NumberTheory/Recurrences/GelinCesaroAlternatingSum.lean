/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The alternating Gelin–Cesàro sum

For a generalized Fibonacci sequence, the quadratic expression in two consecutive terms
changes sign at each step. This lets us express the Gelin–Cesàro summand as the sum of two
consecutive boundary terms and telescope after multiplying by the alternating sign.
-/

namespace MetaMathlibExt
namespace generalized_fibonacci_gelin_cesaro_alternating_sum

variable {W : ℤ → ℝ} {p : ℝ}

/-- The signed quadratic expression in the seeds can be evaluated at any integer index. -/
private theorem signed_seed (hW : ∀ j : ℤ, W (j + 2) = p * W (j + 1) + W j) (t : ℤ) :
    (-1 : ℝ) ^ t * (p * W 0 * W 1 + W 0 ^ 2 - W 1 ^ 2) =
      p * W t * W (t + 1) + W t ^ 2 - W (t + 1) ^ 2 := by
  let Q (i : ℤ) := p * W i * W (i + 1) + W i ^ 2 - W (i + 1) ^ 2
  have step (i : ℤ) : Q (i + 1) = -Q i := by
    dsimp [Q]
    rw [show i + 1 + 1 = i + 2 by omega, hW]
    ring
  have shift (i : ℤ) :
      ((-1 : ℝ) ^ (i + 1) * Q 0 = Q (i + 1)) ↔ ((-1 : ℝ) ^ i * Q 0 = Q i) := by
    rw [step, zpow_add_one₀ (by norm_num), mul_neg_one, neg_mul, neg_inj]
  change (-1 : ℝ) ^ t * Q 0 = Q t
  induction t with
  | zero => simp
  | succ i ih => exact (shift i).2 ih
  | pred i ih => exact (shift (-i - 1)).1 (by simpa using ih)

/-- The two boundary ratios at a common shift. -/
private noncomputable def boundary (W : ℤ → ℝ) (t : ℤ) : ℝ :=
  (W t + W (t - 2)) / W (t - 1) + (W (t + 3) + W (t + 1)) / W (t + 2)

/-- Splitting the unsigned summand at index `t` into two consecutive boundary terms. -/
private theorem split_summand (hW : ∀ j : ℤ, W (j + 2) = p * W (j + 1) + W j) (t : ℤ)
    (hden : W (t - 2) * W (t - 1) * W (t + 1) * W (t + 2) ≠ 0) :
    2 * W t * (W (t + 1) + W (t - 1)) *
        (2 * W t ^ 2 + (-1 : ℝ) ^ t *
          ((p * W 0 * W 1 + W 0 ^ 2 - W 1 ^ 2) * (p ^ 2 - 1))) /
        (W (t - 2) * W (t - 1) * W (t + 1) * W (t + 2)) =
      boundary W (t - 1) + boundary W t := by
  have back (i : ℤ) : W (i - 1) = W (i + 1) - p * W i := by
    rw [eq_sub_iff_add_eq, add_comm]
    simpa only [sub_add_cancel, show i - 1 + 2 = i + 1 by omega] using (hW (i - 1)).symm
  rw [← mul_assoc ((-1 : ℝ) ^ t), signed_seed hW]
  simp only [boundary, sub_add_cancel, show t - 1 - 2 = t - 3 by omega,
    show t - 1 - 1 = t - 2 by omega, show t - 1 + 3 = t + 2 by omega,
    show t - 1 + 2 = t + 1 by omega]
  simp only [mul_ne_zero_iff] at hden
  obtain ⟨⟨⟨hm₂, hm₁⟩, hp₁⟩, hp₂⟩ := hden
  field_simp [hm₂, hm₁, hp₁, hp₂]
  -- Express all neighbors in terms of the adjacent pair at `t` and `t + 1`.
  rw [show t - 3 = (t - 2) - 1 by omega, back (t - 2),
    show t - 2 + 1 = t - 1 by omega, show t - 2 = (t - 1) - 1 by omega, back (t - 1),
    sub_add_cancel, back t, show t + 3 = (t + 1) + 2 by omega, hW (t + 1),
    show t + 1 + 1 = t + 2 by omega, hW t]
  ring

end generalized_fibonacci_gelin_cesaro_alternating_sum

open generalized_fibonacci_gelin_cesaro_alternating_sum in
/-- **Alternating Gelin–Cesàro sum for generalized Fibonacci sequences.** Let $p$ be a real
number, let $W : \mathbb{Z} \to \mathbb{R}$ satisfy $W_{j+2} = p W_{j+1} + W_j$ for every integer
$j$, and put $\gamma_W = (p W_0 W_1 + W_0^2 - W_1^2)(p^2 - 1)$. Let $n \ge 0$ and $k$ be
integers such that $W_{j+k-2} W_{j+k-1} W_{j+k+1} W_{j+k+2} \ne 0$ for $1 \le j \le n$ and
$W_{n+k-1}$, $W_{k-1}$, $W_{n+k+2}$, $W_{k+2}$ are nonzero. Then

$$
\sum_{j=1}^{n} \frac{(-1)^{j-1} \cdot 2 W_{j+k} (W_{j+k+1} + W_{j+k-1})
\bigl(2 W_{j+k}^2 + (-1)^{j+k} \gamma_W\bigr)}{W_{j+k-2} W_{j+k-1} W_{j+k+1} W_{j+k+2}} =
(-1)^{n+1} \frac{W_{n+k} + W_{n+k-2}}{W_{n+k-1}} + \frac{W_k + W_{k-2}}{W_{k-1}} +
(-1)^{n+1} \frac{W_{n+k+3} + W_{n+k+1}}{W_{n+k+2}} + \frac{W_{k+3} + W_{k+1}}{W_{k+2}}.
$$

The paper's standing assumption $p \ne 0$ is not needed.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 11
(`jis-2024-24.6.2-prop-11`). -/
public theorem generalized_fibonacci_gelin_cesaro_alternating_sum
    (W : ℤ → ℝ) (p : ℝ) (hW : ∀ j : ℤ, W (j + 2) = p * W (j + 1) + W j)
    (n : ℕ) (k : ℤ)
    (hden : ∀ j ∈ Finset.Icc 1 n,
      W (j + k - 2) * W (j + k - 1) * W (j + k + 1) * W (j + k + 2) ≠ 0)
    (h₁ : W (n + k - 1) ≠ 0) (h₂ : W (k - 1) ≠ 0) (h₃ : W (n + k + 2) ≠ 0)
    (h₄ : W (k + 2) ≠ 0) :
    ∑ j ∈ Finset.Icc 1 n, (-1 : ℝ) ^ (j - 1) * 2 * W (j + k) *
          (W (j + k + 1) + W (j + k - 1)) *
          (2 * W (j + k) ^ 2 + (-1 : ℝ) ^ ((j : ℤ) + k) *
            ((p * W 0 * W 1 + W 0 ^ 2 - W 1 ^ 2) * (p ^ 2 - 1))) /
          (W (j + k - 2) * W (j + k - 1) * W (j + k + 1) * W (j + k + 2)) =
      (-1 : ℝ) ^ (n + 1) * (W (n + k) + W (n + k - 2)) / W (n + k - 1) +
        (W k + W (k - 2)) / W (k - 1) +
        (-1 : ℝ) ^ (n + 1) * (W (n + k + 3) + W (n + k + 1)) / W (n + k + 2) +
        (W (k + 3) + W (k + 1)) / W (k + 2) := by
  let B (j : ℕ) := (-1 : ℝ) ^ j * boundary W (j + k)
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  calc
    _ = ∑ j ∈ Finset.range n, (B j - B (j + 1)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Nat.add_comm 1 j, Nat.add_sub_cancel]
      have hj' : j + 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, Finset.mem_range.mp hj⟩
      have h := split_summand hW ((j + 1 : ℕ) + k) (hden _ hj')
      conv_rhs at h => rw [show ((j + 1 : ℕ) : ℤ) + k - 1 = j + k by omega]
      dsimp only [B]
      rw [pow_succ (-1 : ℝ) j, mul_neg_one, neg_mul, sub_neg_eq_add, ← mul_add, ← h]
      ring
    _ = B 0 - B n := Finset.sum_range_sub' B n
    _ = _ := by
      simp only [B, boundary, pow_zero, Nat.cast_zero, zero_add, one_mul, pow_succ]
      field_simp [h₁, h₂, h₃, h₄]
      ring

end MetaMathlibExt
