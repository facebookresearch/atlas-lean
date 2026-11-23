/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rising factorial between consecutive powers

Pairing the first and last factors reduces the length by two while preserving
the bases of the bounding powers.
-/

namespace MetaMathlibExt

private theorem ascFactorial_bounds_half.paired_bounds (k n : ℕ) (hn : (k / 2 - 1) ^ 2 ≤ n) :
    (n + k / 2 - 1) ^ k ≤ n.ascFactorial k ∧ n.ascFactorial k ≤ (n + k / 2) ^ k := by
  induction k using Nat.twoStepInduction generalizing n with
  | zero => simp
  | one => simp [Nat.ascFactorial]
  | more k ih _ =>
    set m := k / 2 with hm
    have hhalf : (k + 2) / 2 = m + 1 := by omega
    rw [hhalf, Nat.add_sub_cancel] at hn
    have hinner := ih (n + 1) <| calc
      (m - 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le ..) _
      _ ≤ n + 1 := by omega
    have hlo : (n + m) ^ 2 ≤ n * (n + k + 1) := by
      have hk : 2 * m ≤ k := by omega
      nlinarith only [hn, Nat.mul_le_mul_left n hk]
    have hhi : n * (n + k + 1) ≤ (n + m + 1) ^ 2 := by
      have hk : k ≤ 2 * m + 1 := by omega
      nlinarith [Nat.mul_le_mul_left n hk]
    have hpair : n.ascFactorial (k + 2) = (n + 1).ascFactorial k * (n * (n + k + 1)) := by
      rw [Nat.ascFactorial_succ, Nat.ascFactorial_succ, ← Nat.succ_ascFactorial]
      ac_rfl
    rw [Nat.add_right_comm n 1 m, Nat.add_sub_cancel] at hinner
    rw [hpair, hhalf, ← Nat.add_assoc, Nat.add_sub_cancel, pow_add, pow_add]
    exact ⟨Nat.mul_le_mul hinner.1 hlo, Nat.mul_le_mul hinner.2 hhi⟩

/-- **Rising factorial between consecutive $k$-th powers.** Let $k$ and $n$ be natural numbers,
write $n^{\overline{k}} = n (n + 1) \cdots (n + k - 1)$ for the rising factorial, and let
$r = \lfloor (k^2 - 4k + 6)/4 \rfloor$ if $k$ is even and $r = \lfloor (k^2 - 6k + 11)/4 \rfloor$
if $k$ is odd. If $n \ge r$, then
$(n + \lfloor k/2 \rfloor - 1)^k \le n^{\overline{k}} \le (n + \lfloor k/2 \rfloor)^k$.

Both numerators are positive: $k^2 - 4k + 6 = (k - 2)^2 + 2$ and $k^2 - 6k + 11 = (k - 3)^2 + 2$.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Lemma 1, Equation (8). -/
public theorem ascFactorial_bounds_half (k n : ℕ)
    (hn : (if Even k then (k ^ 2 + 6 - 4 * k) / 4 else (k ^ 2 + 11 - 6 * k) / 4) ≤ n) :
    (n + k / 2 - 1) ^ k ≤ n.ascFactorial k ∧ n.ascFactorial k ≤ (n + k / 2) ^ k := by
  apply ascFactorial_bounds_half.paired_bounds
  match k with
  | 0 | 1 => exact Nat.zero_le _
  | k + 2 =>
    -- For lengths 2m + 2 and 2m + 3 the corresponding numerator is 4m² + 2.
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    all_goals
      simp [Nat.even_iff] at hn
      ring_nf at hn
      rw [show _ / 2 - 1 = m by omega]
      omega

end MetaMathlibExt
