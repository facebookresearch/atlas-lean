/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith

/-!
# Pseudo-greedy expansions into unit fractions

The remainders of Koizumi's pseudo-greedy expansion tend to zero for every positive
initial value, so the reciprocals of the expansion terms sum to that value.
-/

open Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- **Pseudo-greedy remainder sequence.** For a real number $r$, the remainder sequence
$(x_n)_{n \ge 0}$ of the pseudo-greedy expansion of $r$ is defined by $x_0 = r$ and
$x_{n+1} = x_n - 1/a_n$, where $a_n = \lfloor x_n^{-1} + 1 + 1/2 \rfloor$ is the integer
nearest to $x_n^{-1} + 1$, with halves rounded up.

Here $0^{-1}$ and $1/0$ are read as $0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definitions of the pseudo-greedy
expansion and its remainder sequence). -/
noncomputable def pseudoGreedyRemainder (r : ℝ) : ℕ → ℝ
  | 0 => r
  | n + 1 => pseudoGreedyRemainder r n -
      1 / (⌊(pseudoGreedyRemainder r n)⁻¹ + 1 + 1 / 2⌋ : ℝ)

/-- **Pseudo-greedy expansion.** Let $r$ be a real number with pseudo-greedy remainder sequence
$(x_n)_{n \ge 0}$. The pseudo-greedy expansion of $r$ is the integer sequence
$a_n = \lfloor x_n^{-1} + 1 + 1/2 \rfloor$ for $n \ge 0$; that is, $a_n$ is the integer nearest
to $x_n^{-1} + 1$, with halves rounded up.

Here $0^{-1}$ is read as $0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definition of the pseudo-greedy
expansion). -/
noncomputable def pseudoGreedyExpansion (r : ℝ) (n : ℕ) : ℤ :=
  ⌊(pseudoGreedyRemainder r n)⁻¹ + 1 + 1 / 2⌋

/-- **Gap sequence of the pseudo-greedy expansion.** Let $r$ be a real number, and let $(x_n)$
be the remainder sequence and $(a_n)$ the pseudo-greedy expansion of $r$. The gap sequence of
$r$ is the real sequence $\varepsilon_n = x_n^{-1} + 1 - a_n$ for $n \ge 0$.

Here $0^{-1}$ is read as $0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definition of the gap sequence). -/
noncomputable def pseudoGreedyGap (r : ℝ) (n : ℕ) : ℝ :=
  (pseudoGreedyRemainder r n)⁻¹ + 1 - pseudoGreedyExpansion r n

/-- **Remainder recursion.** For every real number $r$ and every $n \ge 0$, the remainder
sequence $(x_n)$ and the pseudo-greedy expansion $(a_n)$ of $r$ satisfy $x_{n+1} = x_n - 1/a_n$.

Here $1/0$ is read as $0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definition of the remainder
sequence). -/
theorem pseudoGreedyRemainder_succ (r : ℝ) (n : ℕ) :
    pseudoGreedyRemainder r (n + 1) =
      pseudoGreedyRemainder r n - 1 / (pseudoGreedyExpansion r n : ℝ) := rfl

/-- **The pseudo-greedy expansion of 1 starts with 2.** The first term $a_0$ of the
pseudo-greedy expansion of $1$ equals $2$, the first Sylvester number.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Example 1 (the expansion of `1` is the Sylvester
sequence). -/
theorem pseudoGreedyExpansion_one_zero : pseudoGreedyExpansion 1 0 = 2 := by
  rw [pseudoGreedyExpansion, pseudoGreedyRemainder, Int.floor_eq_iff]
  norm_num

/-- **Second term of the pseudo-greedy expansion of $1$.** The pseudo-greedy expansion
$(a_n)_{n \ge 0}$ of $1$ satisfies $a_1 = 3$.

The remainder after the first term $a_0 = 2$ is $1 - 1/2 = 1/2$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Example 1 (the expansion of `1` is the Sylvester
sequence). -/
theorem pseudoGreedyExpansion_one_one : pseudoGreedyExpansion 1 1 = 3 := by
  have h : pseudoGreedyRemainder 1 1 = 1 / 2 := by
    rw [pseudoGreedyRemainder_succ, pseudoGreedyExpansion_one_zero]
    simp only [pseudoGreedyRemainder]
    norm_num
  rw [pseudoGreedyExpansion, h, Int.floor_eq_iff]
  norm_num

/-- **The first gap of the expansion of 1 vanishes.** The first term $\varepsilon_0$ of the gap
sequence of the pseudo-greedy expansion of $1$ is $0$: the first remainder is $x_0 = 1$ and the
first term of the expansion is $a_0 = 2$, so $\varepsilon_0 = x_0^{-1} + 1 - a_0 = 1 + 1 - 2 = 0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Example 1 (`ε_n = 0` for the expansion of `1`). -/
theorem pseudoGreedyGap_one_zero : pseudoGreedyGap 1 0 = 0 := by
  rw [pseudoGreedyGap, pseudoGreedyExpansion_one_zero]
  simp only [pseudoGreedyRemainder]
  norm_num

/-- **Convergence of the pseudo-greedy expansion.** For every real number $r > 0$, the
pseudo-greedy expansion $(a_n)_{n \ge 0}$ of $r$ satisfies $\sum_n 1 / a_n = r$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Lemma 1 (`integers-2026-A28-lem-1`). -/
theorem hasSum_one_div_pseudoGreedyExpansion {r : ℝ} (hr : 0 < r) :
    HasSum (fun n => 1 / (pseudoGreedyExpansion r n : ℝ)) r := by
  let x := pseudoGreedyRemainder r
  let a (n : ℕ) : ℝ := pseudoGreedyExpansion r n
  have hstep (n) : x (n + 1) = x n - 1 / a n := pseudoGreedyRemainder_succ r n
  have hlower (n) : (x n)⁻¹ < a n := by
    change (x n)⁻¹ < (⌊(x n)⁻¹ + 1 + 1 / 2⌋ : ℝ)
    linarith [Int.lt_floor_add_one ((x n)⁻¹ + 1 + 1 / 2)]
  have hx (n) : 0 < x n := by
    induction n with
    | zero => exact hr
    | succ n ih =>
      rw [hstep, sub_pos, one_div]
      exact inv_lt_of_inv_lt₀ ih (hlower n)
  have ha (n) : 0 < a n := (inv_pos.mpr (hx n)).trans (hlower n)
  have hterm (n) : 0 ≤ 1 / a n := (one_div_pos.mpr (ha n)).le
  have hsum (n) : ∑ k ∈ Finset.range n, 1 / a k = r - x n := by
    induction n with
    | zero => simp [x, pseudoGreedyRemainder]
    | succ n ih => rw [Finset.sum_range_succ, ih, hstep]; abel
  have hs := summable_of_sum_range_le hterm
    (fun n => (hsum n).le.trans (sub_le_self r (hx n).le))
  -- The floor upper bound gives xₙ ≤ (1 + 2r) / aₙ, whose right side tends to zero.
  have hbound (n) : x n ≤ (1 + 2 * r) * (1 / a n) := by
    have hxr : x n ≤ r := sub_nonneg.mp <| hsum n ▸ Finset.sum_nonneg (fun k _ => hterm k)
    have hu : a n ≤ (x n)⁻¹ + 2 :=
      (Int.floor_le ((x n)⁻¹ + 1 + 1 / 2)).trans (by linarith)
    rw [mul_one_div, le_div_iff₀ (ha n)]
    calc
      x n * a n ≤ x n * ((x n)⁻¹ + 2) := mul_le_mul_of_nonneg_left hu (hx n).le
      _ ≤ 1 + 2 * r := by rw [mul_add, mul_inv_cancel₀ (hx n).ne']; linarith
  have hzero : Tendsto x atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (hx n).le) hbound
    simpa using hs.tendsto_atTop_zero.const_mul (1 + 2 * r)
  apply (hasSum_iff_tendsto_nat_of_nonneg hterm r).mpr
  simp only [hsum]
  simpa using hzero.const_sub r

end

end MetaMathlibExt
