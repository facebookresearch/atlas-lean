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
initial value, so the reciprocals of the expansion terms sum to that value. The gap
sequence gives a recurrence for successive expansion terms, and a zero gap stays zero at the
next step.

## References

* Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential Sequences*,
  *INTEGERS* 26 (2026), Article A28, pp. 1–17, Section 2, Definitions 1–2 and Lemmas 1–3.
  <https://math.colgate.edu/~integers/aa28/aa28.pdf>
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

private theorem inv_remainder_lt_expansion (r : ℝ) (n : ℕ) :
    (pseudoGreedyRemainder r n)⁻¹ < (pseudoGreedyExpansion r n : ℝ) := by
  unfold pseudoGreedyExpansion
  linarith [Int.lt_floor_add_one ((pseudoGreedyRemainder r n)⁻¹ + 1 + 1 / 2)]

private theorem remainder_pos {r : ℝ} (hr : 0 < r) (n : ℕ) : 0 < pseudoGreedyRemainder r n := by
  induction n with
  | zero => exact hr
  | succ n ih =>
    rw [pseudoGreedyRemainder_succ, sub_pos, one_div]
    exact inv_lt_of_inv_lt₀ ih (inv_remainder_lt_expansion r n)

/-- **Positivity of the pseudo-greedy expansion.** If $r > 0$, every term $a_n$ of its
pseudo-greedy expansion is a positive integer. This follows from positivity of the remainders
and the nearest-integer rule in Junnosuke Koizumi's Definition 1. -/
theorem pseudoGreedyExpansion_pos {r : ℝ} (hr : 0 < r) (n : ℕ) :
    0 < pseudoGreedyExpansion r n := by
  exact_mod_cast (inv_pos.mpr (remainder_pos hr n)).trans (inv_remainder_lt_expansion r n)

/-- **Convergence of the pseudo-greedy expansion.** For every real number $r > 0$, the
pseudo-greedy expansion $(a_n)_{n \ge 0}$ of $r$ satisfies $\sum_n 1 / a_n = r$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Lemma 1 (`integers-2026-A28-lem-1`). -/
theorem hasSum_one_div_pseudoGreedyExpansion {r : ℝ} (hr : 0 < r) :
    HasSum (fun n => 1 / (pseudoGreedyExpansion r n : ℝ)) r := by
  let x := pseudoGreedyRemainder r
  let a (n : ℕ) : ℝ := pseudoGreedyExpansion r n
  have hstep (n) : x (n + 1) = x n - 1 / a n := pseudoGreedyRemainder_succ r n
  have hx (n) : 0 < x n := remainder_pos hr n
  have ha (n) : 0 < a n := by
    dsimp only [a]
    exact_mod_cast pseudoGreedyExpansion_pos hr n
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

/-- **Recursion for the pseudo-greedy expansion.** Let $r > 0$ be a real number, and let
$(a_n)$ be its pseudo-greedy expansion and $(\varepsilon_n)$ its gap sequence. Then for every
$n \ge 0$,
$$a_{n+1} = \frac{a_n^2}{1 - \varepsilon_n} - a_n + (1 - \varepsilon_{n+1}).$$

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Lemma 2 (`integers-2026-A28-lem-2`). -/
theorem pseudoGreedyExpansion_succ_eq {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (pseudoGreedyExpansion r (n + 1) : ℝ) =
      1 / (1 - pseudoGreedyGap r n) * (pseudoGreedyExpansion r n : ℝ) ^ 2 -
        pseudoGreedyExpansion r n + (1 - pseudoGreedyGap r (n + 1)) := by
  let u := (pseudoGreedyRemainder r n)⁻¹
  let a : ℝ := pseudoGreedyExpansion r n
  have hu : 0 < u := inv_pos.mpr (remainder_pos hr n)
  have hua : u < a := inv_remainder_lt_expansion r n
  have hnext : pseudoGreedyRemainder r (n + 1) = (a - u) / (u * a) := by
    rw [pseudoGreedyRemainder_succ, one_div]
    simpa only [u, inv_inv] using inv_sub_inv hu.ne' (hu.trans hua).ne'
  have hgap : 1 - pseudoGreedyGap r n = a - u := by
    change 1 - (u + 1 - a) = a - u
    ring
  rw [hgap, pseudoGreedyGap, hnext, inv_div]
  field_simp [(sub_pos.mpr hua).ne']
  ring

/-- **A vanishing gap stays zero.** Let $r > 0$ be a real number and let $(\varepsilon_n)$ be
the gap sequence of its pseudo-greedy expansion. For every $n \ge 0$, if $\varepsilon_n = 0$,
then $\varepsilon_{n+1} = 0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Lemma 3 (`integers-2026-A28-lem-3`). -/
theorem pseudoGreedyGap_succ_eq_zero {r : ℝ} (hr : 0 < r) {n : ℕ}
    (h : pseudoGreedyGap r n = 0) : pseudoGreedyGap r (n + 1) = 0 := by
  let a := pseudoGreedyExpansion r n
  have hrec := pseudoGreedyExpansion_succ_eq hr n
  rw [h, sub_zero, div_one, one_mul, pseudoGreedyGap] at hrec
  have hround : (pseudoGreedyRemainder r (n + 1))⁻¹ + 1 = ((a ^ 2 - a + 1 : ℤ) : ℝ) := by
    push_cast
    dsimp only [a]
    linarith
  rw [pseudoGreedyGap, pseudoGreedyExpansion, hround, Int.floor_intCast_add]
  norm_num

end

end MetaMathlibExt
