/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Log-behavior of the A005773 recurrence

Let `A : ℕ → ℝ` satisfy `A 0 = A 1 = 1` and
`(n + 1) A (n + 1) = 2 (n + 1) A n + 3 (n - 1) A (n - 1)` for `n ≥ 1` (OEIS A005773,
`1, 1, 2, 5, 13, 35, …`). With `x n = A (n + 1) / A n` and `φ n = 3 (2n + 1) / (2 (n + 1))`,
Lemma 1 of Zhao's paper states that, for every `n ≥ 0`, `x n ≤ φ n` and
`x (n + 1) / x n ≥ 2 (3n² + 6n + 2) / ((n + 2)(2n + 1) φ n)`. Both inequalities are equalities
at `n = 2`, where `x 2 = 5 / 2 = φ 2` and `x 3 / x 2 = 26 / 25`. The ratio bounds also give
log-convexity of `(n * A n) ^ n` for indices starting at one.

Forward differences are written out: `ΔA n = A (n + 1) - A n`,
`Δ²A n = A (n + 2) - 2 A (n + 1) + A n`,
`Δ³A n = A (n + 3) - 3 A (n + 2) + 3 A (n + 1) - A n`. A sequence `(z n)_{n ≥ m}` is
log-convex (log-concave) if `z n ^ 2 ≤ z (n - 1) z (n + 1)` (`≥`) for every `n ≥ m + 1`, and
log-balanced (Došlić) if it is log-convex and `(z n / n!)_{n ≥ m}` is log-concave.

## Proof

Every `A n` is positive, by induction along the recurrence. Divided by `(n + 2) A (n + 1)`, the
recurrence `(n + 2) A (n + 2) = 2 (n + 2) A (n + 1) + 3n A n` at `n + 1` reads
`x (n + 1) = 2 + 3n / ((n + 2) x n)`. An induction proves `x n ≤ φ n` together with the lower
bound `6n / (2n + 1) ≤ x n`: the lower bound for `x n` gives the upper bound for `x (n + 1)`, and
the upper bound for `x n`, with `φ n ≤ φ (n + 1)`, gives the lower bound for `x (n + 1)`. For the
second inequality, clear the positive denominators and use the recurrence at `n + 1`: the
right-hand side minus the left-hand side becomes
`(3 (2n + 1) A n - 2 (n + 1) A (n + 1)) (3n (2n + 1) A n + 2 (3n² + 6n + 2) A (n + 1))`,
whose first factor is nonnegative by `x n ≤ φ n` and whose second factor is positive.

## Main results

* `MetaMathlibExt.a005773Recurrence_ratio_bounds`: both bounds, for every `n`.
* `MetaMathlibExt.a005773Recurrence_thirdDiff_logConvex_logBalanced`: log-behavior of Δ³A.
* `MetaMathlibExt.a005773Recurrence_weighted_logConcave`: log-concavity of four weighted sequences.
* `MetaMathlibExt.a005773Recurrence_diff_logBalanced`: log-behavior of ΔA and Δ²A.
* `MetaMathlibExt.a005773Recurrence_pow_logConvex`: log-convexity of `(n * A n) ^ n`.

## References

* Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
  Sequence*, INTEGERS 25 (2025), Article A100.
-/

namespace MetaMathlibExt

@[expose] public section

variable {A : ℕ → ℝ}

/-- The recurrence at index `n + 1`, with the casts pushed through. -/
private lemma a005773Recurrence_succ
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) :
    ((n : ℝ) + 2) * A (n + 2) = 2 * ((n : ℝ) + 2) * A (n + 1) + 3 * n * A n := by
  have h := hrec (n + 1) (by omega)
  rw [Nat.add_sub_cancel] at h
  push_cast at h
  linear_combination h

/-- The recurrence solved for its last term. -/
private lemma a005773Recurrence_next
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (j : ℕ) : A (j + 2) =
      (2 * ((j : ℝ) + 2) * A (j + 1) + 3 * j * A j) / (j + 2) := by
  apply eq_div_of_mul_eq (by positivity)
  rw [mul_comm]
  exact a005773Recurrence_succ hrec j

/-- Two consecutive terms of the sequence are positive. -/
private lemma a005773Recurrence_pos (h0 : A 0 = 1) (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) : 0 < A n ∧ 0 < A (n + 1) := by
  induction n with
  | zero => simp [h0, h1]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h := a005773Recurrence_succ hrec n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith [mul_pos (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 2)) ih.2,
      mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * (n : ℝ)) ih.1.le]

/-- The two-sided bound `6n / (2n + 1) ≤ A (n + 1) / A n ≤ 3 (2n + 1) / (2 (n + 1))`, with the
denominators cleared. -/
private lemma a005773Recurrence_ratio_mem (h0 : A 0 = 1) (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) :
    6 * (n : ℝ) * A n ≤ (2 * n + 1) * A (n + 1) ∧
      2 * ((n : ℝ) + 1) * A (n + 1) ≤ 3 * (2 * n + 1) * A n := by
  induction n with
  | zero => norm_num [h0, h1]
  | succ n ih =>
    obtain ⟨hlo, hhi⟩ := ih
    have h := a005773Recurrence_succ hrec n
    have ha := (a005773Recurrence_pos h0 h1 hrec n).1
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    -- The upper bound at `n`, weakened to `A (n + 1) / A n ≤ φ (n + 1)`.
    have hhi' : 2 * ((n : ℝ) + 2) * A (n + 1) ≤ 3 * (2 * n + 3) * A n := by
      nlinarith [mul_le_mul_of_nonneg_left hhi (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2)]
    push_cast
    rw [show n + 1 + 1 = n + 2 from rfl]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hhi' hn]
    · linarith

/-- Coordinates for two neighboring terms in the cone given by the ratio bounds. -/
private lemma a005773Recurrence_coordinates (h0 : A 0 = 1) (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (m : ℕ) : ∃ l u : ℝ, 0 ≤ l ∧ 0 ≤ u ∧
      A m = 2 * ((m : ℝ) + 1) * l + (2 * m + 1) * u ∧
      A (m + 1) = 3 * (2 * (m : ℝ) + 1) * l + 6 * m * u := by
  obtain ⟨hlo, hhi⟩ := a005773Recurrence_ratio_mem h0 h1 hrec m
  refine ⟨((2 * m + 1) * A (m + 1) - 6 * m * A m) / 3,
    (3 * (2 * m + 1) * A m - 2 * (m + 1) * A (m + 1)) / 3,
    div_nonneg (sub_nonneg.mpr hlo) (by norm_num),
    div_nonneg (sub_nonneg.mpr hhi) (by norm_num), ?_, ?_⟩ <;> ring

/-- **Ratio bounds for the A005773 recurrence.**
Let $(A_n)_{n \ge 0}$ be a sequence of real numbers with $A_0 = A_1 = 1$ and
$(n+1) A_{n+1} = 2(n+1) A_n + 3(n-1) A_{n-1}$ for every $n \ge 1$. Write
$x_n = A_{n+1}/A_n$ and $\varphi_n = 3(2n+1)/(2(n+1))$. Then for every $n \ge 0$ we have
$x_n \le \varphi_n$ and
$$\frac{x_{n+1}}{x_n} \ge \frac{2(3n^2+6n+2)}{(n+2)(2n+1)\,\varphi_n}.$$

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
Sequence*, INTEGERS 25 (2025), Article A100, Lemma 1. -/
public theorem a005773Recurrence_ratio_bounds (A : ℕ → ℝ) (h0 : A 0 = 1) (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) :
    A (n + 1) / A n ≤ 3 * (2 * n + 1) / (2 * (n + 1)) ∧
      2 * (3 * (n : ℝ) ^ 2 + 6 * n + 2) /
          ((n + 2) * (2 * n + 1) * (3 * (2 * n + 1) / (2 * (n + 1))))
        ≤ (A (n + 2) / A (n + 1)) / (A (n + 1) / A n) := by
  obtain ⟨ha, hb⟩ := a005773Recurrence_pos h0 h1 hrec n
  have hc : 0 < A (n + 2) := (a005773Recurrence_pos h0 h1 hrec (n + 1)).2
  have hhi := (a005773Recurrence_ratio_mem h0 h1 hrec n).2
  have h := a005773Recurrence_succ hrec n
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  constructor
  · rw [div_le_div_iff₀ ha (by positivity)]
    linarith
  · have hφ : 2 * (3 * (n : ℝ) ^ 2 + 6 * n + 2) /
        ((n + 2) * (2 * n + 1) * (3 * (2 * n + 1) / (2 * (n + 1)))) =
        4 * ((n : ℝ) + 1) * (3 * n ^ 2 + 6 * n + 2) / (3 * (n + 2) * (2 * n + 1) ^ 2) := by
      field_simp
      ring
    -- Cleared of denominators, the difference of the two sides factors.
    have hfactor : A (n + 2) * A n * (3 * ((n : ℝ) + 2) * (2 * n + 1) ^ 2) -
        4 * ((n : ℝ) + 1) * (3 * n ^ 2 + 6 * n + 2) * (A (n + 1) * A (n + 1)) =
        (3 * (2 * n + 1) * A n - 2 * ((n : ℝ) + 1) * A (n + 1)) *
          (3 * n * (2 * n + 1) * A n + 2 * (3 * n ^ 2 + 6 * n + 2) * A (n + 1)) := by
      linear_combination (3 * (2 * (n : ℝ) + 1) ^ 2 * A n) * h
    have hnonneg : 0 ≤ (3 * (2 * n + 1) * A n - 2 * ((n : ℝ) + 1) * A (n + 1)) *
        (3 * n * (2 * n + 1) * A n + 2 * (3 * n ^ 2 + 6 * n + 2) * A (n + 1)) :=
      mul_nonneg (by linarith) (by positivity)
    rw [hφ, div_div_div_eq, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith

/-- **The third differences of A005773 are log-convex and log-balanced.**
Let $(A_n)_{n \ge 0}$ be a sequence of real numbers with $A_0 = A_1 = 1$ and
$(n+1) A_{n+1} = 2(n+1) A_n + 3(n-1) A_{n-1}$ for every $n \ge 1$, and write
$z_n = \Delta^3 A_n = A_{n+3} - 3A_{n+2} + 3A_{n+1} - A_n$. Then $z_n^2 \le z_{n-1} z_{n+1}$
for every $n \ge 3$, and
$$\frac{z_{n-1}}{(n-1)!} \cdot \frac{z_{n+1}}{(n+1)!} \le \left(\frac{z_n}{n!}\right)^2$$
for every $n \ge 4$. That is, $(\Delta^3 A_n)_{n \ge 2}$ is log-convex and
$(z_n / n!)_{n \ge 3}$ is log-concave, so $(\Delta^3 A_n)_{n \ge 3}$ is log-balanced.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
Sequence*, INTEGERS 25 (2025), Article A100, Theorem 2. -/
public theorem a005773Recurrence_thirdDiff_logConvex_logBalanced (A : ℕ → ℝ)
    (h0 : A 0 = 1) (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1)) :
    let D₃ : ℕ → ℝ := fun m => A (m + 3) - 3 * A (m + 2) + 3 * A (m + 1) - A m
    (∀ n, 3 ≤ n → D₃ n ^ 2 ≤ D₃ (n - 1) * D₃ (n + 1)) ∧
      ∀ n, 4 ≤ n →
        D₃ (n - 1) / (n - 1).factorial * (D₃ (n + 1) / (n + 1).factorial) ≤
          (D₃ n / n.factorial) ^ 2 := by
  intro z
  have step := a005773Recurrence_next hrec
  -- For n = k + 4 use the ratio bounds two indices before the center.
  have bounds (k : ℕ) :
      z (k + 4) ^ 2 ≤ z (k + 3) * z (k + 5) ∧
      ((k : ℝ) + 4) * (z (k + 3) * z (k + 5)) ≤ (k + 5) * z (k + 4) ^ 2 := by
    obtain ⟨l, u, hl, hu, ha, hb⟩ := a005773Recurrence_coordinates h0 h1 hrec (k + 2)
    dsimp only [z]
    rw [step (k + 6), step (k + 5), step (k + 4), step (k + 3), step (k + 2), ha, hb]
    push_cast
    -- Both product differences now have nonnegative coefficients in k, l, and u.
    constructor <;> apply sub_nonneg.mp <;> field_simp <;> ring_nf <;> positivity
  constructor
  · intro n hn
    rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn'
    · -- At the first index the inequality is 25² ≤ 9 · 71.
      dsimp only [z]
      rw [step 5, step 4, step 3, step 2, step 1, step 0, h0, h1]
      norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      exact (bounds k).1
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    change z (k + 3) / (k + 3).factorial * (z (k + 5) / (k + 5).factorial) ≤
      (z (k + 4) / (k + 4).factorial) ^ 2
    have hf : (0 : ℝ) < (k + 3).factorial := by exact_mod_cast Nat.factorial_pos _
    rw [Nat.factorial_succ (k + 4), Nat.factorial_succ (k + 3)]
    push_cast
    field_simp
    linarith only [(bounds k).2]

/-- **Log-concave weighted sequences built from A005773.**
Let $(A_n)_{n \ge 0}$ be a sequence of real numbers with $A_0 = A_1 = 1$ and
$(n+1) A_{n+1} = 2(n+1) A_n + 3(n-1) A_{n-1}$ for every $n \ge 1$, and write
$\Delta A_n = A_{n+1} - A_n$ and $\Delta^2 A_n = A_{n+2} - 2A_{n+1} + A_n$. Then for every
$n \ge 2$, each of the four sequences $z_m = m A_m$, $z_m = (m+1) A_{m+1} - m A_m$,
$z_m = m\,\Delta A_m$ and $z_m = m\,\Delta^2 A_m$ satisfies $z_{n-1} z_{n+1} \le z_n^2$. That
is, these four sequences, indexed from $m = 1$, are log-concave.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
Sequence*, INTEGERS 25 (2025), Article A100, Theorem 3. -/
public theorem a005773Recurrence_weighted_logConcave (A : ℕ → ℝ) (h0 : A 0 = 1)
    (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) (hn : 2 ≤ n) :
    let W : ℕ → ℝ := fun m => m * A m
    let V : ℕ → ℝ := fun m => (m + 1 : ℕ) * A (m + 1) - m * A m
    let U : ℕ → ℝ := fun m => m * (A (m + 1) - A m)
    let T : ℕ → ℝ := fun m => m * (A (m + 2) - 2 * A (m + 1) + A m)
    W (n - 1) * W (n + 1) ≤ W n ^ 2 ∧ V (n - 1) * V (n + 1) ≤ V n ^ 2 ∧
      U (n - 1) * U (n + 1) ≤ U n ^ 2 ∧ T (n - 1) * T (n + 1) ≤ T n ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨lo, hi, hl, hu, ha, hb⟩ := a005773Recurrence_coordinates h0 h1 hrec (k + 1)
  have step := a005773Recurrence_next hrec
  -- Eliminate the next three terms. After clearing positive denominators, each difference
  -- of products has nonnegative coefficients in k, lo, and hi.
  dsimp only
  rw [show k + 2 - 1 = k + 1 by omega, step (k + 3), step (k + 2), step (k + 1), ha, hb]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply sub_nonneg.mp <;> field_simp <;> ring_nf <;> positivity

/-- **The first and second differences of A005773 are log-balanced.**
Let $(A_n)_{n \ge 0}$ be a sequence of real numbers with $A_0 = A_1 = 1$ and
$(n+1) A_{n+1} = 2(n+1) A_n + 3(n-1) A_{n-1}$ for every $n \ge 1$, and write
$\Delta A_n = A_{n+1} - A_n$ and $\Delta^2 A_n = A_{n+2} - 2A_{n+1} + A_n$. Then for every
$n \ge 4$, each of the sequences $z = \Delta A$ and $z = \Delta^2 A$ satisfies
$z_n^2 \le z_{n-1} z_{n+1}$ and
$$\frac{z_{n-1}}{(n-1)!} \cdot \frac{z_{n+1}}{(n+1)!} \le \left(\frac{z_n}{n!}\right)^2.$$
That is, $(\Delta A_n)_{n \ge 3}$ and $(\Delta^2 A_n)_{n \ge 3}$ are log-balanced: log-convex, with
$(z_n / n!)_{n \ge 3}$ log-concave.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
Sequence*, INTEGERS 25 (2025), Article A100, Theorem 1. -/
public theorem a005773Recurrence_diff_logBalanced (A : ℕ → ℝ) (h0 : A 0 = 1)
    (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) (hn : 4 ≤ n) :
    let D₁ : ℕ → ℝ := fun m => A (m + 1) - A m
    let D₂ : ℕ → ℝ := fun m => A (m + 2) - 2 * A (m + 1) + A m
    (D₁ n ^ 2 ≤ D₁ (n - 1) * D₁ (n + 1) ∧
        D₁ (n - 1) / (n - 1).factorial * (D₁ (n + 1) / (n + 1).factorial) ≤
          (D₁ n / n.factorial) ^ 2) ∧
      D₂ n ^ 2 ≤ D₂ (n - 1) * D₂ (n + 1) ∧
        D₂ (n - 1) / (n - 1).factorial * (D₂ (n + 1) / (n + 1).factorial) ≤
          (D₂ n / n.factorial) ^ 2 := by
  intro D₁ D₂
  have step := a005773Recurrence_next hrec
  have bounds (k : ℕ) :
      D₁ (k + 4) ^ 2 ≤ D₁ (k + 3) * D₁ (k + 5) ∧
        ((k : ℝ) + 4) * (D₁ (k + 3) * D₁ (k + 5)) ≤ ((k : ℝ) + 5) * D₁ (k + 4) ^ 2 ∧
        D₂ (k + 4) ^ 2 ≤ D₂ (k + 3) * D₂ (k + 5) ∧
        ((k : ℝ) + 4) * (D₂ (k + 3) * D₂ (k + 5)) ≤ ((k : ℝ) + 5) * D₂ (k + 4) ^ 2 := by
    obtain ⟨l, u, hl, hu, ha, hb⟩ := a005773Recurrence_coordinates h0 h1 hrec (k + 2)
    dsimp only [D₁, D₂]
    rw [step (k + 5), step (k + 4), step (k + 3), step (k + 2), ha, hb]
    push_cast
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply sub_nonneg.mp <;> field_simp <;> ring_nf <;> positivity
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hf : (0 : ℝ) < (k + 3).factorial := by exact_mod_cast Nat.factorial_pos _
  refine ⟨⟨(bounds k).1, ?_⟩, (bounds k).2.2.1, ?_⟩
  · change D₁ (k + 3) / (k + 3).factorial * (D₁ (k + 5) / (k + 5).factorial) ≤
      (D₁ (k + 4) / (k + 4).factorial) ^ 2
    rw [Nat.factorial_succ (k + 4), Nat.factorial_succ (k + 3)]
    push_cast
    field_simp
    linarith only [(bounds k).2.1]
  · change D₂ (k + 3) / (k + 3).factorial * (D₂ (k + 5) / (k + 5).factorial) ≤
      (D₂ (k + 4) / (k + 4).factorial) ^ 2
    rw [Nat.factorial_succ (k + 4), Nat.factorial_succ (k + 3)]
    push_cast
    field_simp
    linarith only [(bounds k).2.2.2]

/-- **Log-convexity of $(n A_n)^n$ for A005773.**
Let $(A_n)_{n \ge 0}$ be a sequence of real numbers with $A_0 = A_1 = 1$ and
$(n+1) A_{n+1} = 2(n+1) A_n + 3(n-1) A_{n-1}$ for every $n \ge 1$, and let
$z_m = (m A_m)^m$. Then $z_n^2 \le z_{n-1} z_{n+1}$ for every $n \ge 2$; that is, the sequence
$(n^n A_n^n)_{n \ge 1}$ is log-convex.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to a Linear Recurrence
Sequence*, INTEGERS 25 (2025), Article A100, Theorem 4. -/
public theorem a005773Recurrence_pow_logConvex (A : ℕ → ℝ) (h0 : A 0 = 1)
    (h1 : A 1 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1) * A (n + 1) = 2 * ((n : ℝ) + 1) * A n + 3 * ((n : ℝ) - 1) * A (n - 1))
    (n : ℕ) (hn : 2 ≤ n) :
    let z : ℕ → ℝ := fun m => ((m : ℝ) * A m) ^ m
    z n ^ 2 ≤ z (n - 1) * z (n + 1) := by
  obtain _ | k := n
  · omega
  have hk : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨ha, hb⟩ := a005773Recurrence_pos h0 h1 hrec k
  have hc : 0 < A (k + 2) := (a005773Recurrence_pos h0 h1 hrec (k + 1)).2
  have hinc : A (k + 1) ≤ A (k + 2) := by
    apply le_of_mul_le_mul_left (a := (k : ℝ) + 2) ?_ (by positivity)
    nlinarith only [a005773Recurrence_succ hrec k, mul_pos (by positivity : 0 < (k : ℝ) + 2) hb,
      mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3) hk) ha]
  -- The lower bound on the quotient of successive ratios is at least one.
  have hconv : A (k + 1) ^ 2 ≤ A k * A (k + 2) := by
    suffices h : A (k + 1) / A k ≤ A (k + 2) / A (k + 1) by
      simpa only [sq, mul_comm] using (div_le_div_iff₀ ha hb).mp h
    apply (one_le_div₀ (div_pos hb ha)).mp
    refine le_trans ?_ (a005773Recurrence_ratio_bounds A h0 h1 hrec k).2
    field_simp
    linarith only [hk]
  -- At the midpoint, convexity of x log x handles the index factor.
  have hmid := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr hk.le)
    (Set.mem_Ici.mpr (by positivity : 0 ≤ (k : ℝ) + 2))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  rw [show (1 / 2 : ℝ) * k + 1 / 2 * (k + 2) = k + 1 by ring] at hmid
  have hlog := Real.log_le_log (sq_pos_of_pos hb) hconv
  rw [Real.log_pow, Real.log_mul ha.ne' hc.ne', Nat.cast_ofNat] at hlog
  -- Weight the log-convexity inequality for A by k and use monotonicity for the two
  -- remaining copies of log (A (k + 1)).
  dsimp only
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    show k + 1 + 1 = k + 2 from rfl]
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_pow, Real.log_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  linarith only [hmid, mul_le_mul_of_nonneg_left hlog hk.le, Real.log_le_log hb hinc]

end

end MetaMathlibExt
