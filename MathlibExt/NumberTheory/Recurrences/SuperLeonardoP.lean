/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.NumberTheory.Recurrences.HonsbergerFibonacciP

/-! # Supergeneralized Leonardo p-numbers

In the homogeneous recurrence, each term is a linear combination of the initial values
with Fibonacci p-numbers as coefficients.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Supergeneralized Leonardo p-numbers.** For natural numbers $p$ and $k$ and a real sequence
$x = (x_n)_{n \in \mathbb{N}}$, the supergeneralized Leonardo $p$-numbers are the real numbers
$\mathcal{L}_{p,k,x}(n)$, $n \in \mathbb{N}$, given by $\mathcal{L}_{p,k,x}(n) = x_n$ for
$n \le p$ and $\mathcal{L}_{p,k,x}(n) = \mathcal{L}_{p,k,x}(n-1) + \mathcal{L}_{p,k,x}(n-p-1) + k$
for $n > p$. Only the initial values $x_0, \dots, x_p$ are used.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Definition 1. -/
noncomputable def superLeonardoP (p k : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  if _h : n ≤ p then x n
  else superLeonardoP p k x (n - 1) + superLeonardoP p k x (n - p - 1) + k
termination_by n
decreasing_by all_goals omega

/-- **Initial values of the supergeneralized Leonardo p-numbers.** For all natural numbers $p$,
$k$ and $n$ with $n \le p$ and every real sequence $x$, the supergeneralized Leonardo $p$-number
$\mathcal{L}_{p,k,x}(n)$ equals $x_n$.

Source: Schütz and Kelly, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Definition 1. -/
theorem superLeonardoP_of_le (p k : ℕ) (x : ℕ → ℝ) {n : ℕ} (hn : n ≤ p) :
    superLeonardoP p k x n = x n := by
  rw [superLeonardoP]; simp [hn]

/-- **Recurrence for the supergeneralized Leonardo p-numbers.** For all natural numbers $p$, $k$
and $n$ with $n > p$ and every real sequence $x$, the supergeneralized Leonardo $p$-numbers
$\mathcal{L}_{p,k,x}$ satisfy
$\mathcal{L}_{p,k,x}(n) = \mathcal{L}_{p,k,x}(n-1) + \mathcal{L}_{p,k,x}(n-p-1) + k$.

Source: Schütz and Kelly, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Definition 1. -/
theorem superLeonardoP_of_lt (p k : ℕ) (x : ℕ → ℝ) {n : ℕ} (hn : p < n) :
    superLeonardoP p k x n =
      superLeonardoP p k x (n - 1) + superLeonardoP p k x (n - p - 1) + k := by
  rw [superLeonardoP]; simp [show ¬n ≤ p by omega]

private theorem fibonacciP_succ_of_pos (p r : ℕ) (hr : 0 < r) :
    fibonacciP p (r + 1) = fibonacciP p r + fibonacciP p (r - p) := by
  by_cases h : r + 1 ≤ p
  · simp [fibonacciP_eq_one p (r + 1) (by omega) h, fibonacciP_eq_one p r hr (by omega),
      Nat.sub_eq_zero_of_le (show r ≤ p by omega)]
  · rw [fibonacciP, ite_eq_right h]

-- Express a term using the window starting at b. Shifting the window by one
-- combines its two endpoint contributions by the Fibonacci recurrence.
private theorem homogeneous_window (p : ℕ) (hp : 1 ≤ p) (u : ℕ → ℝ)
    (hu : ∀ b, u (b + p + 1) = u (b + p) + u b) (m b : ℕ) :
    u (b + p + m) = (fibonacciP p (m + 1) : ℝ) * u (b + p) +
      ∑ i ∈ Finset.range p, (fibonacciP p (m - i) : ℝ) * u (b + i) := by
  induction m generalizing b with
  | zero => simp [fibonacciP_eq_one p 1 le_rfl hp]
  | succ m ih =>
    let w (i : ℕ) := (fibonacciP p (m + 1 - i) : ℝ) * u (b + i)
    have shift : (∑ i ∈ Finset.range p, w (i + 1)) + w 0 =
        (∑ i ∈ Finset.range p, w i) + w p := by
      rw [← Finset.sum_range_succ', Finset.sum_range_succ]
    rw [show b + p + (m + 1) = (b + 1) + p + m by omega, ih (b + 1),
      show b + 1 + p = b + p + 1 by omega, hu, mul_add]
    calc
      _ = (fibonacciP p (m + 1) : ℝ) * u (b + p) +
          ((∑ i ∈ Finset.range p, w (i + 1)) + w 0) := by
        simp only [w, Nat.add_sub_add_right, Nat.sub_zero, Nat.add_zero, Nat.add_right_comm b 1]
        ac_rfl
      _ = _ := by
        rw [shift, fibonacciP_succ_of_pos p (m + 1) (by omega), Nat.cast_add, add_mul]
        dsimp [w]
        ac_rfl

/-- **Homogeneous supergeneralized Leonardo p-numbers via Fibonacci p-numbers.** For all
natural numbers $p \ge 1$ and $n$ and every real sequence $x$, the supergeneralized Leonardo
$p$-numbers $\mathcal{L}_{p,0,x}$ with $k = 0$ satisfy $\mathcal{L}_{p,0,x}(n) = x_n$ if
$n \le p$, and if $n > p$, with $F_p$ denoting the Fibonacci $p$-numbers,
$$\mathcal{L}_{p,0,x}(n) = F_p(n-p+1)\,x_p + \sum_{i=0}^{\min(p-1,\,n-p-1)} F_p(n-p-i)\,x_i.$$

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Theorem 4. -/
theorem superLeonardoP_zero_eq (p : ℕ) (hp : 1 ≤ p) (x : ℕ → ℝ) (n : ℕ) :
    superLeonardoP p 0 x n =
      if n ≤ p then x n
      else (fibonacciP p (n - p + 1) : ℝ) * x p +
        ∑ i ∈ Finset.range (min (p - 1) (n - p - 1) + 1),
          (fibonacciP p (n - p - i) : ℝ) * x i := by
  split_ifs with hn
  · exact superLeonardoP_of_le p 0 x hn
  · have hrec (b : ℕ) : superLeonardoP p 0 x (b + p + 1) =
          superLeonardoP p 0 x (b + p) + superLeonardoP p 0 x b := by
      rw [superLeonardoP_of_lt p 0 x (by omega : p < b + p + 1)]
      simp [show b + p + 1 - p - 1 = b by omega]
    have h := homogeneous_window p hp (superLeonardoP p 0 x) hrec (n - p) 0
    simp only [Nat.zero_add, show p + (n - p) = n by omega,
      superLeonardoP_of_le p 0 x le_rfl] at h
    rw [h]
    congr 1
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono (by omega))
    · intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_range] at hi
      simp [show n - p - i = 0 by omega]
    · intro i hi
      have := Finset.mem_range.mp hi
      rw [superLeonardoP_of_le p 0 x (by omega)]

end

end MetaMathlibExt
