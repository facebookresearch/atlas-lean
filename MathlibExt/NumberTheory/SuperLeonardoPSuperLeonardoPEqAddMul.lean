/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.SuperLeonardoP
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-! # Reduction of supergeneralized Leonardo p-numbers to the homogeneous case

`superLeonardoP_eq_add_mul` writes each supergeneralized Leonardo `p`-number as its
homogeneous part plus a correction weight times the increment `k`.

Statements from Clemens Schütz and Kristian Kelly, *An Explicit Formula for
Supergeneralized Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025),
Article 25.8.2 (<https://cs.uwaterloo.ca/journals/JIS/VOL28/Schutz/schutz3.tex>).
-/

namespace MetaMathlibExt

@[expose] public section

-- The correction weight satisfies the same recurrence with unit forcing.
private theorem superLeonardoP_correction_rec (p n : ℕ) (hp : 1 ≤ p) (hn : p < n) :
    (if p < n then superLeonardoP p 1 (fun i => (i : ℝ) + 1) (n - (p + 1)) else 0)
      = (if p < n - 1 then superLeonardoP p 1 (fun i => (i : ℝ) + 1) (n - 1 - (p + 1))
          else 0)
        + (if p < n - p - 1
            then superLeonardoP p 1 (fun i => (i : ℝ) + 1) (n - p - 1 - (p + 1)) else 0)
        + 1 := by
  rw [ite_eq_left hn]
  by_cases h1 : p < n - 1
  · rw [ite_eq_left h1]
    by_cases h2 : p < n - p - 1
    · rw [ite_eq_left h2]
      have hm : p < n - (p + 1) := by omega
      rw [superLeonardoP_of_lt p 1 _ hm]
      have e1 : n - (p + 1) - 1 = n - 1 - (p + 1) := by omega
      have e2 : n - (p + 1) - p - 1 = n - p - 1 - (p + 1) := by omega
      rw [e1, e2, Nat.cast_one]
    · rw [ite_eq_right h2]
      have hm_le : n - (p + 1) ≤ p := by omega
      rw [superLeonardoP_of_le p 1 _ hm_le]
      have hm1_le : n - 1 - (p + 1) ≤ p := by omega
      rw [superLeonardoP_of_le p 1 _ hm1_le]
      have hsucc : n - (p + 1) = (n - 1 - (p + 1)) + 1 := by omega
      rw [hsucc]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
  · rw [ite_eq_right h1]
    have h2 : ¬p < n - p - 1 := by omega
    rw [ite_eq_right h2]
    have hm0 : n - (p + 1) = 0 := by omega
    rw [hm0, superLeonardoP_of_le p 1 _ (Nat.zero_le p)]
    simp

/-- **Reduction of supergeneralized Leonardo p-numbers to the homogeneous case.** Let $p \ge 1$
and $k$ be natural numbers, $x$ a real sequence, $y$ the real sequence $y_i = i + 1$, and write
$\mathcal{L}_{p,k,x}(n)$ for the supergeneralized Leonardo $p$-numbers. For every natural number
$n$, $\mathcal{L}_{p,k,x}(n) = \mathcal{L}_{p,0,x}(n)$ if $n \le p$, and
$\mathcal{L}_{p,k,x}(n) = \mathcal{L}_{p,0,x}(n) + \mathcal{L}_{p,1,y}(n-(p+1)) \cdot k$ if $n > p$.

The paper writes the correction term as $\max\{0, \mathcal{L}_{p,1,y}(n-(p+1))\} \cdot k$ with
$y = (1, \dots, p + 1)$ and sets $\mathcal{L} \le 0$ at negative indices, so the correction term
is $0$ for $n \le p$; for $n > p$ the $\max$ is redundant since $\mathcal{L}_{p,1,y}$ is positive.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Theorem 3. -/
public theorem superLeonardoP_eq_add_mul (p k : ℕ) (hp : 1 ≤ p) (x : ℕ → ℝ) (n : ℕ) :
    superLeonardoP p k x n =
      superLeonardoP p 0 x n +
        (if p < n then superLeonardoP p 1 (fun i => (i : ℝ) + 1) (n - (p + 1)) else 0) *
          k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : p < n
    · rw [superLeonardoP_of_lt p k x hn, superLeonardoP_of_lt p 0 x hn,
        ih (n - 1) (by omega), ih (n - p - 1) (by omega),
        superLeonardoP_correction_rec p n hp hn]
      ring
    · rw [ite_eq_right hn, superLeonardoP_of_le p k x (by omega),
        superLeonardoP_of_le p 0 x (by omega)]
      simp

end

end MetaMathlibExt
