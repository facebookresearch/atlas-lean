/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Complete exponential autonomous functions

Source: José Luis López, *Exponential Autonomous Functions*:
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Orozco/orozco5.tex>.
-/

open scoped BigOperators

@[expose] public section

namespace MetaMathlibExt

/-- **Complete Bell polynomials.** For a sequence $x = (x_0, x_1, x_2, \dots)$ of complex numbers,
the complete Bell polynomials $B_n(x)$ are defined by $B_0(x) = 1$ and, for every $m \ge 0$,
$B_{m+1}(x) = \sum_{i=0}^{m} \binom{m}{i} B_{m-i}(x) \, x_i$.

Writing $x_i = y_{i+1}$, this is the usual recurrence for $B_{m+1}(y_1, \dots, y_{m+1})$.

Source: statement `jis_4e6064ed86b521df4a4febe5` (concept `jis_sem_2f450d618ad4cc4cadb7505f`). -/
noncomputable def completeBellPolynomial (n : Nat) (x : Nat → Complex) : Complex :=
  Nat.strongRecOn (motive := fun _ => (Nat → Complex) → Complex) n
    (fun m ih x =>
      match m with
      | 0 => 1
      | m + 1 =>
        ∑ i ∈ Finset.range (m + 1),
          (m.choose i : Complex) * ih (m - i) (by omega) x * x i) x

@[simp]
theorem completeBellPolynomial_zero (x : ℕ → ℂ) : completeBellPolynomial 0 x = 1 := by
  rw [completeBellPolynomial, Nat.strongRecOn_eq]

@[simp]
theorem completeBellPolynomial_one (x : ℕ → ℂ) : completeBellPolynomial 1 x = x 0 := by
  rw [completeBellPolynomial, Nat.strongRecOn_eq]
  simp [Nat.strongRecOn_eq]

@[simp]
theorem completeBellPolynomial_two (x : ℕ → ℂ) :
    completeBellPolynomial 2 x = x 0 ^ 2 + x 1 := by
  rw [completeBellPolynomial, Nat.strongRecOn_eq]
  norm_num [Finset.sum_range_succ, pow_two]
  rw [Nat.strongRecOn_eq, Nat.strongRecOn_eq]
  ring_nf
  rw [Nat.strongRecOn_eq]
  simp only [one_mul]

/-- **Complete exponential autonomous functions.** Let $k \ge 1$, $a \in \mathbb{C}$ and
$x_0, \dots, x_{k-1} \in \mathbb{C}$. The complete exponential autonomous function of order $k$
with parameter $a$ and variables $x$ is the sequence $f_0, f_1, f_2, \dots$ of complex numbers
given by $f_n = x_n$ for $n < k$, $f_k = a e^{x_0}$, and $f_n = a e^{x_0} B_{n-k}(y)$ for
$n > k$, where $B_{n-k}$ is the complete Bell polynomial and $y$ is the sequence with
$y_i = f_{i+1}$ (so only $f_1, \dots, f_{n-k}$ enter).

Source: statement `jis_4e6064ed86b521df4a4febe5` (concept `jis_sem_2f450d618ad4cc4cadb7505f`). -/
noncomputable def completeExponentialAutonomousFunction (k : Nat) (hk : 0 < k)
    (a : Complex) (x : Fin k → Complex) : Nat → Complex :=
  fun N =>
    Nat.strongRecOn (motive := fun _ => Complex) N (fun n ih =>
      if h : n < k then x ⟨n, h⟩
      else if _h2 : n = k then a * Complex.exp (x ⟨0, hk⟩)
      else
        a * Complex.exp (x ⟨0, hk⟩) *
          completeBellPolynomial (n - k) (fun i =>
            if h3 : i + 1 < n then ih (i + 1) h3 else 0))

end MetaMathlibExt
