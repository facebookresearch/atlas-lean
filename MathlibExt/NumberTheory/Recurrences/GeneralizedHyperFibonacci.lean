/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.Ring

/-! # Generalized hyper-Fibonacci numbers -/

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-- **Generalized $p$-Fibonacci sequence.** For integers $p$, $a$ and $b$, the generalized
Fibonacci sequence $(W_{p,n})_{n \ge 0}$ of integers is defined by $W_{p,0} = a$, $W_{p,1} = b$
and $W_{p,n} = p W_{p,n-1} + W_{p,n-2}$ for $n \ge 2$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, recurrence (1). -/
public def generalizedPFibonacci (p a b : ℤ) : ℕ → ℤ
  | 0 => a
  | 1 => b
  | n + 2 => p * generalizedPFibonacci p a b (n + 1) + generalizedPFibonacci p a b n

/-- **$p$-Fibonacci numbers as a Lucas sequence.** For every integer $p$, the generalized
Fibonacci sequence $W_{p,n}$ with initial values $a = 0$ and $b = 1$ (the $p$-Fibonacci numbers
$F_{p,n}$) is the Lucas sequence $U(p, -1)$: $W_{p,n} = U_n(p, -1)$ for every natural number $n$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, remark after recurrence (1) (`p`-Fibonacci
numbers `F_{p,n}`). -/
public theorem generalizedPFibonacci_zero_one (p : ℤ) (n : ℕ) :
    generalizedPFibonacci p 0 1 n = lucasU ⟨p, -1, by decide⟩ n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    simp only [generalizedPFibonacci, lucasU, ih1, ih2]
    ring

/-- **$p$-Lucas numbers as a companion Lucas sequence.** For every integer $p$, the generalized
Fibonacci sequence $W_{p,n}$ with initial values $a = 2$ and $b = p$ (the $p$-Lucas numbers
$L_{p,n}$) is the companion Lucas sequence $V(p, -1)$: $W_{p,n} = V_n(p, -1)$ for every natural
number $n$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, remark after recurrence (1) (`p`-Lucas numbers
`L_{p,n}`). -/
public theorem generalizedPFibonacci_two_p (p : ℤ) (n : ℕ) :
    generalizedPFibonacci p 2 p n = lucasV ⟨p, -1, by decide⟩ n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    simp only [generalizedPFibonacci, lucasV, ih1, ih2]
    ring

/-- **Generalized hyper-Fibonacci numbers.** Let $p, a, b$ be integers and let $W_{p,n}$ denote the
generalized Fibonacci sequence, with $W_{p,0} = a$, $W_{p,1} = b$ and
$W_{p,n+2} = p W_{p,n+1} + W_{p,n}$. The generalized hyper-Fibonacci numbers $W^{(r)}_{p,n}$, for
natural numbers $r$ and $n$, are the integers defined by $W^{(0)}_{p,n} = W_{p,n}$ and, for
$r \ge 1$, by $W^{(r)}_{p,n} = \sum_{k=0}^{n} p^{n-k} W^{(r-1)}_{p,k}$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, definition (2). -/
public def generalizedHyperFibonacci (p a b : ℤ) : ℕ → ℕ → ℤ
  | 0 => generalizedPFibonacci p a b
  | r + 1 => fun n =>
      ∑ k ∈ Finset.range (n + 1), p ^ (n - k) * generalizedHyperFibonacci p a b r k

/-- **Initial values of generalized hyper-Fibonacci numbers.** Let $p, a, b$ be integers and let
$W^{(r)}_{p,n}$ denote the generalized hyper-Fibonacci numbers. For every natural number $r$,
$W^{(r)}_{p,0} = a$ and $W^{(r)}_{p,1} = p \cdot a \cdot r + b$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, definition (2) (initial values). -/
public theorem generalizedHyperFibonacci_zero_one (p a b : ℤ) (r : ℕ) :
    generalizedHyperFibonacci p a b r 0 = a ∧
      generalizedHyperFibonacci p a b r 1 = p * a * r + b := by
  induction r with
  | zero => exact ⟨rfl, by simp [generalizedHyperFibonacci, generalizedPFibonacci]⟩
  | succ r ih =>
    refine ⟨?_, ?_⟩
    · simp [generalizedHyperFibonacci, ih.1]
    · simp only [generalizedHyperFibonacci, Finset.sum_range_succ, Finset.sum_range_zero,
        ih.1, ih.2]
      push_cast
      ring

/-- **Recurrence for generalized hyper-Fibonacci numbers.** Let $p, a, b$ be integers and let
$W^{(r)}_{p,n}$ denote the generalized hyper-Fibonacci numbers. For all natural numbers $r \ge 1$
and $n \ge 1$, $W^{(r)}_{p,n} = p W^{(r)}_{p,n-1} + W^{(r-1)}_{p,n}$.

The paper assumes $p \ge 1$, $a \ge 0$, and $b > 0$; the recurrence holds for arbitrary integer
parameters.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Lemma 5, equation (7), quoting Ait-Amrane et al.
(`jis-2026-26.2.5-lem-5`). -/
public theorem generalizedHyperFibonacci_succ_succ (p a b : ℤ) (r n : ℕ) :
    generalizedHyperFibonacci p a b (r + 1) (n + 1) =
      p * generalizedHyperFibonacci p a b (r + 1) n +
        generalizedHyperFibonacci p a b r (n + 1) := by
  simp only [generalizedHyperFibonacci]
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ', mul_assoc]

end

end MetaMathlibExt
