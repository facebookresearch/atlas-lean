/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Digits of p-adic integers

This file defines the digits of a p-adic integer from consecutive `PadicInt.appr` values and
proves the one-step and finite-sum reconstruction formulas.
-/

@[expose] public section

set_option autoImplicit false

namespace PadicInt

variable {p : Nat} [hp : Fact p.Prime]

/-- **Digits of a p-adic integer.** Let $p$ be a prime and $a \in \mathbb{Z}_p$, and for each
$n \ge 0$ let $a_n$ be the unique natural number with $a_n < p^n$ and
$a \equiv a_n \pmod{p^n \mathbb{Z}_p}$. The $n$-th $p$-adic digit of $a$ is the natural number
$(a_{n+1} - a_n)/p^n$.

Since $a_n \le a_{n+1}$ and $p^n$ divides $a_{n+1} - a_n$, this quotient is exact. -/
noncomputable def padicDigit (a : ℤ_[p]) (n : Nat) : Nat :=
  (a.appr (n + 1) - a.appr n) / p ^ n

/-- **p-adic digits are less than p.** Let $p$ be a prime and $a \in \mathbb{Z}_p$. For every
$n \ge 0$, the $n$-th $p$-adic digit of $a$ is strictly less than $p$. -/
theorem padicDigit_lt (a : ℤ_[p]) (n : Nat) : padicDigit a n < p := by
  unfold padicDigit
  obtain ⟨k, hk⟩ := dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n)
  rw [hk, Nat.mul_div_cancel_left _
    (pos_of_ne_zero (pow_ne_zero n (Nat.Prime.pos hp.out).ne'))]
  have h_sub_lt : a.appr (n + 1) - a.appr n < p ^ (n + 1) :=
    lt_of_le_of_lt (Nat.sub_le _ _) (appr_lt a (n + 1))
  rw [hk, pow_succ] at h_sub_lt
  exact Nat.lt_of_mul_lt_mul_left h_sub_lt

/-- **p-adic expansion.** Let $p$ be a prime and $a \in \mathbb{Z}_p$. The $p$-adic expansion of
$a$ is the sequence whose $n$-th term is the $n$-th $p$-adic digit of $a$, viewed as an element of
$\{0, 1, \dots, p - 1\}$. -/
noncomputable def padicExpansion (a : ℤ_[p]) (n : Nat) : Fin p :=
  ⟨padicDigit a n, padicDigit_lt a n⟩

/-- **Terms of the p-adic expansion are the digits.** Let $p$ be a prime and $a \in \mathbb{Z}_p$.
For every $n \ge 0$, the $n$-th term of the $p$-adic expansion of $a$, read as a natural number,
is the $n$-th $p$-adic digit of $a$. -/
@[simp] theorem padicExpansion_val (a : ℤ_[p]) (n : Nat) :
    (padicExpansion a n).val = padicDigit a n := rfl

/-- **p-adic digits measure the gaps between approximations.** Let $p$ be a prime and
$a \in \mathbb{Z}_p$, and for each $n \ge 0$ let $a_n$ be the unique natural number with
$a_n < p^n$ and $a \equiv a_n \pmod{p^n \mathbb{Z}_p}$. For every $n \ge 0$, the $n$-th $p$-adic
digit $d_n$ of $a$ satisfies $d_n p^n = a_{n+1} - a_n$.

Here $a_n \le a_{n+1}$, so the difference is an honest natural number. -/
theorem padicDigit_mul_pow (a : ℤ_[p]) (n : Nat) :
    padicDigit a n * p ^ n = a.appr (n + 1) - a.appr n := by
  unfold padicDigit
  exact Nat.div_mul_cancel (dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n))

/-- **One-step reconstruction from p-adic digits.** Let $p$ be a prime and $a \in \mathbb{Z}_p$,
and for each $n \ge 0$ let $a_n$ be the unique natural number with $a_n < p^n$ and
$a \equiv a_n \pmod{p^n \mathbb{Z}_p}$. For every $n \ge 0$, the $n$-th $p$-adic
digit $d_n$ of $a$ satisfies $a_{n+1} = a_n + d_n p^n$. -/
theorem appr_succ_eq (a : ℤ_[p]) (n : Nat) :
    a.appr (n + 1) = a.appr n + padicDigit a n * p ^ n := by
  have hle : a.appr n ≤ a.appr (n + 1) := appr_mono a (Nat.le_succ n)
  have h := padicDigit_mul_pow a n
  omega

/-- **One-step reconstruction from the p-adic expansion.** Let $p$ be a prime and
$a \in \mathbb{Z}_p$, and for each $n \ge 0$ let $a_n$ be the unique natural number with
$a_n < p^n$ and $a \equiv a_n \pmod{p^n \mathbb{Z}_p}$. For every $n \ge 0$,
$a_{n+1} = a_n + e_n p^n$, where $e_n$ is the $n$-th term of the $p$-adic expansion of $a$, read as
a natural number. -/
theorem appr_succ_eq_val (a : ℤ_[p]) (n : Nat) :
    a.appr (n + 1) = a.appr n + (padicExpansion a n).val * p ^ n := by
  simpa using appr_succ_eq a n

/-- **Approximations as sums of p-adic digits.** Let $p$ be a prime and $a \in \mathbb{Z}_p$, and
for each $n \ge 0$ let $a_n$ be the unique natural number with $a_n < p^n$ and
$a \equiv a_n \pmod{p^n \mathbb{Z}_p}$. For every $n \ge 0$,
$a_n = \sum_{k=0}^{n-1} d_k p^k$, where $d_k$ is the $k$-th $p$-adic digit of $a$. -/
theorem appr_eq_sum_padicDigit (a : ℤ_[p]) (n : Nat) :
    a.appr n = ∑ k ∈ Finset.range n, padicDigit a k * p ^ k := by
  induction n with
  | zero => simp [appr]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, appr_succ_eq]

/-- **Approximations as truncations of the p-adic expansion.** Let $p$ be a prime and
$a \in \mathbb{Z}_p$, and for each $n \ge 0$ let $a_n$ be the unique natural number with
$a_n < p^n$ and $a \equiv a_n \pmod{p^n \mathbb{Z}_p}$. For every $n \ge 0$,
$a_n = \sum_{k=0}^{n-1} e_k p^k$, where $e_k$ is the $k$-th term of the $p$-adic expansion of $a$,
read as a natural number. -/
theorem appr_eq_sum_expansion_val (a : ℤ_[p]) (n : Nat) :
    a.appr n = ∑ k ∈ Finset.range n, (padicExpansion a k).val * p ^ k := by
  simpa using appr_eq_sum_padicDigit a n

end PadicInt
