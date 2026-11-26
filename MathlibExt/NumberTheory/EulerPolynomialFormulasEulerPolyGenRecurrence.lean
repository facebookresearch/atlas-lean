/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.EulerPolynomialBinomialAverage
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Recurrence for Euler polynomials of order α

This module defines Euler numbers and polynomials of order α and proves their recurrence.

Source: Nouara Mokhtari, Rachid Boumahdi, and
Farid Bencherif, "Generalizations of Several Explicit
Formulas for Euler Polynomials", *INTEGERS* 25 (2025),
Article A65
(<https://math.colgate.edu/~integers/vol25.html>).
-/

set_option autoImplicit false

@[expose] public section

open Polynomial Finset

namespace MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

/-- **Fuel-bounded recurrence for the Euler numbers of order α.** Let $E_m(x)$ denote the Euler
polynomial. For a complex number $\alpha$, the complex numbers $a_\alpha(f, n)$, for natural
numbers $f$ (the fuel) and $n$, are defined by $a_\alpha(0, n) = 1$, $a_\alpha(f + 1, 0) = 1$
and $a_\alpha(f + 1, n + 1) = -\alpha \, a_\alpha(f, n) +
\frac{\alpha}{2} \sum_{k=0}^{n} \binom{n}{k} a_\alpha(f, k) \, E_{n-k}(0)$.

Whenever $n \le f$, $a_\alpha(f, n)$ equals the Euler number of order $\alpha$,
$E_n^{(\alpha)}(0)$. -/
noncomputable def eulerNumGenAux (α : ℂ) : ℕ → ℕ → ℂ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | fuel + 1, n + 1 =>
      -α * eulerNumGenAux α fuel n + (α / 2) *
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℂ) * eulerNumGenAux α fuel k *
            (((eulerPoly (n - k)).eval (0 : ℚ) : ℚ) : ℂ)

/-- **Euler numbers of order α.** Let $E_m(x)$ denote the Euler polynomial. For a complex number
$\alpha$, the Euler numbers of order $\alpha$ are the complex numbers $E_n^{(\alpha)}(0)$,
$n \ge 0$, defined by $E_0^{(\alpha)}(0) = 1$ and
$E_{n+1}^{(\alpha)}(0) = -\alpha E_n^{(\alpha)}(0) +
\frac{\alpha}{2} \sum_{k=0}^{n} \binom{n}{k} E_k^{(\alpha)}(0) \, E_{n-k}(0)$ for $n \ge 0$.

This is the coefficient recurrence of the generating function $(2/(e^t + 1))^\alpha$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Section 1 (generalized Euler
polynomials). -/
noncomputable def eulerNumGen (α : ℂ) (n : ℕ) : ℂ :=
  eulerNumGenAux α n n

/-- **Euler polynomials of order α.** For a complex number $\alpha$ and $n \ge 0$, let
$E_k^{(\alpha)}(0)$ denote the Euler numbers of order $\alpha$. The Euler polynomial of order
$\alpha$ is the complex polynomial
$E_n^{(\alpha)}(x) = \sum_{k=0}^{n} \binom{n}{k} E_k^{(\alpha)}(0) \, x^{n-k}$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Section 1 (generalized Euler
polynomials). -/
noncomputable def eulerPolyGen (α : ℂ) (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C ((Nat.choose n k : ℂ) * eulerNumGen α k) * X ^ (n - k)

private theorem aux_stable (α : ℂ) (n f : ℕ) (h : n ≤ f) :
    eulerNumGenAux α f n = eulerNumGen α n := by
  induction n using Nat.strong_induction_on generalizing f with
  | ind n ih =>
    cases n with
    | zero => cases f <;> rfl
    | succ n =>
      cases f with
      | zero => omega
      | succ f =>
        simp only [eulerNumGen, eulerNumGenAux]
        rw [ih n (by omega) f (by omega), ih n (by omega) n (by omega)]
        congr 2
        apply sum_congr rfl
        intro k hk
        have hk' : k ≤ n := mem_range_succ_iff.mp hk
        rw [ih k (by omega) f (by omega), ih k (by omega) n hk']

private theorem num_succ (α : ℂ) (n : ℕ) :
    eulerNumGen α (n + 1) = -α * eulerNumGen α n + (α / 2) *
      ∑ k ∈ range (n + 1), (n.choose k : ℂ) * eulerNumGen α k *
        (((eulerPoly (n - k)).eval (0 : ℚ) : ℚ) : ℂ) := by
  rw [eulerNumGen, eulerNumGenAux]
  congr 2
  apply sum_congr rfl
  intro k hk
  rw [aux_stable α k n (mem_range_succ_iff.mp hk)]

private theorem euler_zero : (eulerPoly 0).eval (0 : ℚ) = 1 := by
  norm_num [eulerPoly, Polynomial.bernoulli_one]

private theorem euler_sign (m : ℕ) (hm : 0 < m) :
    (-1 : ℂ) ^ (m + 1) * (((eulerPoly m).eval (0 : ℚ) : ℚ) : ℂ) =
      (((eulerPoly m).eval (0 : ℚ) : ℚ) : ℂ) := by
  rcases Nat.even_or_odd m with he | ho
  · have hb : _root_.bernoulli (m + 1) = 0 :=
      bernoulli_eq_zero_of_odd he.add_one (by omega)
    have hz : (eulerPoly m).eval (0 : ℚ) = 0 := by
      simp [eulerPoly, Polynomial.bernoulli_eval_zero, hb]
    simp [hz]
  · rw [ho.add_one.neg_one_pow, one_mul]

private theorem poly_coeff (α : ℂ) (n j : ℕ) :
    (eulerPolyGen α n).coeff j = (n.choose j : ℂ) * eulerNumGen α (n - j) := by
  simp only [eulerPolyGen, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hj : j ≤ n
  · rw [sum_eq_single (n - j)]
    · simp [Nat.sub_sub_self hj, Nat.choose_symm hj]
    · intro k hk hkj
      have hk' : k ≤ n := mem_range_succ_iff.mp hk
      have hne : j ≠ n - k := by omega
      simp [hne]
    · intro h
      exact (h (mem_range_succ_iff.mpr (by omega))).elim
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    apply sum_eq_zero
    intro k hk
    have hk' : k ≤ n := mem_range_succ_iff.mp hk
    simp [show j ≠ n - k by omega]

private theorem convolution (a b : ℕ → ℂ) (m j : ℕ) (hj : j ≤ m) :
    ∑ k ∈ range (m + 1), (m.choose k : ℂ) * b (m - k) *
        ((k.choose j : ℂ) * a (k - j)) =
      (m.choose j : ℂ) * ∑ r ∈ range (m - j + 1),
        ((m - j).choose r : ℂ) * a r * b (m - j - r) := by
  rw [show m + 1 = j + (m - j + 1) by omega, sum_range_add]
  have hz : ∑ k ∈ range j, (m.choose k : ℂ) * b (m - k) *
      ((k.choose j : ℂ) * a (k - j)) = 0 := by
    apply sum_eq_zero
    intro k hk
    rw [Nat.choose_eq_zero_of_lt (mem_range.mp hk)]
    simp
  rw [hz, zero_add, mul_sum]
  apply sum_congr rfl
  intro r _
  have hc : (m.choose (j + r) : ℂ) * ((j + r).choose j : ℂ) =
      (m.choose j : ℂ) * ((m - j).choose r : ℂ) := by
    exact_mod_cast (by simpa using (Nat.choose_mul (n := m) (k := j + r) (s := j) (by omega)))
  rw [show j + r - j = r by omega, show m - (j + r) = m - j - r by omega]
  calc
    _ = ((m.choose (j + r) : ℂ) * ((j + r).choose j : ℂ)) *
        (a r * b (m - j - r)) := by ring
    _ = _ := by rw [hc]; ring

private theorem poly_succ (α : ℂ) (m : ℕ) :
    eulerPolyGen α (m + 1) = X * eulerPolyGen α m - C α * eulerPolyGen α m +
      C (α / 2) * ∑ k ∈ range (m + 1),
        C ((m.choose k : ℂ) * (((eulerPoly (m - k)).eval (0 : ℚ) : ℚ) : ℂ)) *
          eulerPolyGen α k := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro j
  simp only [coeff_add, coeff_sub, coeff_C_mul, finsetSum_coeff]
  cases j with
  | zero =>
    simp only [coeff_X_mul_zero, poly_coeff]
    rw [convolution (eulerNumGen α)
      (fun r => (((eulerPoly r).eval (0 : ℚ) : ℚ) : ℂ)) m 0 (Nat.zero_le m)]
    simpa using num_succ α m
  | succ j =>
    rw [coeff_X_mul]
    simp only [poly_coeff]
    by_cases hj : j < m
    · rw [convolution (eulerNumGen α)
        (fun r => (((eulerPoly r).eval (0 : ℚ) : ℚ) : ℂ)) m (j + 1) (by omega)]
      rw [Nat.choose_succ_succ', Nat.cast_add]
      have hsub : m - j = (m - (j + 1)) + 1 := by omega
      rw [show m + 1 - (j + 1) = m - j by omega, hsub, num_succ]
      ring
    · have hs : ∑ k ∈ range (m + 1), (m.choose k : ℂ) *
          (((eulerPoly (m - k)).eval (0 : ℚ) : ℚ) : ℂ) *
          ((k.choose (j + 1) : ℂ) * eulerNumGen α (k - (j + 1))) = 0 := by
        apply sum_eq_zero
        intro k hk
        rw [Nat.choose_eq_zero_of_lt (n := k) (k := j + 1)
          (by have := mem_range_succ_iff.mp hk; omega)]
        simp
      rw [hs, Nat.choose_eq_zero_of_lt (n := m) (k := j + 1) (by omega)]
      simp only [Nat.cast_zero, zero_mul, mul_zero, sub_zero, add_zero]
      by_cases he : j = m
      · subst j
        simp
      · rw [Nat.choose_eq_zero_of_lt (n := m + 1) (k := j + 1) (by omega),
          Nat.choose_eq_zero_of_lt (n := m) (k := j) (by omega)]
        simp

/-- **Recurrence for Euler polynomials of order α.** Let $E_m(x)$ denote the Euler polynomial
and $E_m^{(\alpha)}(x)$ the Euler polynomial of order $\alpha$. For every complex number
$\alpha$ and every integer $n \ge 1$, as polynomials in $x$,
$E_n^{(\alpha)}(x) = (x - \alpha/2) \, E_{n-1}^{(\alpha)}(x) +
\frac{\alpha}{2} \sum_{k=0}^{n-2} \binom{n-1}{k} (-1)^{n-k} E_{n-1-k}(0) \, E_k^{(\alpha)}(x)$,
where the sum is empty when $n = 1$. The printed equation (21) of the source has $E_{n-k}(0)$
in place of $E_{n-1-k}(0)$; the index $n-1-k$ used here is the correct one.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Proposition 3.2. -/
public theorem eulerPolyGen_recurrence (α : ℂ) (n : ℕ)
    (hn : 1 ≤ n) :
    eulerPolyGen α n =
      (X - C (α / 2)) * eulerPolyGen α (n - 1) +
        C (α / 2) * ∑ k ∈ Finset.range (n - 1),
          C ((Nat.choose (n - 1) k : ℂ) * (-1) ^ (n - k) *
            (((eulerPoly (n - 1 - k)).eval (0 : ℚ) : ℚ) : ℂ)) *
            eulerPolyGen α k
    := by
  cases n with
  | zero => omega
  | succ m =>
    simp only [Nat.add_sub_cancel]
    have hs : ∑ k ∈ range m,
        C ((m.choose k : ℂ) * (-1) ^ (m + 1 - k) *
          (((eulerPoly (m - k)).eval (0 : ℚ) : ℚ) : ℂ)) * eulerPolyGen α k =
        ∑ k ∈ range m,
          C ((m.choose k : ℂ) * (((eulerPoly (m - k)).eval (0 : ℚ) : ℚ) : ℂ)) *
            eulerPolyGen α k := by
      apply sum_congr rfl
      intro k hk
      have hk' : k < m := mem_range.mp hk
      rw [show m + 1 - k = (m - k) + 1 by omega, mul_assoc,
        euler_sign (m - k) (by omega)]
    rw [hs, poly_succ, sum_range_succ]
    simp only [Nat.sub_self, Nat.choose_self, Nat.cast_one, euler_zero, Rat.cast_one,
      one_mul, C_1]
    have ha : C α = C (α / 2) + C (α / 2) := by
      rw [← C_add]
      congr 1
      ring
    rw [ha]
    ring

end MathlibExt.NumberTheory.EulerPolynomialFormulasWanted
