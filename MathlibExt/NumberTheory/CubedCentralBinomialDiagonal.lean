/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/OEIS/2897.lean` (Formal Conjectures), for the definitions and statement.
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Cubed central binomial coefficients as diagonal coefficients

The theorem `a_eq_coeff_holds` expresses the cube of the central binomial coefficient as the
coefficient of a diagonal monomial in the three-variable polynomial `pPoly`.

Set `t = 1 + x`. The last two factors of `pPoly n` multiply to `(t² - (y - z)²)^n`.
To extract the terms of equal degree in `y` and `z`, the proof expands
`((y + z) + T * (y - z))^d` in two ways. The remaining sum is the sum of squares
of the binomial coefficients in row `n`.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.OeisA002897Wanted

/-- **Cubed central binomial coefficients.** For a natural number $n$, $a(n) = \binom{2n}{n}^3$. -/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3

/-- **Indices for three variables.** Three polynomial variables are indexed by the set
$\{0, 1, 2\}$. -/
abbrev Vars := Fin 3

/-- **Exponent vector of $x^n y^n z^n$.** For a natural number $n$, the exponent vector assigning
exponent $n$ to each of the three variables $x, y, z$, that is, the monomial $x^n y^n z^n$. -/
noncomputable def xyzPowN (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars => n) (Set.toFinite _)

local notation "P" => MvPolynomial Vars ℤ

/-- **Product polynomial for the cubed central binomial coefficients.** For a natural number $n$,
this is the polynomial $(1 + x + y + z)^{2n} (1 + x + y - z)^n (1 + x - y + z)^n$ in three
variables $x, y, z$ (indexed by $0, 1, 2$) with integer coefficients. -/
noncomputable def pPoly (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n

/-- **Diagonal-coefficient property of the cubed central binomial coefficients.** This is the
proposition that for every natural number $n$, the coefficient of $x^n y^n z^n$ in the
polynomial $(1 + x + y + z)^{2n} (1 + x + y - z)^n (1 + x - y + z)^n$ in three variables
$x, y, z$ with integer coefficients equals $\binom{2n}{n}^3$. -/
def a_eq_coeff : Prop :=
  ∀ (n : ℕ), (a n : ℤ) = AddMonoidAlgebra.coeff (pPoly n) (xyzPowN n)

open Finset MvPolynomial

local notation "x" => (MvPolynomial.X 0 : P)
local notation "y" => (MvPolynomial.X 1 : P)
local notation "z" => (MvPolynomial.X 2 : P)

/-- Extract the diagonal coefficient after fixing the powers of the last two variables. -/
private lemma diagonal_monomial (m i j n : ℕ) (c : ℤ) :
    ((1 + x) ^ m * (y ^ i * z ^ j * C c)).coeff (xyzPowN n) =
      if i = n ∧ j = n then (m.choose n : ℤ) * c else 0 := by
  classical
  rw [add_comm (1 : P), add_pow, sum_mul, coeff_sum]
  have h (k : ℕ) :
      Finsupp.single (0 : Vars) k + (Finsupp.single 1 i + Finsupp.single 2 j) = xyzPowN n ↔
        k = n ∧ i = n ∧ j = n := by
    constructor
    · intro he
      have h0 := DFunLike.congr_fun he 0
      have h1 := DFunLike.congr_fun he 1
      have h2 := DFunLike.congr_fun he 2
      simpa [xyzPowN] using And.intro h0 (And.intro h1 h2)
    · rintro ⟨rfl, rfl, rfl⟩
      ext v
      fin_cases v <;> simp [xyzPowN]
  simp only [one_pow, mul_one, X_pow_eq_monomial, ← map_natCast (C : ℤ →+* P), C_apply, add_zero,
    monomial_mul_monomial, one_mul, coeff_monomial, h, ite_and,
    sum_ite_eq', mem_range]
  split_ifs <;> simp_all [Nat.choose_eq_zero_of_lt]

/-- Binomial expansion of a linear polynomial, including indices above its degree. -/
private lemma coeff_linear_pow {R : Type*} [CommRing R] (a b : R) (d k : ℕ) :
    ((Polynomial.C a * Polynomial.X + Polynomial.C b) ^ d).coeff k =
      a ^ k * b ^ (d - k) * d.choose k := by
  classical
  rw [add_pow, Polynomial.finsetSum_coeff]
  simp only [mul_pow, ← Polynomial.C_pow, Polynomial.coeff_mul_natCast,
    Polynomial.coeff_mul_C, Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k ≤ d
  · simp [ite_mul, Finset.sum_ite_eq, hk]
  · simp [ite_mul, Finset.sum_ite_eq, hk, Nat.choose_eq_zero_of_lt (by omega : d < k)]

local notation "T" => (Polynomial.X : Polynomial ℤ)

/-- Mark each occurrence of `y - z` by an auxiliary variable. Collecting instead by powers
of `y` turns its sign into the factor `(1 + T)^i (1 - T)^(d-i)`. -/
private lemma marked_expansion (d k : ℕ) :
    (y - z) ^ k * (y + z) ^ (d - k) * d.choose k =
      ∑ i ∈ range (d + 1), y ^ i * z ^ (d - i) *
        C ((((1 + T) ^ i * (1 - T) ^ (d - i)).coeff k) * d.choose i) := by
  classical
  let φ := Polynomial.mapRingHom (C : ℤ →+* P)
  have mark : Polynomial.C (y - z) * Polynomial.X + Polynomial.C (y + z) =
      φ (1 + T) * Polynomial.C y + φ (1 - T) * Polynomial.C z := by
    simp [φ, map_add, map_sub]
    ring
  rw [← coeff_linear_pow, mark, add_pow, Polynomial.finsetSum_coeff]
  refine sum_congr rfl fun i _ => ?_
  have factor :
      (φ (1 + T) * Polynomial.C y) ^ i * (φ (1 - T) * Polynomial.C z) ^ (d - i) =
        φ ((1 + T) ^ i * (1 - T) ^ (d - i)) * Polynomial.C (y ^ i * z ^ (d - i)) := by
    simp only [map_mul, map_pow, mul_pow]
    ring
  rw [factor, Polynomial.coeff_mul_natCast, Polynomial.coeff_mul_C]
  simp only [φ, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rw [map_mul, C_eq_natCast]
  ring

/-- Only total degree `2 * n` in `y,z` can contribute to the diagonal. At that degree the
two marked factors pair to give `(1 - T²)^n`. -/
private lemma marked_diagonal (m d k n : ℕ) :
    (d.choose k : ℤ) * ((1 + x) ^ m * ((y - z) ^ k * (y + z) ^ (d - k))).coeff (xyzPowN n) =
      if d = 2 * n then
        (m.choose n : ℤ) * (((1 - T ^ 2) ^ n).coeff k * (2 * n).choose n) else 0 := by
  classical
  rw [← coeff_C_mul, C_eq_natCast, mul_comm (d.choose k : P), mul_assoc,
    marked_expansion, mul_sum, coeff_sum]
  simp only [diagonal_monomial, ite_and, sum_ite_eq', mem_range]
  by_cases hd : d = 2 * n
  · subst d
    have h : (2 * n - n) = n := by omega
    have hpoly : (1 + T) * (1 - T) = 1 - T ^ 2 := by ring
    simp [h, show n < 2 * n + 1 by omega, ← mul_pow, hpoly]
  · split_ifs <;> first | rfl | omega

/-- The even coefficients after pairing the two signs. -/
private lemma coeff_even (n k : ℕ) :
    ((1 - T ^ 2) ^ n).coeff (2 * k) = (-1 : ℤ) ^ k * n.choose k := by
  have h : (1 - T ^ 2) ^ n = Polynomial.expand ℤ 2 ((1 - T) ^ n) := by simp
  rw [h, Polynomial.coeff_expand_mul' (by decide : 0 < 2)]
  simpa [sub_eq_add_neg, add_comm] using coeff_linear_pow (-1 : ℤ) 1 n k

/-- In the two binomial expansions only the terms indexed by `i = 2k` survive. -/
private lemma diagonal_term (n i k : ℕ) (hi : i ≤ 2 * n) (hk : k ≤ n) :
    ((2 * n).choose i : ℤ) *
        ((1 + x) ^ (i + 2 * (n - k)) * ((y - z) ^ (2 * k) * (y + z) ^ (2 * n - i))).coeff
          (xyzPowN n) =
      if i = 2 * k then ((2 * n).choose n : ℤ) ^ 2 * ((-1) ^ k * n.choose k) else 0 := by
  split_ifs with h
  · subst i
    rw [show 2 * k + 2 * (n - k) = 2 * n by omega, marked_diagonal, ite_eq_left rfl, coeff_even]
    ring
  · let d := 2 * k + (2 * n - i)
    have hz := marked_diagonal (i + 2 * (n - k)) d (2 * k) n
    rw [ite_eq_right (show d ≠ 2 * n by dsimp [d]; omega),
      show d - 2 * k = 2 * n - i by dsimp [d]; omega] at hz
    have hpos : 0 < d.choose (2 * k) := Nat.choose_pos (Nat.le_add_right _ _)
    rw [((mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hpos.ne')), mul_zero]

/--
**Cubed central binomial coefficients as diagonal coefficients.** For every natural number $n$,
the coefficient of $x^n y^n z^n$ in the polynomial
$(1 + x + y + z)^{2n} (1 + x + y - z)^n (1 + x - y + z)^n$ in three variables $x, y, z$ with
integer coefficients equals $\binom{2n}{n}^3$.

Source: Formal proof of the A002897 diagonal-coefficient identity
(methods of Tsoukalas et al. [arXiv/2605.22763]),
https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/2897.wip.lean#L408.
Moved from `OpenConjectures/NumberTheory/OeisA002897`.
-/
theorem a_eq_coeff_holds : a_eq_coeff := by
  intro n
  classical
  have hp : pPoly n = (-(y - z) ^ 2 + (1 + x) ^ 2) ^ n * ((1 + x) + (y + z)) ^ (2 * n) := by
    have h : (1 + x + y - z) * (1 + x - y + z) = -(y - z) ^ 2 + (1 + x) ^ 2 := by ring
    rw [pPoly, mul_assoc, ← mul_pow, h, mul_comm, add_assoc (1 + x) y z]
  symm
  calc
    (pPoly n).coeff (xyzPowN n) = ∑ k ∈ range (n + 1), ∑ i ∈ range (2 * n + 1),
          ((-1 : ℤ) ^ k * n.choose k) *
            (if i = 2 * k then ((2 * n).choose n : ℤ) ^ 2 * ((-1) ^ k * n.choose k) else 0) := by
      rw [hp, add_pow, add_pow (1 + x), sum_mul]
      simp only [mul_sum, coeff_sum]
      refine sum_congr rfl fun k hk => sum_congr rfl fun i hi => ?_
      rw [← diagonal_term n i k (mem_range_succ_iff.mp hi) (mem_range_succ_iff.mp hk)]
      conv_rhs => rw [← mul_assoc, ← coeff_C_mul]
      apply congrArg (fun p : P => p.coeff (xyzPowN n))
      rw [neg_pow]
      simp only [map_mul, map_pow, map_neg, map_one, C_eq_natCast, pow_add, pow_mul]
      ring
    _ = ∑ k ∈ range (n + 1), ((2 * n).choose n : ℤ) ^ 2 * (n.choose k : ℤ) ^ 2 := by
      refine sum_congr rfl fun k hk => ?_
      have h : 2 * k ∈ range (2 * n + 1) := by simp only [mem_range] at hk ⊢; omega
      simp only [mul_ite, mul_zero, sum_ite_eq', h, ite_true]
      have sign : ((-1 : ℤ) ^ k) ^ 2 = 1 := by rw [pow_right_comm]; simp
      calc
        _ = ((2 * n).choose n : ℤ) ^ 2 * (n.choose k : ℤ) ^ 2 * ((-1 : ℤ) ^ k) ^ 2 := by ring
        _ = _ := by rw [sign, mul_one]
    _ = _ := by
      rw [← mul_sum]
      norm_cast
      rw [Nat.sum_range_choose_sq, a, pow_succ _ 2]

end MathlibExt.NumberTheory.OeisA002897Wanted
