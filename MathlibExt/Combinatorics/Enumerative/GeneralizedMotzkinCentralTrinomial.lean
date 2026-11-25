/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Generalized Motzkin numbers from central trinomial coefficients

The constant terms of three consecutive powers of the symmetric trinomial Laurent polynomial
give a formula for the corresponding generalized Motzkin number.
-/

namespace MetaMathlibExt

open LaurentPolynomial

/-- **The symmetric trinomial Laurent polynomial.** For integers $a$ and $b$, this is the Laurent
polynomial $a x^{-1} + b + a x$ with integer coefficients, used to define the generalized central
trinomial coefficients and the generalized Motzkin numbers.

Source: Nadav Kohen, *Density and Symmetry in the
Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Definitions. -/
@[expose] public noncomputable def trinomialLaurent (a b : ℤ) : LaurentPolynomial ℤ :=
  C a * T (-1) + C b + C a * T 1

/-- **Generalized central trinomial coefficients.** For integers $a, b$ and a natural number $n$,
the generalized central trinomial coefficient $T_n^{(a/b)}$ is the constant term of the Laurent
polynomial $(a x^{-1} + b + a x)^n$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Definitions. -/
@[expose] public noncomputable def centralTrinomial (a b : ℤ) (n : ℕ) : ℤ :=
  (trinomialLaurent a b ^ n).coeff 0

/-- **Generalized Motzkin numbers.** For integers $a, b$ and a natural number $n$, the generalized
Motzkin number $M^{(a,b)}_n$ is the constant term of the Laurent polynomial
$(a x^{-1} + b + a x)^n (1 - x^2)$ with integer coefficients.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Definitions. -/
@[expose] public noncomputable def generalizedMotzkin (a b : ℤ) (n : ℕ) : ℤ :=
  (trinomialLaurent a b ^ n * (1 - T 2)).coeff 0

namespace generalizedMotzkin_centralTrinomial_relation

/-- Multiplication by the trinomial combines the three neighboring coefficients. -/
private theorem coeff_pow_succ (a b : ℤ) (n : ℕ) (k : ℤ) :
    (trinomialLaurent a b ^ (n + 1)).coeff k =
      (trinomialLaurent a b ^ n).coeff (k + 1) * a +
        (trinomialLaurent a b ^ n).coeff k * b +
        (trinomialLaurent a b ^ n).coeff (k - 1) * a := by
  rw [pow_succ]
  nth_rw 2 [trinomialLaurent]
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T, ← single_eq_C]
  simp only [mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_mul_single_apply, neg_neg, neg_zero, add_zero, sub_eq_add_neg]

end generalizedMotzkin_centralTrinomial_relation

/-- **Generalized Motzkin numbers from three central trinomial coefficients.** For integers $a$, $b$
let $T_r$ and $M_r$ be the constant terms of $(a x^{-1} + b + a x)^r$ and of
$(a x^{-1} + b + a x)^r (1 - x^2)$, the generalized central trinomial coefficients and generalized
Motzkin numbers. Then for every natural number $n$,
$$
2a^2 M_n = (4a^2 - b^2) T_n + 2b T_{n+1} - T_{n+2}.
$$

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Proposition 1. -/
public theorem generalizedMotzkin_centralTrinomial_relation
    (a b : ℤ) (n : ℕ) :
    2 * a ^ 2 * generalizedMotzkin a b n =
      (4 * a ^ 2 - b ^ 2) * centralTrinomial a b n +
        2 * b * centralTrinomial a b (n + 1) -
          centralTrinomial a b (n + 2) := by
  have hinv : invert (trinomialLaurent a b) = trinomialLaurent a b := by
    simp [trinomialLaurent, add_comm, add_left_comm]
  have hsym : (trinomialLaurent a b ^ n).coeff 2 = (trinomialLaurent a b ^ n).coeff (-2) := by
    simpa only [map_pow, hinv] using invert_apply (trinomialLaurent a b ^ n) 2
  simp only [generalizedMotzkin, centralTrinomial, mul_sub, mul_one, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, T, AddMonoidAlgebra.coeff_mul_single_apply,
    generalizedMotzkin_centralTrinomial_relation.coeff_pow_succ]
  norm_num
  rw [hsym]
  ring

/-- The Euler derivative multiplies each coefficient by its exponent. -/
private noncomputable def euler (p : LaurentPolynomial ℤ) :
    LaurentPolynomial ℤ :=
  AddMonoidAlgebra.ofCoeff <|
    Finsupp.onFinset p.coeff.support (fun j => j * p.coeff j) (by
      intro j hj
      by_contra hn
      exact hj (by rw [Finsupp.notMem_support_iff.mp hn, mul_zero]))

private theorem euler_coeff (p : LaurentPolynomial ℤ) (j : ℤ) :
    (euler p).coeff j = j * p.coeff j := rfl

private theorem euler_add (p q : LaurentPolynomial ℤ) :
    euler (p + q) = euler p + euler q := by
  apply LaurentPolynomial.ext
  intro j
  simp only [euler_coeff, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, mul_add]

private theorem euler_sub (p q : LaurentPolynomial ℤ) :
    euler (p - q) = euler p - euler q := by
  apply LaurentPolynomial.ext
  intro j
  simp only [euler_coeff, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, mul_sub]

private theorem euler_single (j c : ℤ) :
    euler (AddMonoidAlgebra.single j c) =
      AddMonoidAlgebra.single j (j * c) := by
  apply LaurentPolynomial.ext
  intro k
  simp only [euler_coeff, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split <;> simp_all

private theorem euler_mul (p q : LaurentPolynomial ℤ) :
    euler (p * q) = euler p * q + p * euler q := by
  refine p.induction_on' (fun p₁ p₂ h₁ h₂ => ?_) (fun i c => ?_)
  · simp only [add_mul, euler_add, h₁, h₂]
    ac_rfl
  refine q.induction_on' (fun q₁ q₂ h₁ h₂ => ?_) (fun j d => ?_)
  · simp only [mul_add, euler_add, h₁, h₂]
    ac_rfl
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.single_mul_single, euler_single,
    ← AddMonoidAlgebra.single_add]
  congr 1
  ring

private theorem euler_pow_succ (p : LaurentPolynomial ℤ) (n : ℕ) :
    euler (p ^ (n + 1)) = C (n + 1 : ℤ) * euler p * p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ p (n + 1), euler_mul, ih, pow_succ p n]
    simp only [Nat.cast_succ, map_add, map_one]
    ring

private theorem euler_monomial (j c : ℤ) :
    euler (C c * T j) = C (j * c) * T j := by
  simp only [← single_eq_C_mul_T, euler_single]

private theorem euler_C (c : ℤ) : euler (C c) = 0 := by
  rw [← single_eq_C, euler_single, zero_mul, AddMonoidAlgebra.single_zero]

private theorem euler_trinomial (a b : ℤ) :
    euler (trinomialLaurent a b) = C a * T 1 - C a * T (-1) := by
  simp only [trinomialLaurent, euler_add, euler_monomial, euler_C]
  norm_num [map_neg]
  ring

private theorem euler_euler_trinomial (a b : ℤ) :
    euler (euler (trinomialLaurent a b)) = trinomialLaurent a b - C b := by
  rw [euler_trinomial, euler_sub, euler_monomial, euler_monomial,
    trinomialLaurent]
  norm_num [map_neg]
  ring

private theorem euler_trinomial_sq (a b : ℤ) :
    euler (trinomialLaurent a b) ^ 2 =
      (trinomialLaurent a b - C b) ^ 2 - C (4 * a ^ 2) := by
  have hprod : C a * T (-1) * (C a * T 1) = C (a ^ 2) := calc
    _ = C (a * a) * (T (-1) * T 1) := by rw [map_mul]; ac_rfl
    _ = _ := by rw [← T_add]; norm_num [T_zero, pow_two]
  rw [euler_trinomial, trinomialLaurent, map_mul, ← hprod]
  norm_num [map_ofNat]
  ring

private theorem coeff_C_mul (c : ℤ) (p : LaurentPolynomial ℤ) (j : ℤ) :
    (C c * p).coeff j = c * p.coeff j := by
  rw [← single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply,
    neg_zero, zero_add]

/-- **Recurrence for generalized central trinomial coefficients.** Let $a, b$ be integers and let
$T_n$ be the constant term of $(a x^{-1} + b + a x)^n$. For every natural number $n$,
$$(n + 2) T_{n+2} = b (2n + 3) T_{n+1} - (b^2 - 4a^2)(n + 1) T_n.$$

This is the source's recurrence with its index shifted by two, so that every index is a natural
number.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Proposition 2. -/
public theorem centralTrinomial_recurrence (a b : ℤ) (n : ℕ) :
    (n + 2 : ℤ) * centralTrinomial a b (n + 2) =
      b * (2 * n + 3 : ℤ) * centralTrinomial a b (n + 1) -
        (b ^ 2 - 4 * a ^ 2) * (n + 1 : ℤ) * centralTrinomial a b n := by
  let P := trinomialLaurent a b
  -- Expand the derivative before taking its (vanishing) constant coefficient.
  have hpoly : euler (euler P * P ^ (n + 1)) =
      C (n + 2 : ℤ) * P ^ (n + 2) - C (b * (2 * n + 3 : ℤ)) * P ^ (n + 1) +
        C ((b ^ 2 - 4 * a ^ 2) * (n + 1 : ℤ)) * P ^ n := by
    calc
      _ = (P - C b) * P ^ (n + 1) +
          C (n + 1 : ℤ) * euler P ^ 2 * P ^ n := by
        rw [euler_mul, euler_pow_succ, euler_euler_trinomial]
        ring
      _ = _ := by
        rw [euler_trinomial_sq, pow_succ P (n + 1), pow_succ P n]
        simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
        ring
  have h := congrArg (fun f : LaurentPolynomial ℤ => f.coeff 0) hpoly
  simp only [euler_coeff, zero_mul, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    coeff_C_mul, sub_add_eq_add_sub] at h
  exact eq_sub_of_add_eq (sub_eq_zero.mp h.symm)

/-- **OEIS A005717.** For a natural number $n$, $a_n$ is the constant term of the Laurent
polynomial $x (x^{-1} + 1 + x)^n$ with integer coefficients.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Definitions. -/
@[expose] public noncomputable def a005717 (n : ℕ) : ℤ :=
  (trinomialLaurent 1 1 ^ n * T 1).coeff 0

/-- **OEIS A005773.** For a natural number $n$, $a_n$ is the constant term of the Laurent
polynomial $(1 + x)(x^{-1} + 1 + x)^n$ with integer coefficients.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Definitions. -/
@[expose] public noncomputable def a005773 (n : ℕ) : ℤ :=
  (trinomialLaurent 1 1 ^ n * (1 + T 1)).coeff 0

/-- **The first five powers of $x^{-1} + 1 + x$.** In the ring of Laurent polynomials over
$\mathbb{Z}$,
$(x^{-1} + 1 + x)^0 = 1$,
$(x^{-1} + 1 + x)^1 = x^{-1} + 1 + x$,
$(x^{-1} + 1 + x)^2 = x^{-2} + 2x^{-1} + 3 + 2x + x^2$,
$(x^{-1} + 1 + x)^3 = x^{-3} + 3x^{-2} + 6x^{-1} + 7 + 6x + 3x^2 + x^3$ and
$(x^{-1} + 1 + x)^4 = x^{-4} + 4x^{-3} + 10x^{-2} + 16x^{-1} + 19 + 16x + 10x^2 + 4x^3 + x^4$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Definitions. -/
public theorem trinomialLaurent_one_one_powers :
    trinomialLaurent 1 1 ^ 0 = AddMonoidAlgebra.single 0 1 ∧
    trinomialLaurent 1 1 ^ 1 =
      AddMonoidAlgebra.single (-1) 1 + AddMonoidAlgebra.single 0 1 +
        AddMonoidAlgebra.single 1 1 ∧
    trinomialLaurent 1 1 ^ 2 =
      AddMonoidAlgebra.single (-2) 1 + AddMonoidAlgebra.single (-1) 2 +
        AddMonoidAlgebra.single 0 3 + AddMonoidAlgebra.single 1 2 +
        AddMonoidAlgebra.single 2 1 ∧
    trinomialLaurent 1 1 ^ 3 =
      AddMonoidAlgebra.single (-3) 1 + AddMonoidAlgebra.single (-2) 3 +
        AddMonoidAlgebra.single (-1) 6 + AddMonoidAlgebra.single 0 7 +
        AddMonoidAlgebra.single 1 6 + AddMonoidAlgebra.single 2 3 +
        AddMonoidAlgebra.single 3 1 ∧
    trinomialLaurent 1 1 ^ 4 =
      AddMonoidAlgebra.single (-4) 1 + AddMonoidAlgebra.single (-3) 4 +
        AddMonoidAlgebra.single (-2) 10 + AddMonoidAlgebra.single (-1) 16 +
        AddMonoidAlgebra.single 0 19 + AddMonoidAlgebra.single 1 16 +
        AddMonoidAlgebra.single 2 10 + AddMonoidAlgebra.single 3 4 +
        AddMonoidAlgebra.single 4 1 := by
  constructor
  · simp [trinomialLaurent, LaurentPolynomial.single_eq_C_mul_T]
  constructor
  · simp [trinomialLaurent, LaurentPolynomial.single_eq_C_mul_T]
  constructor
  · simp only [LaurentPolynomial.single_eq_C_mul_T]
    simp [trinomialLaurent]
    ring_nf
    simp only [LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
    norm_num
    ring
  constructor
  · simp only [LaurentPolynomial.single_eq_C_mul_T]
    simp [trinomialLaurent]
    ring_nf
    simp only [LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
    norm_num
    ring
  · simp only [LaurentPolynomial.single_eq_C_mul_T]
    simp [trinomialLaurent]
    ring_nf
    simp only [LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
    norm_num
    ring

/-- **First five central trinomial coefficients.** The central trinomial coefficients $T_n$, the
constant terms of $(x^{-1} + 1 + x)^n$, are $1, 1, 3, 7, 19$ for $n = 0, 1, 2, 3, 4$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Definitions. -/
public theorem centralTrinomial_one_one_values :
    (List.range 5).map (centralTrinomial 1 1) = [1, 1, 3, 7, 19] := by
  rcases trinomialLaurent_one_one_powers with ⟨h0, h1, h2, h3, h4⟩
  have hr : List.range 5 = [0, 1, 2, 3, 4] := by decide
  rw [hr]
  simp only [List.map_cons, List.map_nil]
  unfold centralTrinomial
  rw [h0, h1, h2, h3, h4]
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single,
    Finsupp.add_apply, Finsupp.single_apply]
  norm_num

/-- **First five generalized Motzkin numbers at $a = b = 1$.** The generalized Motzkin numbers
$M_n$ for $a = b = 1$, the constant terms of $(x^{-1} + 1 + x)^n (1 - x^2)$, are $1, 1, 2, 4, 9$
for $n = 0, 1, 2, 3, 4$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Definitions. -/
public theorem generalizedMotzkin_one_one_values :
    (List.range 5).map (generalizedMotzkin 1 1) = [1, 1, 2, 4, 9] := by
  rcases trinomialLaurent_one_one_powers with ⟨h0, h1, h2, h3, h4⟩
  have hr : List.range 5 = [0, 1, 2, 3, 4] := by decide
  rw [hr]
  simp only [List.map_cons, List.map_nil]
  unfold generalizedMotzkin
  rw [h0, h1, h2, h3, h4]
  simp only [sub_eq_add_neg, mul_add, add_mul, mul_neg, mul_one,
    LaurentPolynomial.T, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_neg,
    AddMonoidAlgebra.coeff_single, Finsupp.add_apply, Finsupp.neg_apply,
    Finsupp.single_apply]
  norm_num

end MetaMathlibExt
