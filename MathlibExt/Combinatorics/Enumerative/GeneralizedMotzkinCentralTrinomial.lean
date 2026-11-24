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
