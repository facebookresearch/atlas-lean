/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Nat.Digits.Defs
public import MathlibExt.Combinatorics.Enumerative.RiordanNumber
public import MathlibExt.Data.Set.Density
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

@[expose] public section

open LaurentPolynomial

/-- **The symmetric trinomial Laurent polynomial.** For integers $a$ and $b$, this is the Laurent
polynomial $a x^{-1} + b + a x$ with integer coefficients, used to define the generalized central
trinomial coefficients and the generalized Motzkin numbers.

Source: Nadav Kohen, *Density and Symmetry in the
Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Definitions. -/
public noncomputable def trinomialLaurent (a b : ℤ) : LaurentPolynomial ℤ :=
  C a * T (-1) + C b + C a * T 1

/-- **Laurent polynomials of degree at most one.** For integers $\alpha, \beta, \gamma$, this is the
Laurent polynomial $\alpha x^{-1} + \beta + \gamma x$ with integer coefficients.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Lemma 1. The degree-one hypotheses of Lemma 1 are imposed on the
coefficients in the statements that use this polynomial. -/
public noncomputable def linearLaurent (α β γ : ℤ) : LaurentPolynomial ℤ :=
  C α * T (-1) + C β + C γ * T 1

/-- **Generalized central trinomial coefficients.** For integers $a, b$ and a natural number $n$,
the generalized central trinomial coefficient $T_n^{(a/b)}$ is the constant term of the Laurent
polynomial $(a x^{-1} + b + a x)^n$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Definitions. -/
public noncomputable def centralTrinomial (a b : ℤ) (n : ℕ) : ℤ :=
  (trinomialLaurent a b ^ n).coeff 0

/-- **Generalized Motzkin numbers.** For integers $a, b$ and a natural number $n$, the generalized
Motzkin number $M^{(a,b)}_n$ is the constant term of the Laurent polynomial
$(a x^{-1} + b + a x)^n (1 - x^2)$ with integer coefficients.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Definitions. -/
public noncomputable def generalizedMotzkin (a b : ℤ) (n : ℕ) : ℤ :=
  (trinomialLaurent a b ^ n * (1 - T 2)).coeff 0

/-- **OEIS A005717.** For a natural number $n$, $a_n$ is the constant term of the Laurent
polynomial $x (x^{-1} + 1 + x)^n$ with integer coefficients.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Definitions. -/
public noncomputable def a005717 (n : ℕ) : ℤ :=
  (trinomialLaurent 1 1 ^ n * T 1).coeff 0

/-- **OEIS A005773.** For a natural number $n$, $a_n$ is the constant term of the Laurent
polynomial $(1 + x)(x^{-1} + 1 + x)^n$ with integer coefficients.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Definitions. -/
public noncomputable def a005773 (n : ℕ) : ℤ :=
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

/-- **Generalized Motzkin numbers from three central trinomial coefficients.** For integers $a$, $b$
let $T_r$ and $M_r$ be the constant terms of $(a x^{-1} + b + a x)^r$ and of
$(a x^{-1} + b + a x)^r (1 - x^2)$, the generalized central trinomial coefficients and generalized
Motzkin numbers. Then for every natural number $n$,
$$
2a^2 M_n = (4a^2 - b^2) T_n + 2b T_{n+1} - T_{n+2}.
$$

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Proposition 1. -/
public theorem_wanted generalizedMotzkin_centralTrinomial_relation
    (a b : ℤ) (n : ℕ) :
    2 * a ^ 2 * generalizedMotzkin a b n =
      (4 * a ^ 2 - b ^ 2) * centralTrinomial a b n +
        2 * b * centralTrinomial a b (n + 1) -
          centralTrinomial a b (n + 2)

/-- **Recurrence for generalized central trinomial coefficients.** Let $a, b$ be integers and let
$T_n$ be the constant term of $(a x^{-1} + b + a x)^n$. For every natural number $n$,
$$(n + 2) T_{n+2} = b (2n + 3) T_{n+1} - (b^2 - 4a^2)(n + 1) T_n.$$

This is the source's recurrence with its index shifted by two, so that every index is a natural
number.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Proposition 2. -/
public theorem_wanted centralTrinomial_recurrence (a b : ℤ) (n : ℕ) :
    (n + 2 : ℤ) * centralTrinomial a b (n + 2) =
      b * (2 * n + 3 : ℤ) * centralTrinomial a b (n + 1) -
        (b ^ 2 - 4 * a ^ 2) * (n + 1 : ℤ) * centralTrinomial a b n

/-- **Three-term recurrence for generalized Motzkin numbers.** For integers $a$, $b$ let $M_r$ be
the constant term of $(a x^{-1} + b + a x)^r (1 - x^2)$, the generalized Motzkin number. Then for
every natural number $n$,
$$
(n + 4) M_{n+2} = b (2n + 5) M_{n+1} - (b^2 - 4a^2)(n + 1) M_n.
$$

The source states the recurrence for $M_n$ with $n \ge 2$; it is written here at index $n + 2$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Corollary 1. -/
public theorem_wanted generalizedMotzkin_recurrence (a b : ℤ) (n : ℕ) :
    (n + 4 : ℤ) * generalizedMotzkin a b (n + 2) =
      b * (2 * n + 5 : ℤ) * generalizedMotzkin a b (n + 1) -
        (b ^ 2 - 4 * a ^ 2) * (n + 1 : ℤ) * generalizedMotzkin a b n

/-- **Mirror symmetry of central trinomial coefficients modulo a prime.** Let $a, b$ be integers
and let $T_n$ be the constant term of $(a x^{-1} + b + a x)^n$. For every prime $p > 2$ and every
natural number $k \le (p - 1)/2$,
$$T_{p-1-k} \equiv (b^2 - 4a^2)^{(p-1)/2 - k} \, T_k \pmod p.$$

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Theorem 1. -/
public theorem_wanted centralTrinomial_mod_prime_symmetry
    (a b : ℤ) (p k : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hk : k ≤ (p - 1) / 2) :
    centralTrinomial a b (p - 1 - k) ≡
      (b ^ 2 - 4 * a ^ 2) ^ ((p - 1) / 2 - k) * centralTrinomial a b k
      [ZMOD p]

/-- **Reflection symmetry of generalized Motzkin numbers modulo $p$.** For integers $a$, $b$ let
$M_r$ be the constant term of $(a x^{-1} + b + a x)^r (1 - x^2)$, the generalized Motzkin number.
Let $p > 3$ be a prime and $k$ a natural number with $k \le (p - 3)/2$. Then
$$
M_{p-3-k} \equiv (b^2 - 4a^2)^{(p-3)/2 - k} \, M_k \pmod p.
$$

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Theorem 2. -/
public theorem_wanted generalizedMotzkin_mod_prime_symmetry
    (a b : ℤ) (p k : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (hk : k ≤ (p - 3) / 2) :
    generalizedMotzkin a b (p - 3 - k) ≡
      (b ^ 2 - 4 * a ^ 2) ^ ((p - 3) / 2 - k) * generalizedMotzkin a b k
      [ZMOD p]

/-- **Squared central trinomial coefficient at one less than a prime.** Let $a, b$ be integers,
let $T_n$ be the constant term of $(a x^{-1} + b + a x)^n$, and let $p$ be a prime with
$b^2 - 4a^2 \not\equiv 0 \pmod p$. Then $T_{p-1}^2 \equiv 1 \pmod p$.

This is the source's Corollary 2 in an equivalent squared form, which avoids an inverse residue
modulo $p$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Corollary 2. -/
public theorem_wanted centralTrinomial_prime_minus_one_sq
    (a b : ℤ) (p : ℕ) (hp : p.Prime)
    (hdisc : ¬(b ^ 2 - 4 * a ^ 2 ≡ 0 [ZMOD p])) :
    centralTrinomial a b (p - 1) ^ 2 ≡ 1 [ZMOD p]

/-- **Primes dividing the Motzkin number $M_{p-2}$.** A prime $p$ divides the Motzkin number
$M_{p-2} = M^{(1,1)}_{p-2}$ if and only if $p \equiv 1 \pmod 3$.

For $p = 2$ both sides are false, since $M_0 = 1$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Proposition 3. -/
public theorem_wanted prime_dvd_motzkin_prime_minus_two_iff
    (p : ℕ) (hp : p.Prime) :
    generalizedMotzkin 1 1 (p - 2) ≡ 0 [ZMOD p] ↔ p ≡ 1 [MOD 3]

/-- **Lucas property for constant terms of powers of linear Laurent polynomials.** Let $p$ be a
prime, let $\alpha$, $\beta$, $\gamma$, $a$, $b$ be integers, and let $n$ be a natural number whose
base-$p$ digits are $d_0, \dots, d_s$ (there are none when $n = 0$, and both products below are
then $1$). Write $\operatorname{ct}(F)$ for the constant term of a Laurent polynomial $F$ and put
$P = \alpha x^{-1} + \beta + \gamma x$. Then
$$
\operatorname{ct}(P^n) \equiv \prod_{i=0}^{s} \operatorname{ct}(P^{d_i}) \pmod p,
$$
and the generalized central trinomial coefficients $T_r = \operatorname{ct}((a x^{-1} + b + a x)^r)$
satisfy $T_n \equiv \prod_{i=0}^{s} T_{d_i} \pmod p$.

The source assumes that $P$ has degree one; here $\alpha$ and $\gamma$ are arbitrary, which
includes that case.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Proposition 4. -/
public theorem_wanted constantTerm_linearLaurent_pow_digits (α β γ a b : ℤ) (p n : ℕ)
    (hp : p.Prime) :
    (linearLaurent α β γ ^ n).coeff 0 ≡
        ((Nat.digits p n).map fun d => (linearLaurent α β γ ^ d).coeff 0).prod [ZMOD p] ∧
      centralTrinomial a b n ≡
        ((Nat.digits p n).map fun d => centralTrinomial a b d).prod [ZMOD p]

/-- **Digit decomposition of shifted sums of constant terms modulo a prime.** Let $\alpha, \beta,
\gamma$ be integers with $\alpha \ne 0$ or $\gamma \ne 0$, let $a_r$ be the constant term of
$(\alpha x^{-1} + \beta + \gamma x)^r$, let $p$ be a prime, let $h < p$ be a natural number, let
$c_0, c_1, \ldots$ be integers, and let $b_r = \sum_{i=0}^{h} c_i a_{r+i}$. Let $q, k$ be natural
numbers, let $m, n_0 < p$ be natural numbers with $m \ne p - 1$, put
$n = ((qp + m) p^k + p^k - 1) p + n_0$ (in base $p$: the digits of $q$, then $m$, then $k$ digits
$p - 1$, then $n_0$), and let $C = \min(h, p - n_0 - 1)$. Then
$$b_n \equiv a_q \Big( a_m a_{p-1}^k \sum_{i=0}^{C} c_i a_{n_0+i} +
a_{m+1} \sum_{i=p-n_0}^{h} c_i a_{i-(p-n_0)} \Big) \pmod p,$$
where the last sum is empty when $h < p - n_0$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Lemma 1. -/
public theorem_wanted constantTermLinearCombination_digit_decomposition
    (α β γ : ℤ) (hdegree : α ≠ 0 ∨ γ ≠ 0) (c : ℕ → ℤ)
    (h p q m k n₀ n : ℕ) (hp : p.Prime) (hph : h < p)
    (hm : m < p) (hn₀ : n₀ < p) (hmne : m ≠ p - 1)
    (hn : n = ((q * p + m) * p ^ k + (p ^ k - 1)) * p + n₀) :
    let a := fun r : ℕ => (linearLaurent α β γ ^ r).coeff 0
    let b := fun r : ℕ => ∑ i ∈ Finset.range (h + 1), c i * a (r + i)
    let C := min h (p - n₀ - 1)
    b n ≡ a q *
      (a m * a (p - 1) ^ k *
          (∑ i ∈ Finset.range (C + 1), c i * a (n₀ + i)) +
        a (m + 1) *
          (∑ i ∈ Finset.Icc (p - n₀) h, c i * a (i - (p - n₀))))
      [ZMOD p]

/-- **Digit formula for shifted sums of constant terms, small last digit.** Let $\alpha$, $\beta$,
$\gamma$ be integers with $\alpha \ne 0$ or $\gamma \ne 0$, and let $a_r$ be the constant term of
$(\alpha x^{-1} + \beta + \gamma x)^r$. Let $c_0, c_1, c_2, \dots$ be integers, let $h$ be a natural
number, and put $b_r = \sum_{i=0}^{h} c_i a_{r+i}$. Let $p$ be a prime with $h < p$, and let $q$,
$m$, $k$, $n_0$ be natural numbers with $m < p$, $m \ne p - 1$, $n_0 < p$ and $n_0 < p - h$. If
$n = ((qp + m)p^k + p^k - 1)p + n_0$, that is, $n$ is obtained from $q$ by appending the base-$p$
digits $m$, then $k$ digits $p - 1$, then $n_0$, then
$$
b_n \equiv a_q \, a_m \, a_{p-1}^k \sum_{i=0}^{h} c_i a_{n_0+i} \pmod p
\quad \text{and} \quad
b_n \equiv a_{(n - n_0)/p} \, b_{n_0} \pmod p.
$$

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Lemma 1. -/
public theorem_wanted constantTermLinearCombination_small_last_digit
    (α β γ : ℤ) (hdegree : α ≠ 0 ∨ γ ≠ 0) (c : ℕ → ℤ)
    (h p q m k n₀ n : ℕ) (hp : p.Prime) (hph : h < p)
    (hm : m < p) (hn₀ : n₀ < p) (hmne : m ≠ p - 1)
    (hnsmall : n₀ < p - h)
    (hn : n = ((q * p + m) * p ^ k + (p ^ k - 1)) * p + n₀) :
    let a := fun r : ℕ => (linearLaurent α β γ ^ r).coeff 0
    let b := fun r : ℕ => ∑ i ∈ Finset.range (h + 1), c i * a (r + i)
    (b n ≡ a q * a m * a (p - 1) ^ k *
        (∑ i ∈ Finset.range (h + 1), c i * a (n₀ + i)) [ZMOD p]) ∧
      (b n ≡ a ((n - n₀) / p) * b n₀ [ZMOD p])

/-- **Density one for zeros of shifted combinations of central trinomial coefficients.** Let
$\alpha$ and $\beta$ be integers with $\alpha \neq 0$, and write $a_r$ for the generalized central
trinomial coefficient with parameters $\alpha, \beta$, the constant term of
$(\alpha x^{-1} + \beta + \alpha x)^r$. Let $p$ be a prime, let $h < p$ be a natural number, let
$(c_i)_{i \ge 0}$ be a sequence of integers, and set $b_r = \sum_{i=0}^{h} c_i a_{r+i}$ for
$r \in \mathbb{N}$. If $a_r \equiv 0 \pmod p$ for some $r \in \mathbb{N}$, then the set of
$r \in \mathbb{N}$ with $b_r \equiv 0 \pmod p$ has natural density $1$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers
Modulo p*, INTEGERS 26 (2026), Article A22, Lemma 2. -/
public theorem_wanted symmetricConstantTerm_zero_density_one
    (α β : ℤ) (hα : α ≠ 0) (c : ℕ → ℤ) (h p : ℕ)
    (hp : p.Prime) (hph : h < p)
    (hzero : ∃ r : ℕ, centralTrinomial α β r ≡ 0 [ZMOD p]) :
    let b := fun r : ℕ =>
      ∑ i ∈ Finset.range (h + 1), c i * centralTrinomial α β (r + i)
    ({r | b r ≡ 0 [ZMOD p]} : Set ℕ).HasDensity 1

/-- **Zero density of shifted combinations of central trinomial coefficients.** Let $\alpha$ and
$\beta$ be integers with $\alpha \neq 0$, and write $a_r$ for the generalized central trinomial
coefficient with parameters $\alpha, \beta$, the constant term of
$(\alpha x^{-1} + \beta + \alpha x)^r$. Let $p$ be a prime, let $h < p$ be a natural number, let
$(c_i)_{i \ge 0}$ be a sequence of integers, and set $b_r = \sum_{i=0}^{h} c_i a_{r+i}$ for
$r \in \mathbb{N}$. Suppose that $a_r \not\equiv 0 \pmod p$ for every $r \in \mathbb{N}$. For
$p - h \le r \le p - 1$ put $C_r = \min(h, p - r - 1)$, $S_r = \sum_{i=0}^{C_r} c_i a_{r+i}$ and
$S'_r = \sum_{i=C_r+1}^{h} c_i a_{i-(p-r)}$. Let $N_0$ be the number of $r$ with $0 \le r < p - h$
and $b_r \equiv 0 \pmod p$, let $N_1$ be the number of pairs $(r, m)$ with $p - h \le r \le p - 1$
and $0 \le m \le p - 2$ such that $a_m S_r \equiv -a_{m+1} S'_r \pmod p$, and let $N_2$ be the
number of pairs $(r, m)$ in that range such that $a_m S_r \equiv -a_{p-1} a_{m+1} S'_r \pmod p$.
Then the set of $r \in \mathbb{N}$ with $b_r \equiv 0 \pmod p$ has natural density

$$\frac{N_0}{p} + \frac{N_1}{(p-1)(p+1)} + \frac{N_2}{(p-1)p(p+1)}.$$

No assumption $p > 2$ is made.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo
p*, INTEGERS 26 (2026), Article A22, Lemma 2. -/
public theorem_wanted symmetricConstantTerm_zero_density_formula
    (α β : ℤ) (hα : α ≠ 0) (c : ℕ → ℤ) (h p : ℕ)
    (hp : p.Prime) (hph : h < p)
    (hnonzero : ∀ r : ℕ, ¬(centralTrinomial α β r ≡ 0 [ZMOD p])) :
    let a := centralTrinomial α β
    let b := fun r : ℕ => ∑ i ∈ Finset.range (h + 1), c i * a (r + i)
    let boundary := (Finset.Icc (p - h) (p - 1)).product (Finset.range (p - 1))
    let firstPairs := boundary.filter (fun nm =>
      let r := nm.1
      let m := nm.2
      let C := min h (p - r - 1)
      a m * (∑ i ∈ Finset.range (C + 1), c i * a (r + i)) ≡
        -(a (m + 1) * (∑ i ∈ Finset.Icc (C + 1) h,
          c i * a (i - (p - r)))) [ZMOD p])
    let secondPairs := boundary.filter (fun nm =>
      let r := nm.1
      let m := nm.2
      let C := min h (p - r - 1)
      a m * (∑ i ∈ Finset.range (C + 1), c i * a (r + i)) ≡
        -(a (p - 1) * a (m + 1) *
          (∑ i ∈ Finset.Icc (C + 1) h, c i * a (i - (p - r)))) [ZMOD p])
    ({r | b r ≡ 0 [ZMOD p]} : Set ℕ).HasDensity
      ((((Finset.range (p - h)).filter (fun r => b r ≡ 0 [ZMOD p])).card : ℝ) /
          (p : ℝ) +
        (firstPairs.card : ℝ) / (((p - 1 : ℕ) : ℝ) * (p + 1 : ℝ)) +
        (secondPairs.card : ℝ) /
          (((p - 1 : ℕ) : ℝ) * (p : ℝ) * (p + 1 : ℝ)))

/-- **Generalized Motzkin numbers modulo $p$ with last digit below $p - 2$.** For integers $a$, $b$
let $T_r$ and $M_r$ be the constant terms of $(a x^{-1} + b + a x)^r$ and of
$(a x^{-1} + b + a x)^r (1 - x^2)$, the generalized central trinomial coefficients and generalized
Motzkin numbers. Let $p > 2$ be a prime with $b^2 - 4a^2 \not\equiv 0 \pmod p$, and let
$q$, $n_0$ be natural numbers with $n_0 < p - 2$. If $n = qp + n_0$, then
$$
2a^2 M_n \equiv 2a^2 \, T_q \, M_{n_0} \pmod p.
$$

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Proposition 5(i). -/
public theorem_wanted generalizedMotzkin_digit_below_prime_minus_two
    (a b : ℤ) (p q n₀ n : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hdisc : ¬(b ^ 2 - 4 * a ^ 2 ≡ 0 [ZMOD p]))
    (hn₀ : n₀ < p - 2) (hn : n = q * p + n₀) :
    2 * a ^ 2 * generalizedMotzkin a b n ≡
      2 * a ^ 2 * centralTrinomial a b q * generalizedMotzkin a b n₀
      [ZMOD p]

/-- **Generalized Motzkin numbers modulo $p$ with last digit $p - 2$.** For integers $a$, $b$ let
$T_r$ and $M_r$ be the constant terms of $(a x^{-1} + b + a x)^r$ and of
$(a x^{-1} + b + a x)^r (1 - x^2)$, the generalized central trinomial coefficients and generalized
Motzkin numbers. Let $p > 2$ be a prime with $b^2 - 4a^2 \not\equiv 0 \pmod p$, and let
$q$, $m$, $k$ be natural numbers with $m < p - 1$. If $n = ((qp + m)p^k + p^k - 1)p + p - 2$, that
is, $n$ is obtained from $q$ by appending the base-$p$ digits $m$, then $k$ digits $p - 1$, then
$p - 2$, then
$$
2a^2 M_n \equiv T_q \left( b \, T_m \, T_{p-1}^{k+1} - T_{m+1} \right) \pmod p.
$$

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Proposition 5(ii). -/
public theorem_wanted generalizedMotzkin_digit_prime_minus_two
    (a b : ℤ) (p q m k n : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hdisc : ¬(b ^ 2 - 4 * a ^ 2 ≡ 0 [ZMOD p])) (hm : m < p - 1)
    (hn : n = ((q * p + m) * p ^ k + (p ^ k - 1)) * p + (p - 2)) :
    2 * a ^ 2 * generalizedMotzkin a b n ≡
      centralTrinomial a b q *
        (b * centralTrinomial a b m * centralTrinomial a b (p - 1) ^ (k + 1) -
          centralTrinomial a b (m + 1))
      [ZMOD p]

/-- **Generalized Motzkin numbers modulo $p$ with last digit $p - 1$.** For integers $a$, $b$ let
$T_r$ and $M_r$ be the constant terms of $(a x^{-1} + b + a x)^r$ and of
$(a x^{-1} + b + a x)^r (1 - x^2)$, the generalized central trinomial coefficients and generalized
Motzkin numbers. Let $p > 2$ be a prime with $D = b^2 - 4a^2 \not\equiv 0 \pmod p$, let
$q$, $m$, $k$ be natural numbers with $m < p - 1$, and put $\ell = p - 2 - m$. If
$n = ((qp + m)p^k + p^k - 1)p + p - 1$, that is, $n$ is obtained from $q$ by appending the base-$p$
digits $m$, then $k + 1$ digits $p - 1$, then
$$
D^{(p-1)/2} \cdot 2a^2 M_n \equiv
D^{m+1} \, T_q \left( b \, T_\ell - T_{p-1}^{k+1} \, T_{\ell+1} \right) \pmod p.
$$

The source states this congruence with a power of the unit $D$ whose exponent may be negative;
here it is multiplied out so that every exponent is nonnegative.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Proposition 5(iii). -/
public theorem_wanted generalizedMotzkin_digit_prime_minus_one
    (a b : ℤ) (p q m k n : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hdisc : ¬(b ^ 2 - 4 * a ^ 2 ≡ 0 [ZMOD p])) (hm : m < p - 1)
    (hn : n = ((q * p + m) * p ^ k + (p ^ k - 1)) * p + (p - 1)) :
    let ℓ := p - 2 - m
    (b ^ 2 - 4 * a ^ 2) ^ ((p - 1) / 2) *
        (2 * a ^ 2 * generalizedMotzkin a b n) ≡
      (b ^ 2 - 4 * a ^ 2) ^ (m + 1) * centralTrinomial a b q *
        (b * centralTrinomial a b ℓ -
          centralTrinomial a b (p - 1) ^ (k + 1) *
            centralTrinomial a b (ℓ + 1))
      [ZMOD p]

/-- **Zeros of generalized Motzkin numbers with a small last digit.** Let $a, b$ be integers and
let $p > 2$ be a prime with $b^2 - 4a^2 \not\equiv 0 \pmod p$, and suppose that the generalized
central trinomial coefficients satisfy $T^{(a,b)}_r \not\equiv 0 \pmod p$ for every $r < p$. Let
$q, n_0$ be natural numbers with $n_0 < p - 2$ and let $n = qp + n_0$. Then $p$ divides the
generalized Motzkin number $M^{(a,b)}_n$ if and only if $p$ divides $M^{(a,b)}_{n_0}$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Corollary 3. -/
public theorem_wanted generalizedMotzkin_zero_digit_below_prime_minus_two
    (a b : ℤ) (p q n₀ n : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hdisc : ¬(b ^ 2 - 4 * a ^ 2 ≡ 0 [ZMOD p]))
    (hT : ∀ r < p, ¬(centralTrinomial a b r ≡ 0 [ZMOD p]))
    (hn₀ : n₀ < p - 2) (hn : n = q * p + n₀) :
    generalizedMotzkin a b n ≡ 0 [ZMOD p] ↔
      generalizedMotzkin a b n₀ ≡ 0 [ZMOD p]

/-- **Zeros of generalized Motzkin numbers with last digit $p - 2$.** Let $a, b$ be integers and
let $p > 2$ be a prime with $a \not\equiv 0 \pmod p$ and $b^2 - 4a^2 \not\equiv 0 \pmod p$. Write
$T_r = T^{(a,b)}_r$ for the generalized central trinomial coefficients and suppose that
$T_r \not\equiv 0 \pmod p$ for every $r < p$. Let $q, m, k$ be natural numbers with $m < p - 1$
and let
$$n = \bigl((qp + m)p^k + p^k - 1\bigr)p + p - 2.$$
Then $p$ divides the generalized Motzkin number $M^{(a,b)}_n$ if and only if
$b T_m \equiv T_{p-1}^{k+1} T_{m+1} \pmod p$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Corollary 3. The hypothesis $a \not\equiv 0 \pmod p$ is implicit
in the paper, which cancels $2a^2$. -/
public theorem_wanted generalizedMotzkin_zero_digit_prime_minus_two
    (a b : ℤ) (p q m k n : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (ha : ¬(a ≡ 0 [ZMOD p]))
    (hdisc : ¬(b ^ 2 - 4 * a ^ 2 ≡ 0 [ZMOD p]))
    (hT : ∀ r < p, ¬(centralTrinomial a b r ≡ 0 [ZMOD p]))
    (hm : m < p - 1)
    (hn : n = ((q * p + m) * p ^ k + (p ^ k - 1)) * p + (p - 2)) :
    generalizedMotzkin a b n ≡ 0 [ZMOD p] ↔
      b * centralTrinomial a b m ≡
        centralTrinomial a b (p - 1) ^ (k + 1) *
          centralTrinomial a b (m + 1) [ZMOD p]

/-- **Zeros of generalized Motzkin numbers with last digit $p - 1$.** Let $a, b$ be integers and
let $p > 2$ be a prime with $a \not\equiv 0 \pmod p$ and $b^2 - 4a^2 \not\equiv 0 \pmod p$. Write
$T_r = T^{(a,b)}_r$ for the generalized central trinomial coefficients and suppose that
$T_r \not\equiv 0 \pmod p$ for every $r < p$. Let $q, m, k$ be natural numbers with $m < p - 1$,
let
$$n = \bigl((qp + m)p^k + p^k - 1\bigr)p + p - 1,$$
and let $\ell = p - 2 - m$. Then $p$ divides the generalized Motzkin number $M^{(a,b)}_n$ if and
only if $b T_\ell \equiv T_{p-1}^{k+1} T_{\ell+1} \pmod p$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Corollary 3. The hypothesis $a \not\equiv 0 \pmod p$ is implicit
in the paper, which cancels $2a^2$. -/
public theorem_wanted generalizedMotzkin_zero_digit_prime_minus_one
    (a b : ℤ) (p q m k n : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (ha : ¬(a ≡ 0 [ZMOD p]))
    (hdisc : ¬(b ^ 2 - 4 * a ^ 2 ≡ 0 [ZMOD p]))
    (hT : ∀ r < p, ¬(centralTrinomial a b r ≡ 0 [ZMOD p]))
    (hm : m < p - 1)
    (hn : n = ((q * p + m) * p ^ k + (p ^ k - 1)) * p + (p - 1)) :
    let ℓ := p - 2 - m
    generalizedMotzkin a b n ≡ 0 [ZMOD p] ↔
      b * centralTrinomial a b ℓ ≡
        centralTrinomial a b (p - 1) ^ (k + 1) *
          centralTrinomial a b (ℓ + 1) [ZMOD p]

/-- **Generalized Motzkin numbers vanish modulo a prime with density one.** Let $a, b$ be integers
and let $p$ be a prime. If $p$ divides the generalized central trinomial coefficient
$T^{(a,b)}_r$ for some $r < p$, then the set of $n \in \mathbb{N}$ such that $p$ divides the
generalized Motzkin number $M^{(a,b)}_n$ has natural density $1$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Theorem 3. -/
public theorem_wanted generalizedMotzkin_zero_density_one
    (a b : ℤ) (p : ℕ) (hp : p.Prime)
    (hzero : ∃ r < p, centralTrinomial a b r ≡ 0 [ZMOD p]) :
    ({n | generalizedMotzkin a b n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity 1

/-- **Zero density formula for generalized Motzkin numbers modulo a prime.** Let $a, b$ be
integers and let $p > 2$ be a prime with $a \not\equiv 0 \pmod p$. Write $T_r = T^{(a,b)}_r$ for
the generalized central trinomial coefficients and $M_n = M^{(a,b)}_n$ for the generalized Motzkin
numbers, and suppose that $T_r \not\equiv 0 \pmod p$ for every $r < p$. Let $A$ be the number of
$r < p - 2$ with $M_r \equiv 0 \pmod p$, let $B$ be the number of $m < p - 1$ with
$b T_m \equiv T_{p-1} T_{m+1} \pmod p$, and let $C$ be the number of $m < p - 1$ with
$b T_m \equiv T_{m+1} \pmod p$. Then the set of $n \in \mathbb{N}$ with $M_n \equiv 0 \pmod p$ has
natural density
$$D_0 = \frac{A}{p} + \frac{2B}{(p-1)(p+1)} + \frac{2C}{(p-1)p(p+1)}.$$

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Theorem 3. The hypothesis $a \not\equiv 0 \pmod p$ is implicit in
the paper, which cancels $2a^2$. -/
public theorem_wanted generalizedMotzkin_zero_density_formula
    (a b : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (ha : ¬(a ≡ 0 [ZMOD p]))
    (hnonzero : ∀ r < p, ¬(centralTrinomial a b r ≡ 0 [ZMOD p])) :
    let D₀ :=
      ((((Finset.range (p - 2)).filter
          (fun r => generalizedMotzkin a b r ≡ 0 [ZMOD p])).card : ℝ) /
          (p : ℝ) +
        2 * (((Finset.range (p - 1)).filter (fun m =>
          b * centralTrinomial a b m ≡
            centralTrinomial a b (p - 1) * centralTrinomial a b (m + 1)
            [ZMOD p])).card : ℝ) /
          (((p - 1 : ℕ) : ℝ) * (p + 1 : ℝ)) +
        2 * (((Finset.range (p - 1)).filter (fun m =>
          b * centralTrinomial a b m ≡ centralTrinomial a b (m + 1)
            [ZMOD p])).card : ℝ) /
          (((p - 1 : ℕ) : ℝ) * (p : ℝ) * (p + 1 : ℝ)))
    ({n | generalizedMotzkin a b n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity D₀

/-- **Density of each nonzero residue among generalized Motzkin numbers modulo $p$.** For integers
$a$, $b$ let $T_r$ and $M_r$ be the constant terms of $(a x^{-1} + b + a x)^r$ and of
$(a x^{-1} + b + a x)^r (1 - x^2)$, the generalized central trinomial coefficients and generalized
Motzkin numbers. Let $p > 2$ be a prime with $a \not\equiv 0 \pmod p$ such that
$T_r \not\equiv 0 \pmod p$ for every $r < p$, and suppose that the residues of $T_0, \dots, T_{p-1}$
generate the unit group $(\mathbb{Z}/p\mathbb{Z})^\times$. Put
$$
D_0 = \frac{N_1}{p} + \frac{2 N_2}{(p - 1)(p + 1)} + \frac{2 N_3}{(p - 1) p (p + 1)},
$$
where $N_1$ is the number of $r < p - 2$ with $M_r \equiv 0 \pmod p$, $N_2$ is the number of
$m < p - 1$ with $b T_m \equiv T_{p-1} T_{m+1} \pmod p$, and $N_3$ is the number of $m < p - 1$
with $b T_m \equiv T_{m+1} \pmod p$. Then for every nonzero residue $z$ modulo $p$, the set of
natural numbers $n$ with $M_n \equiv z \pmod p$ has natural density $(1 - D_0)/(p - 1)$.

The hypothesis $a \not\equiv 0 \pmod p$ is implicit in the source, which cancels $2a^2$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Theorem 3. -/
public theorem_wanted generalizedMotzkin_nonzero_density
    (a b : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (ha : ¬(a ≡ 0 [ZMOD p]))
    (hnonzero : ∀ r < p, ¬(centralTrinomial a b r ≡ 0 [ZMOD p]))
    (hgenerate : Subgroup.closure
      {u : (ZMod p)ˣ | ∃ r < p,
        (u : ZMod p) = (centralTrinomial a b r : ZMod p)} = ⊤)
    (z : ZMod p) (hz : z ≠ 0) :
    let D₀ :=
      ((((Finset.range (p - 2)).filter
          (fun r => generalizedMotzkin a b r ≡ 0 [ZMOD p])).card : ℝ) /
          (p : ℝ) +
        2 * (((Finset.range (p - 1)).filter (fun m =>
          b * centralTrinomial a b m ≡
            centralTrinomial a b (p - 1) * centralTrinomial a b (m + 1)
            [ZMOD p])).card : ℝ) /
          (((p - 1 : ℕ) : ℝ) * (p + 1 : ℝ)) +
        2 * (((Finset.range (p - 1)).filter (fun m =>
          b * centralTrinomial a b m ≡ centralTrinomial a b (m + 1)
            [ZMOD p])).card : ℝ) /
          (((p - 1 : ℕ) : ℝ) * (p : ℝ) * (p + 1 : ℝ)))
    ({n | (generalizedMotzkin a b n : ZMod p) = z} : Set ℕ).HasDensity
      ((1 - D₀) / ((p - 1 : ℕ) : ℝ))

/-- **Zero density of Motzkin numbers modulo a prime.** Let $p$ be a prime, and write
$M_n = M^{(1,1)}_n$ for the Motzkin numbers and $T_r = T^{(1,1)}_r$ for the central trinomial
coefficients. If $T_r \equiv 0 \pmod p$ for some $r < p$, then the set of $n \in \mathbb{N}$ with
$M_n \equiv 0 \pmod p$ has natural density $1$. If instead $T_r \not\equiv 0 \pmod p$ for every
$r < p$ and $p > 2$, let $A$ be the number of $r < p - 2$ with $M_r \equiv 0 \pmod p$, let $B$ be
the number of $m < p - 1$ with $T_m \equiv T_{p-1} T_{m+1} \pmod p$, and let $C$ be the number of
$m < p - 1$ with $T_m \equiv T_{m+1} \pmod p$; then this set has natural density
$$D_0 = \frac{A}{p} + \frac{2B}{(p-1)(p+1)} + \frac{2C}{(p-1)p(p+1)},$$
and $D_0 \ge \frac{2}{p(p-1)}$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Corollary 4. The paper's conjecture-conditional middle clause is
omitted. -/
public theorem_wanted motzkin_zero_density
    (p : ℕ) (hp : p.Prime) :
    ((∃ r < p, centralTrinomial 1 1 r ≡ 0 [ZMOD p]) →
      ({n | generalizedMotzkin 1 1 n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity 1) ∧
    ((∀ r < p, ¬(centralTrinomial 1 1 r ≡ 0 [ZMOD p])) → 2 < p →
      let D₀ :=
        ((((Finset.range (p - 2)).filter
            (fun r => generalizedMotzkin 1 1 r ≡ 0 [ZMOD p])).card : ℝ) /
            (p : ℝ) +
          2 * (((Finset.range (p - 1)).filter (fun m =>
            centralTrinomial 1 1 m ≡
              centralTrinomial 1 1 (p - 1) * centralTrinomial 1 1 (m + 1)
              [ZMOD p])).card : ℝ) /
            (((p - 1 : ℕ) : ℝ) * (p + 1 : ℝ)) +
          2 * (((Finset.range (p - 1)).filter (fun m =>
            centralTrinomial 1 1 m ≡ centralTrinomial 1 1 (m + 1)
              [ZMOD p])).card : ℝ) /
            (((p - 1 : ℕ) : ℝ) * (p : ℝ) * (p + 1 : ℝ)))
      ({n | generalizedMotzkin 1 1 n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity D₀ ∧
        2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) ≤ D₀)

/-- **Zero density of A005717 modulo a prime.** Let $p$ be a prime, let $T_m$ be the central
trinomial coefficient, the constant term of $(x^{-1} + 1 + x)^m$, and let $a_n$ be the constant
term of $x (x^{-1} + 1 + x)^n$ (OEIS A005717). If $T_r \equiv 0 \pmod p$ for some $r < p$, then
the set of $n \in \mathbb{N}$ with $a_n \equiv 0 \pmod p$ has natural density $1$. If instead
$T_r \not\equiv 0 \pmod p$ for every $r < p$ and $p > 2$, let $N_1$ be the number of $m < p - 1$
with $T_m \equiv T_{p-1} T_{m+1} \pmod p$ and let $N_2$ be the number of $m < p - 1$ with
$T_m \equiv T_{m+1} \pmod p$. Then that set has natural density
$D_0 = (N_1 + p N_2) / ((p - 1)(p + 1))$, and $D_0 \ge 1/(p - 1)$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Proposition 6. -/
public theorem_wanted a005717_zero_density
    (p : ℕ) (hp : p.Prime) :
    ((∃ r < p, centralTrinomial 1 1 r ≡ 0 [ZMOD p]) →
      ({n | a005717 n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity 1) ∧
    ((∀ r < p, ¬(centralTrinomial 1 1 r ≡ 0 [ZMOD p])) → 2 < p →
      let D₀ :=
        ((((Finset.range (p - 1)).filter (fun m =>
            centralTrinomial 1 1 m ≡
              centralTrinomial 1 1 (p - 1) * centralTrinomial 1 1 (m + 1)
              [ZMOD p])).card : ℝ) +
          p * (((Finset.range (p - 1)).filter (fun m =>
            centralTrinomial 1 1 m ≡ centralTrinomial 1 1 (m + 1)
              [ZMOD p])).card : ℝ)) /
          (((p - 1 : ℕ) : ℝ) * (p + 1 : ℝ))
      ({n | a005717 n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity D₀ ∧
        1 / ((p - 1 : ℕ) : ℝ) ≤ D₀)

/-- **Zero density of Riordan numbers modulo a prime.** Let $p$ be a prime, and write $r_n$ for the
Riordan numbers and $T_m = T^{(1,1)}_m$ for the central trinomial coefficients. If
$T_m \equiv 0 \pmod p$ for some $m < p$, then the set of $n \in \mathbb{N}$ with
$r_n \equiv 0 \pmod p$ has natural density $1$. If instead $T_m \not\equiv 0 \pmod p$ for every
$m < p$ and $p > 2$, let $B$ be the number of $m < p - 1$ with
$3 T_m \equiv T_{p-1} T_{m+1} \pmod p$ and let $C$ be the number of $m < p - 1$ with
$3 T_m \equiv T_{m+1} \pmod p$; then this set has natural density
$$D_0 = \frac{B + pC}{(p-1)(p+1)},$$
and $D_0 \ge \frac{1}{p-1}$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Proposition 7. -/
public theorem_wanted riordan_zero_density
    (p : ℕ) (hp : p.Prime) :
    ((∃ r < p, centralTrinomial 1 1 r ≡ 0 [ZMOD p]) →
      ({n | riordanNumber n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity 1) ∧
    ((∀ r < p, ¬(centralTrinomial 1 1 r ≡ 0 [ZMOD p])) → 2 < p →
      let D₀ :=
        ((((Finset.range (p - 1)).filter (fun m =>
            3 * centralTrinomial 1 1 m ≡
              centralTrinomial 1 1 (p - 1) * centralTrinomial 1 1 (m + 1)
              [ZMOD p])).card : ℝ) +
          p * (((Finset.range (p - 1)).filter (fun m =>
            3 * centralTrinomial 1 1 m ≡ centralTrinomial 1 1 (m + 1)
              [ZMOD p])).card : ℝ)) /
          (((p - 1 : ℕ) : ℝ) * (p + 1 : ℝ))
      ({n | riordanNumber n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity D₀ ∧
        1 / ((p - 1 : ℕ) : ℝ) ≤ D₀)

/-- **Zero density of A005773 modulo a prime.** Let $p$ be a prime, let $T_m$ be the central
trinomial coefficient, the constant term of $(x^{-1} + 1 + x)^m$, and let $a_n$ be the constant
term of $(1 + x)(x^{-1} + 1 + x)^n$ (OEIS A005773). If $T_r \equiv 0 \pmod p$ for some $r < p$,
then the set of $n \in \mathbb{N}$ with $a_n \equiv 0 \pmod p$ has natural density $1$. If
instead $T_r \not\equiv 0 \pmod p$ for every $r < p$ and $p > 2$, let $N_1$ be the number of
$m < p - 1$ with $T_m \equiv -T_{p-1} T_{m+1} \pmod p$ and let $N_2$ be the number of
$m < p - 1$ with $T_m \equiv -T_{m+1} \pmod p$. Then that set has natural density
$D_0 = (N_1 + p N_2) / ((p - 1)(p + 1))$, and $D_0 \ge 1/(p - 1)$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Proposition 8. -/
public theorem_wanted a005773_zero_density
    (p : ℕ) (hp : p.Prime) :
    ((∃ r < p, centralTrinomial 1 1 r ≡ 0 [ZMOD p]) →
      ({n | a005773 n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity 1) ∧
    ((∀ r < p, ¬(centralTrinomial 1 1 r ≡ 0 [ZMOD p])) → 2 < p →
      let D₀ :=
        ((((Finset.range (p - 1)).filter (fun m =>
            centralTrinomial 1 1 m ≡
              -(centralTrinomial 1 1 (p - 1) * centralTrinomial 1 1 (m + 1))
              [ZMOD p])).card : ℝ) +
          p * (((Finset.range (p - 1)).filter (fun m =>
            centralTrinomial 1 1 m ≡ -centralTrinomial 1 1 (m + 1)
              [ZMOD p])).card : ℝ)) /
          (((p - 1 : ℕ) : ℝ) * (p + 1 : ℝ))
      ({n | a005773 n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity D₀ ∧
        1 / ((p - 1 : ℕ) : ℝ) ≤ D₀)

end

end MetaMathlibExt
