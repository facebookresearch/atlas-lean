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

/-- The symmetric Laurent polynomial `a x⁻¹ + b + a x` used to define the generalized central
trinomial coefficients and Motzkin numbers. Source: Nadav Kohen, *Density and Symmetry in the
Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Definitions. -/
public noncomputable def trinomialLaurent (a b : ℤ) : LaurentPolynomial ℤ :=
  C a * T (-1) + C b + C a * T 1

/-- The general degree-at-most-one Laurent polynomial `α x⁻¹ + β + γ x`; the degree-one hypotheses
in Lemma 1 are imposed on the coefficients at the theorem statement. Source: Nadav Kohen, *Density
and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Lemma
1. -/
public noncomputable def linearLaurent (α β γ : ℤ) : LaurentPolynomial ℤ :=
  C α * T (-1) + C β + C γ * T 1

/-- The generalized central trinomial coefficient `T⁽ᵃᐟᵇ⁾ₙ`, defined as the constant term of
`(a x⁻¹ + b + a x)ⁿ`. Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers
Modulo p*, INTEGERS 26 (2026), Article A22, Definitions. -/
public noncomputable def centralTrinomial (a b : ℤ) (n : ℕ) : ℤ :=
  (trinomialLaurent a b ^ n).coeff 0

/-- The generalized Motzkin number `M⁽ᵃᐟᵇ⁾ₙ`, defined as the constant term of
`(a x⁻¹ + b + a x)ⁿ (1 - x²)`. Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin
Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Definitions. -/
public noncomputable def generalizedMotzkin (a b : ℤ) (n : ℕ) : ℤ :=
  (trinomialLaurent a b ^ n * (1 - T 2)).coeff 0

/-- OEIS A005717, defined as the constant term of `(x⁻¹ + 1 + x)ⁿ x`. Source: Nadav Kohen, *Density
and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22,
Definitions. -/
public noncomputable def a005717 (n : ℕ) : ℤ :=
  (trinomialLaurent 1 1 ^ n * T 1).coeff 0

/-- OEIS A005773, defined as the constant term of `(x⁻¹ + 1 + x)ⁿ (1 + x)`. Source: Nadav Kohen,
*Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22,
Definitions. -/
public noncomputable def a005773 (n : ℕ) : ℤ :=
  (trinomialLaurent 1 1 ^ n * (1 + T 1)).coeff 0

/-- The first five powers of x⁻¹ + 1 + x, expanded as finitely supported Laurent coefficients. This
computational bridge is used only to prove the three requested finite characteristic-value lemmas.
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

/-- The first five generalized central trinomial coefficients at `a = b = 1` are `1, 1, 3, 7, 19`.
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

/-- The first five generalized Motzkin numbers at `a = b = 1` are `1, 1, 2, 4, 9`. Source: Nadav
Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026),
Article A22, Definitions. -/
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

/-- Proposition 1: for integers a, b and natural n, the generalized Motzkin number is related to
three consecutive generalized central trinomial coefficients by the displayed identity. The a = b =
1 specialization is omitted because it follows by substitution. Source: Nadav Kohen, *Density and
Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Proposition
1. -/
public theorem_wanted generalizedMotzkin_centralTrinomial_relation
    (a b : ℤ) (n : ℕ) :
    2 * a ^ 2 * generalizedMotzkin a b n =
      (4 * a ^ 2 - b ^ 2) * centralTrinomial a b n +
        2 * b * centralTrinomial a b (n + 1) -
          centralTrinomial a b (n + 2)

/-- Proposition 2: the generalized central trinomial recurrence is stated at the paper's index n +
2, so every subscript is nonnegative and no natural subtraction truncates. Source: Nadav Kohen,
*Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22,
Proposition 2. -/
public theorem_wanted centralTrinomial_recurrence (a b : ℤ) (n : ℕ) :
    (n + 2 : ℤ) * centralTrinomial a b (n + 2) =
      b * (2 * n + 3 : ℤ) * centralTrinomial a b (n + 1) -
        (b ^ 2 - 4 * a ^ 2) * (n + 1 : ℤ) * centralTrinomial a b n

/-- Corollary 1: the generalized Motzkin recurrence is stated at the paper's index n + 2, replacing
its n ≥ 2 hypothesis and avoiding truncated natural subtraction. Source: Nadav Kohen, *Density and
Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Corollary
1. -/
public theorem_wanted generalizedMotzkin_recurrence (a b : ℤ) (n : ℕ) :
    (n + 4 : ℤ) * generalizedMotzkin a b (n + 2) =
      b * (2 * n + 5 : ℤ) * generalizedMotzkin a b (n + 1) -
        (b ^ 2 - 4 * a ^ 2) * (n + 1 : ℤ) * generalizedMotzkin a b n

/-- Theorem 1: for a prime p > 2 and k ≤ (p-1)/2, reflection across p-1 sends T_k to T_(p-1-k) up to
the stated discriminant power. Natural subtraction is safe under the displayed bound. Source: Nadav
Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026),
Article A22, Theorem 1. -/
public theorem_wanted centralTrinomial_mod_prime_symmetry
    (a b : ℤ) (p k : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hk : k ≤ (p - 1) / 2) :
    centralTrinomial a b (p - 1 - k) ≡
      (b ^ 2 - 4 * a ^ 2) ^ ((p - 1) / 2 - k) * centralTrinomial a b k
      [ZMOD p]

/-- Theorem 2: for a prime p > 3 and k ≤ (p-3)/2, reflection across p-3 sends M_k to M_(p-3-k) up to
the stated discriminant power. Natural subtraction is safe under the displayed bound. Source: Nadav
Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026),
Article A22, Theorem 2. -/
public theorem_wanted generalizedMotzkin_mod_prime_symmetry
    (a b : ℤ) (p k : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (hk : k ≤ (p - 3) / 2) :
    generalizedMotzkin a b (p - 3 - k) ≡
      (b ^ 2 - 4 * a ^ 2) ^ ((p - 3) / 2 - k) * generalizedMotzkin a b k
      [ZMOD p]

/-- Corollary 2 in its equivalent squared form: if the discriminant is nonzero modulo the prime p,
then T_(p-1)^2 is congruent to one. This avoids formalizing an inverse residue while retaining the
stated equivalent result. Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin
Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Corollary 2. -/
public theorem_wanted centralTrinomial_prime_minus_one_sq
    (a b : ℤ) (p : ℕ) (hp : p.Prime)
    (hdisc : ¬(b ^ 2 - 4 * a ^ 2 ≡ 0 [ZMOD p])) :
    centralTrinomial a b (p - 1) ^ 2 ≡ 1 [ZMOD p]

/-- Proposition 3: a prime divides the Motzkin number M_(p-2) exactly when its natural residue
modulo 3 is 1. At p = 2 both sides are false because M_0 = 1, so no extra lower bound is added.
Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26
(2026), Article A22, Proposition 3. -/
public theorem_wanted prime_dvd_motzkin_prime_minus_two_iff
    (p : ℕ) (hp : p.Prime) :
    generalizedMotzkin 1 1 (p - 2) ≡ 0 [ZMOD p] ↔ p ≡ 1 [MOD 3]

/-- Proposition 4 (Lucas property): for a prime `p` and a Laurent polynomial `P = αx⁻¹ + β + γx`,
the constant terms `a_n = ct[Pⁿ]` satisfy `a_n ≡ ∏ᵢ a_{(n)_p[i]} (mod p)` over the base-`p` digits
of `n`; in particular `T⁽ᵃᐟᵇ⁾ₙ ≡ ∏ᵢ T⁽ᵃᐟᵇ⁾_{(n)_p[i]} (mod p)`. Digits are `Nat.digits p n` (none
for `n = 0`, where both sides are `1`). The paper assumes `deg P = 1`; the statement is given for
degree at most one (`α`, `γ` arbitrary), which includes it. Source: Nadav Kohen, *Density and
Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Proposition
4. -/
public theorem_wanted constantTerm_linearLaurent_pow_digits (α β γ a b : ℤ) (p n : ℕ)
    (hp : p.Prime) :
    (linearLaurent α β γ ^ n).coeff 0 ≡
        ((Nat.digits p n).map fun d => (linearLaurent α β γ ^ d).coeff 0).prod [ZMOD p] ∧
      centralTrinomial a b n ≡
        ((Nat.digits p n).map fun d => centralTrinomial a b d).prod [ZMOD p]

/-- Lemma 1, full digit decomposition: a r is the constant term of the r-th power of αx⁻¹+β+γx, b r
is its finite shifted linear combination, and C is min h (p-n₀-1). The arithmetic equality is the
supplied encoding of the base-p word; α ≠ 0 ∨ γ ≠ 0 encodes degree one. Source: Nadav Kohen,
*Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22,
Lemma 1. -/
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

/-- Lemma 1, small-last-digit clause: under n₀ < p-h, the full digit formula reduces first to the
displayed product and then to a_((n-n₀)/p) b_(n₀). Both congruences are recorded, and the arithmetic
equality encodes the paper's base-p word. Source: Nadav Kohen, *Density and Symmetry in the
Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Lemma 1. -/
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

/-- Lemma 2, zero case: for a symmetric degree-one Laurent polynomial and a finite shifted linear
combination b, the existence of a zero anywhere in the constant-term sequence forces the zero set of
b to have density one. Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers
Modulo p*, INTEGERS 26 (2026), Article A22, Lemma 2. -/
public theorem_wanted symmetricConstantTerm_zero_density_one
    (α β : ℤ) (hα : α ≠ 0) (c : ℕ → ℤ) (h p : ℕ)
    (hp : p.Prime) (hph : h < p)
    (hzero : ∃ r : ℕ, centralTrinomial α β r ≡ 0 [ZMOD p]) :
    let b := fun r : ℕ =>
      ∑ i ∈ Finset.range (h + 1), c i * centralTrinomial α β (r + i)
    ({r | b r ≡ 0 [ZMOD p]} : Set ℕ).HasDensity 1

/-- Lemma 2, nonzero case: when no a_r vanishes, the zero density of b is the three-term real
expression in the paper. Inclusive finite ranges encode 0 ≤ i ≤ C; pair cardinalities use a product
finset. No p > 2 assumption is added because the displayed real denominators remain meaningful for
every prime. Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo
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

/-- Proposition 5(i): if the last base-p digit n₀ is below p-2, then 2a²M_n factors modulo p as
2a²T_qM_(n₀). The arithmetic equality encodes the base-p word n = q n₀. Source: Nadav Kohen,
*Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22,
Proposition 5(i). -/
public theorem_wanted generalizedMotzkin_digit_below_prime_minus_two
    (a b : ℤ) (p q n₀ n : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hdisc : ¬(b ^ 2 - 4 * a ^ 2 ≡ 0 [ZMOD p]))
    (hn₀ : n₀ < p - 2) (hn : n = q * p + n₀) :
    2 * a ^ 2 * generalizedMotzkin a b n ≡
      2 * a ^ 2 * centralTrinomial a b q * generalizedMotzkin a b n₀
      [ZMOD p]

/-- Proposition 5(ii): for the base-p suffix m (p-1)^k (p-2), with the genuine digit condition m <
p-1, the stated two-term formula gives 2a²M_n modulo p. Source: Nadav Kohen, *Density and Symmetry
in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Proposition 5(ii). -/
public theorem_wanted generalizedMotzkin_digit_prime_minus_two
    (a b : ℤ) (p q m k n : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hdisc : ¬(b ^ 2 - 4 * a ^ 2 ≡ 0 [ZMOD p])) (hm : m < p - 1)
    (hn : n = ((q * p + m) * p ^ k + (p ^ k - 1)) * p + (p - 2)) :
    2 * a ^ 2 * generalizedMotzkin a b n ≡
      centralTrinomial a b q *
        (b * centralTrinomial a b m * centralTrinomial a b (p - 1) ^ (k + 1) -
          centralTrinomial a b (m + 1))
      [ZMOD p]

/-- Proposition 5(iii): for the base-p suffix m (p-1)^k (p-1), ℓ is p-2-m. The paper's possibly
negative unit exponent is replaced by the equivalent multiplied-out nonnegative-exponent form
requested in the task. Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers
Modulo p*, INTEGERS 26 (2026), Article A22, Proposition 5(iii). -/
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

/-- Corollary 3, ordinary last-digit case: under nonvanishing of all T_r for r < p, a number with
last digit n₀ < p-2 has M_n congruent to zero exactly when M_(n₀) is. The base-p word is encoded by
n = qp+n₀. Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Corollary 3. -/
public theorem_wanted generalizedMotzkin_zero_digit_below_prime_minus_two
    (a b : ℤ) (p q n₀ n : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hdisc : ¬(b ^ 2 - 4 * a ^ 2 ≡ 0 [ZMOD p]))
    (hT : ∀ r < p, ¬(centralTrinomial a b r ≡ 0 [ZMOD p]))
    (hn₀ : n₀ < p - 2) (hn : n = q * p + n₀) :
    generalizedMotzkin a b n ≡ 0 [ZMOD p] ↔
      generalizedMotzkin a b n₀ ≡ 0 [ZMOD p]

/-- Corollary 3, last digit p-2: under nonvanishing of the first p central trinomial coefficients,
M_n vanishes exactly when the displayed congruence holds. The arithmetic equality encodes the stated
base-p word. The hypothesis `a ≢ 0 (mod p)` is implicit in the paper, which cancels `2a²`. Source:
Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026),
Article A22, Corollary 3. -/
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

/-- Corollary 3, last digit p-1: with ℓ = p-2-m, M_n vanishes exactly when the displayed congruence
holds. The hypothesis m < p-1 makes m a genuine preceding digit distinct from p-1. The hypothesis
`a ≢ 0 (mod p)` is implicit in the paper, which cancels `2a²`. Source: Nadav Kohen, *Density and
Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Corollary
3. -/
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

/-- Theorem 3, vanishing-central-term case: if one T_r with r < p is zero modulo p, then the indices
at which M_n is zero have asymptotic density one. Source: Nadav Kohen, *Density and Symmetry in the
Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Theorem 3. -/
public theorem_wanted generalizedMotzkin_zero_density_one
    (a b : ℤ) (p : ℕ) (hp : p.Prime)
    (hzero : ∃ r < p, centralTrinomial a b r ≡ 0 [ZMOD p]) :
    ({n | generalizedMotzkin a b n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity 1

/-- Theorem 3, nonvanishing-central-term case: for p > 2, the zero density of M_n is the displayed
D₀; its three cardinals correspond respectively to small last digits and the two boundary
congruences. The hypothesis `a ≢ 0 (mod p)` is implicit in the paper, which cancels `2a²`. Source:
Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026),
Article A22, Theorem 3. -/
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

/-- Theorem 3, nonzero residues: assuming the units represented by the first p central trinomial
values generate (ZMod p)ˣ through Subgroup.closure, every fixed nonzero residue z occurs among M_n
with density (1-D₀)/(p-1). The set of units is expressed extensionally, avoiding a choice of unit
per residue. The hypothesis `a ≢ 0 (mod p)` is implicit in the paper, which cancels `2a²`. Source:
Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026),
Article A22, Theorem 3. -/
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

/-- Corollary 4: ordinary Motzkin zeros have density one when some T_r with r < p vanishes.
Otherwise, for p > 2, their density is the displayed D₀ and D₀ ≥ 2/(p(p-1)). The paper's
conjecture-conditional middle clause is omitted; Theorem 3 above already states it with unit
generation as an explicit hypothesis. Source: Nadav Kohen, *Density and Symmetry in the Generalized
Motzkin Numbers Modulo p*, INTEGERS 26 (2026), Article A22, Corollary 4. -/
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

/-- Proposition 6: the zero set of A005717 has density one if a central trinomial coefficient below
p vanishes. Otherwise, for p > 2, it has the displayed density D₀ and D₀ ≥ 1/(p-1). Source: Nadav
Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*, INTEGERS 26 (2026),
Article A22, Proposition 6. -/
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

/-- Proposition 7: the Riordan zero set has density one if a central trinomial coefficient below p
vanishes. Otherwise, for p > 2, its density uses the two congruences with coefficient 3 and is at
least 1/(p-1). Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo
p*, INTEGERS 26 (2026), Article A22, Proposition 7. -/
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

/-- Proposition 8: the A005773 zero set has density one if a central trinomial coefficient below p
vanishes. Otherwise, for p > 2, its density uses the two congruences with negated right sides and is
at least 1/(p-1). Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers
Modulo p*, INTEGERS 26 (2026), Article A22, Proposition 8. -/
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
