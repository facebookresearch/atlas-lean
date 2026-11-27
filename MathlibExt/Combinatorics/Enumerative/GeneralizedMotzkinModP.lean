/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.FieldTheory.Finite.Basic
public import MathlibExt.Combinatorics.Enumerative.GeneralizedMotzkinCentralTrinomial

/-!
# Digit congruences for constant terms of Laurent polynomial powers

For a prime `p` and a Laurent polynomial supported in the interval from `-1` to `1`, appending
a base-`p` digit to the exponent multiplies the constant term modulo `p` by its digit factor.
Iterating gives the product over all digits, including for the central trinomial coefficients.
-/

namespace MetaMathlibExt

open LaurentPolynomial

/-- **Laurent polynomials of degree at most one.** For integers $\alpha, \beta, \gamma$, this is the
Laurent polynomial $\alpha x^{-1} + \beta + \gamma x$ with integer coefficients.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Lemma 1. The degree-one hypotheses of Lemma 1 are imposed on the
coefficients in the statements that use this polynomial. -/
@[expose] public noncomputable def linearLaurent (α β γ : ℤ) : LaurentPolynomial ℤ :=
  C α * T (-1) + C β + C γ * T 1

namespace constantTermLinearCombination_small_last_digit

/-- Each multiplication by the trinomial moves an exponent by at most one. -/
private theorem coeff_pow_eq_zero (α β γ : ℤ) (r : ℕ) (j : ℤ) (hj : r < j.natAbs) :
    (linearLaurent α β γ ^ r).coeff j = 0 := by
  induction r generalizing j with
  | zero =>
    have hj' : j ≠ 0 := Int.natAbs_pos.mp hj
    change (Finsupp.single (0 : ℤ) (1 : ℤ)) j = 0
    exact Finsupp.single_eq_of_ne hj'
  | succ r ih =>
    rw [pow_succ]
    nth_rw 2 [linearLaurent]
    rw [← single_eq_C_mul_T α (-1), ← single_eq_C_mul_T γ 1, ← single_eq_C β]
    simp only [mul_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, AddMonoidAlgebra.coeff_mul_single_apply]
    rw [ih _ (by omega), ih _ (by omega), ih _ (by omega)]
    simp

/-- In characteristic `p`, only the constant monomial of `f` can contribute when the
exponents of `g` have absolute value less than `p`. -/
private theorem coeff_zero_pow_prime_mul {p : ℕ} [Fact p.Prime]
    (f g : LaurentPolynomial (ZMod p)) (hg : ∀ j : ℤ, p ≤ j.natAbs → g.coeff j = 0) :
    (f ^ p * g).coeff 0 = f.coeff 0 * g.coeff 0 := by
  let : CharP (LaurentPolynomial (ZMod p)) p :=
    charP_of_injective_ringHom (f := C) AddMonoidAlgebra.single_right_injective p
  induction f using LaurentPolynomial.induction_on' with
  | add f₁ f₂ h₁ h₂ =>
    simp only [add_pow_char, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h₁, h₂]
  | C_mul_T j v =>
    rw [← single_eq_C_mul_T, AddMonoidAlgebra.single_pow,
      AddMonoidAlgebra.coeff_single_mul_apply, ZMod.pow_card, nsmul_eq_mul, add_zero]
    by_cases hj : j = 0
    · simp [hj]
    · rw [hg _ (by
        simpa only [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast] using
          Nat.le_mul_of_pos_right p (Int.natAbs_pos.mpr hj))]
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right hj, mul_zero,
        zero_mul]

/-- Appending one digit to the exponent multiplies the constant term by its digit factor. -/
private theorem append_digit (α β γ : ℤ) {p : ℕ} (hp : p.Prime) (u d : ℕ) (hd : d < p) :
    let f := linearLaurent α β γ
    (f ^ (u * p + d)).coeff 0 ≡ (f ^ u).coeff 0 * (f ^ d).coeff 0 [ZMOD p] := by
  intro f
  let : Fact p.Prime := ⟨hp⟩
  let reduce := AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom (ZMod p))
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_mul]
  change (reduce (f ^ (u * p + d))).coeff 0 =
    (reduce (f ^ u)).coeff 0 * (reduce (f ^ d)).coeff 0
  rw [pow_add, pow_mul, map_mul, map_pow]
  apply coeff_zero_pow_prime_mul
  intro j hj
  change ((f ^ d).coeff j : ZMod p) = 0
  rw [coeff_pow_eq_zero _ _ _ _ _ (hd.trans_le hj), Int.cast_zero]

end constantTermLinearCombination_small_last_digit

set_option linter.unusedVariables false in
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
public theorem constantTermLinearCombination_small_last_digit
    (α β γ : ℤ) (hdegree : α ≠ 0 ∨ γ ≠ 0) (c : ℕ → ℤ)
    (h p q m k n₀ n : ℕ) (hp : p.Prime) (hph : h < p)
    (hm : m < p) (hn₀ : n₀ < p) (hmne : m ≠ p - 1)
    (hnsmall : n₀ < p - h)
    (hn : n = ((q * p + m) * p ^ k + (p ^ k - 1)) * p + n₀) :
    let a := fun r : ℕ => (linearLaurent α β γ ^ r).coeff 0
    let b := fun r : ℕ => ∑ i ∈ Finset.range (h + 1), c i * a (r + i)
    (b n ≡ a q * a m * a (p - 1) ^ k *
        (∑ i ∈ Finset.range (h + 1), c i * a (n₀ + i)) [ZMOD p]) ∧
      (b n ≡ a ((n - n₀) / p) * b n₀ [ZMOD p]) := by
  intro a b
  let highDigits (j : ℕ) := (q * p + m) * p ^ j + (p ^ j - 1)
  have digit (u d : ℕ) (hd : d < p) : a (u * p + d) ≡ a u * a d [ZMOD p] :=
    constantTermLinearCombination_small_last_digit.append_digit α β γ hp u d hd
  have hHighDigits (j : ℕ) : a (highDigits j) ≡ a q * a m * a (p - 1) ^ j [ZMOD p] := by
    induction j with
    | zero => simpa [highDigits] using digit q m hm
    | succ j ih =>
      have hpow := Nat.sub_add_cancel (Nat.one_le_pow j p hp.pos)
      have hmul := congrArg (· * p) hpow
      simp only [Nat.add_mul, Nat.one_mul] at hmul
      have hs : highDigits (j + 1) = highDigits j * p + (p - 1) := by
        simp only [highDigits, pow_succ, Nat.add_mul, Nat.mul_assoc]
        omega
      rw [hs, pow_succ, ← mul_assoc]
      exact (digit _ _ (Nat.sub_lt hp.pos Nat.one_pos)).trans (ih.mul_right _)
  have hshift : b n ≡ a (highDigits k) * b n₀ [ZMOD p] := by
    dsimp only [b]
    rw [Finset.mul_sum]
    apply Int.ModEq.sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show n + i = highDigits k * p + (n₀ + i) by rw [hn, Nat.add_assoc]]
    simpa only [mul_left_comm] using (digit (highDigits k) (n₀ + i) (by omega)).mul_left (c i)
  refine ⟨hshift.trans ((hHighDigits k).mul_right _), ?_⟩
  simpa only [hn, Nat.add_sub_cancel, Nat.mul_div_cancel _ hp.pos, highDigits] using hshift

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
public theorem constantTerm_linearLaurent_pow_digits (α β γ a b : ℤ) (p n : ℕ)
    (hp : p.Prime) :
    (linearLaurent α β γ ^ n).coeff 0 ≡
        ((Nat.digits p n).map fun d => (linearLaurent α β γ ^ d).coeff 0).prod [ZMOD p] ∧
      centralTrinomial a b n ≡
        ((Nat.digits p n).map fun d => centralTrinomial a b d).prod [ZMOD p] := by
  have digits (x y z : ℤ) (m : ℕ) :
      (linearLaurent x y z ^ m).coeff 0 ≡
        ((p.digits m).map fun d => (linearLaurent x y z ^ d).coeff 0).prod [ZMOD p] := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      rcases eq_or_ne m 0 with rfl | hm
      · simp [AddMonoidAlgebra.one_def, -single_eq_C_mul_T]
      · rw [Nat.digits_eq_cons_digits_div hp.one_lt hm, List.map_cons, List.prod_cons, mul_comm]
        have step := constantTermLinearCombination_small_last_digit.append_digit
          x y z hp (m / p) (m % p) (Nat.mod_lt _ hp.pos)
        simpa only [Nat.div_add_mod'] using
          step.trans ((ih (m / p) (Nat.div_lt_self (Nat.pos_of_ne_zero hm) hp.one_lt)).mul_right _)
  exact ⟨digits α β γ n, digits a b a n⟩

end MetaMathlibExt
