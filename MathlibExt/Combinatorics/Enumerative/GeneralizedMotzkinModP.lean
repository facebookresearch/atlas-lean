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
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
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

section

open Polynomial

/-- Multiplying by `X^n` shifts the Laurent constant term to the middle coefficient. -/
private theorem centralTrinomial_cast_eq_coeff (a b : ℤ) (p n : ℕ) :
    (centralTrinomial a b n : ZMod p) =
      ((Polynomial.C (a : ZMod p) * X ^ 2 + Polynomial.C (b : ZMod p) * X +
        Polynomial.C (a : ZMod p)) ^ n).coeff n := by
  let P : (ZMod p)[X] :=
    Polynomial.C (a : ZMod p) * X ^ 2 + Polynomial.C (b : ZMod p) * X + Polynomial.C (a : ZMod p)
  let reduce := AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom (ZMod p))
  have hmap : reduce (trinomialLaurent a b) =
      LaurentPolynomial.C (a : ZMod p) * T (-1) + LaurentPolynomial.C (b : ZMod p) +
        LaurentPolynomial.C (a : ZMod p) * T 1 := by
    unfold trinomialLaurent
    rw [← single_eq_C_mul_T a (-1), ← single_eq_C_mul_T a 1, ← single_eq_C b]
    simp only [reduce, map_add, AddMonoidAlgebra.mapRingHom_single]
    simp only [single_eq_C_mul_T, T_zero, mul_one]
    rfl
  have hshift : P.toLaurent = reduce (trinomialLaurent a b) * T 1 := by
    rw [hmap]
    simp only [P, map_add, toLaurent_C_mul_eq, toLaurent_X_pow, toLaurent_X, toLaurent_C,
      add_mul, mul_T_assoc]
    norm_num
    ac_rfl
  have hpow : (P ^ n).toLaurent = reduce (trinomialLaurent a b ^ n) * T n := by
    rw [map_pow, hshift, mul_pow, ← map_pow, T_pow, mul_one]
  have h := congrArg (fun f : LaurentPolynomial (ZMod p) => f.coeff (n : ℤ)) hpow
  change (P ^ n).toLaurent.coeff (Nat.castEmbedding n) = _ at h
  rw [coeff_toLaurent, Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective] at h
  change (P ^ n).coeff n = _ at h
  rw [T, AddMonoidAlgebra.coeff_mul_single_apply, add_neg_cancel, mul_one] at h
  change (P ^ n).coeff n = (AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom (ZMod p))
    (trinomialLaurent a b ^ n)).coeff 0 at h
  rw [AddMonoidAlgebra.coeff_mapRingHom] at h
  exact h.symm

/-- Up to degree `2(p-1)`, precisely two power sums contribute to the sum of evaluations. -/
private theorem sum_eval_eq_neg_coeffs {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X])
    (hf : f.natDegree ≤ 2 * (p - 1)) :
    (∑ x : ZMod p, f.eval x) = -f.coeff (p - 1) - f.coeff (2 * (p - 1)) := by
  let m := p - 1
  have hm : 0 < m := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hsmall (i : ℕ) (hi : i < m) : (∑ x : ZMod p, x ^ i) = 0 :=
    FiniteField.sum_pow_lt_card_sub_one _ i (by rwa [ZMod.card])
  have hshift (i : ℕ) (hi : 0 < i) : (∑ x : ZMod p, x ^ (m + i)) = ∑ x : ZMod p, x ^ i := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = 0
    · simp [hx, hi.ne']
    · rw [pow_add, ZMod.pow_card_sub_one_eq_one hx, one_mul]
  have hmSum : (∑ x : ZMod p, x ^ m) = -1 := by
    calc
      (∑ x : ZMod p, x ^ m) = ∑ x : ZMod p, ((1 : ZMod p) - if x = 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = 0 <;> simp [m, ZMod.pow_card_sub_one, hx]
      _ = _ := by simp [Finset.sum_sub_distrib, ZMod.card]
  have hsum (i : ℕ) (hi : i ≤ 2 * m) :
      f.coeff i * (∑ x : ZMod p, x ^ i) =
        (if i = m then -f.coeff i else 0) + (if i = 2 * m then -f.coeff i else 0) := by
    by_cases h₁ : i = m
    · subst i
      simp [hmSum, show m ≠ 2 * m by omega]
    by_cases h₂ : i = 2 * m
    · subst i
      simp only [ite_eq_right h₁, ite_true, zero_add]
      rw [show 2 * m = m + m by omega, hshift m hm, hmSum, mul_neg_one]
    rw [ite_eq_right h₁, ite_eq_right h₂, add_zero]
    have hzero : (∑ x : ZMod p, x ^ i) = 0 := by
      by_cases h : i < m
      · exact hsmall i h
      calc
        _ = ∑ x : ZMod p, x ^ (i - m) := by
          simpa only [show m + (i - m) = i by omega] using hshift (i - m) (by omega)
        _ = 0 := hsmall (i - m) (by omega)
    rw [hzero, mul_zero]
  change _ = -f.coeff m - f.coeff (2 * m)
  simp_rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hf)]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i hi => hsum i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))),
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [Finset.mem_range, show m < 2 * m + 1 by omega, sub_eq_add_neg]

/-- Fermat evaluation sums the indicator of the nonroots of the quadratic. -/
private theorem sum_quadratic_pow {p : ℕ} [Fact p.Prime] (a b : ZMod p) :
    (∑ x : ZMod p, (a * (x * x) + b * x + a) ^ (p - 1)) =
      -(∑ x : ZMod p, if a * (x * x) + b * x + a = 0 then 1 else 0) := by
  simp_rw [ZMod.pow_card_sub_one]
  have h (x : ZMod p) : (if a * (x * x) + b * x + a ≠ 0 then 1 else 0) =
      (1 : ZMod p) - (if a * (x * x) + b * x + a = 0 then 1 else 0) := by
    by_cases hx : a * (x * x) + b * x + a = 0 <;> simp [hx]
  simp_rw [h, Finset.sum_sub_distrib]
  simp [ZMod.card]

/-- **Squared central trinomial coefficient at one less than a prime.** Let $a, b$ be integers,
let $T_n$ be the constant term of $(a x^{-1} + b + a x)^n$, and let $p$ be a prime with
$b^2 - 4a^2 \not\equiv 0 \pmod p$. Then $T_{p-1}^2 \equiv 1 \pmod p$.

This is the source's Corollary 2 in an equivalent squared form, which avoids an inverse residue
modulo $p$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Corollary 2. -/
public theorem centralTrinomial_prime_minus_one_sq
    (a b : ℤ) (p : ℕ) (hp : p.Prime)
    (hdisc : ¬(b ^ 2 - 4 * a ^ 2 ≡ 0 [ZMOD p])) :
    centralTrinomial a b (p - 1) ^ 2 ≡ 1 [ZMOD p] := by
  let : Fact p.Prime := ⟨hp⟩
  let A : ZMod p := a
  let B : ZMod p := b
  let Q : (ZMod p)[X] := Polynomial.C A * X ^ 2 + Polynomial.C B * X + Polynomial.C A
  have hd : discrim A B A ≠ 0 := by
    rw [← ZMod.intCast_eq_intCast_iff] at hdisc
    push_cast at hdisc
    simpa only [discrim, pow_two, mul_assoc, A, B] using hdisc
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_pow, Int.cast_one, centralTrinomial_cast_eq_coeff]
  change ((Q ^ (p - 1)).coeff (p - 1)) ^ 2 = 1
  rcases hp.two_le.eq_or_lt with rfl | hp2
  · have h4 : (4 : ZMod 2) = 0 := by
      exact (ZMod.natCast_eq_zero_iff 4 2).mpr (by decide)
    have hB : B ≠ 0 := by
      intro hB
      exact hd (by simp [discrim, hB, h4])
    have hcoeff : Q.coeff 1 = B := by
      simp [Q, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    change ((Q ^ 1).coeff 1) ^ 2 = 1
    rw [pow_one, hcoeff, show B = 1 by simpa using ZMod.pow_card_sub_one_eq_one hB, one_pow]
  by_cases hA : A = 0
  · have hB : B ≠ 0 := by
      intro hB
      exact hd (by simp [discrim, hA, hB])
    have hQ : Q = Polynomial.C B * X := by simp [Q, hA]
    rw [hQ, mul_pow, ← (Polynomial.C (R := ZMod p)).map_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, ite_eq_left rfl, mul_one, ZMod.pow_card_sub_one_eq_one hB, one_pow]
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact fun h => (not_le_of_gt hp2) (Nat.le_of_dvd (by decide)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  let : NeZero (2 : ZMod p) := ⟨htwo⟩
  have hQdeg : Q.natDegree ≤ 2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · exact Polynomial.natDegree_C_mul_X_pow_le A 2
      · simpa only [pow_one] using
          (Polynomial.natDegree_C_mul_X_pow_le B 1).trans (by decide : 1 ≤ 2)
    · simp
  have htop : (Q ^ (p - 1)).coeff (2 * (p - 1)) = 1 := by
    rw [Nat.mul_comm 2, Polynomial.coeff_pow_of_natDegree_le hQdeg]
    have h : Q.coeff 2 = A := by
      simp [Q, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [h, ZMod.pow_card_sub_one_eq_one hA]
  have hEval := sum_eval_eq_neg_coeffs (Q ^ (p - 1))
    (by simpa only [Nat.mul_comm 2] using Polynomial.natDegree_pow_le_of_le (p - 1) hQdeg)
  have hEvalQ (x : ZMod p) : Q.eval x = A * (x * x) + B * x + A := by simp [Q, pow_two]
  simp_rw [Polynomial.eval_pow, hEvalQ, htop] at hEval
  rw [sum_quadratic_pow] at hEval
  -- A nonzero discriminant gives either two distinct roots or none.
  by_cases hs : ∃ s : ZMod p, discrim A B A = s * s
  · obtain ⟨s, hs⟩ := hs
    let u := (-B + s) / (2 * A)
    let v := (-B - s) / (2 * A)
    have hs0 : s ≠ 0 := by
      intro h
      exact hd (by simp [hs, h])
    have huv : u ≠ v := by
      intro h
      have h' := (div_left_inj₀ (mul_ne_zero htwo hA)).mp h
      apply mul_ne_zero htwo hs0
      linear_combination h'
    have hind (x : ZMod p) :
        (if A * (x * x) + B * x + A = 0 then 1 else 0 : ZMod p) =
          (if x = u then 1 else 0) + (if x = v then 1 else 0) := by
      have hroot : A * (x * x) + B * x + A = 0 ↔ x = u ∨ x = v :=
        quadratic_eq_zero_iff hA hs x
      by_cases hu : x = u
      · have hv : x ≠ v := hu ▸ huv
        rw [ite_eq_left (hroot.mpr (Or.inl hu)), ite_eq_left hu, ite_eq_right hv, add_zero]
      · by_cases hv : x = v
        · rw [ite_eq_left (hroot.mpr (Or.inr hv)), ite_eq_right hu, ite_eq_left hv, zero_add]
        · rw [ite_eq_right (fun h => (hroot.mp h).elim hu hv),
            ite_eq_right hu, ite_eq_right hv, zero_add]
    simp_rw [hind, Finset.sum_add_distrib, Fintype.sum_ite_eq'] at hEval
    have h : (Q ^ (p - 1)).coeff (p - 1) = 1 := by linear_combination hEval
    rw [h, one_pow]
  · have hroot (x : ZMod p) : A * (x * x) + B * x + A ≠ 0 := by
      intro h
      apply hs
      exact ⟨2 * A * x + B, by simpa only [pow_two] using discrim_eq_sq_of_quadratic_eq_zero h⟩
    simp only [ite_eq_right (hroot _), Finset.sum_const_zero, neg_zero] at hEval
    have h : (Q ^ (p - 1)).coeff (p - 1) = -1 := by linear_combination hEval
    rw [h, neg_sq, one_pow]

end

end MetaMathlibExt
