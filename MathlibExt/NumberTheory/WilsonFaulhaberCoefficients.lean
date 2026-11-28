/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.NumberTheory.Padics.PadicNorm

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.NumberTheory.BernoulliPolynomials
import MathlibExt.Algebra.Polynomial.SquareComposition
import MathlibExt.NumberTheory.Bernoulli.SumModPrime
import MathlibExt.NumberTheory.WilsonFermatQuotient

/-!
# Faulhaber coefficients and Wilson's theorem modulo `p^2`

For an odd prime `p = 2l + 1`, the sum of the first `n` `p`-th powers is a polynomial
in `n(n+1)/2`. Its coefficients of degrees `i + 1` for `1 ≤ i ≤ l` are `p`-integral,
and half its quadratic coefficient minus `p` is congruent to `(p - 1)!` modulo `p^2`.
The polynomial is specified by its evaluations at all triangular numbers rather than by a
particular coefficient expansion.

The reflection symmetry of the Bernoulli polynomial about `1/2` gives a polynomial
in the triangular number. For the congruence we use the Bernoulli power-sum argument
following Corollary 1, with the quadratic coefficient identified by differentiation.

## References

* Claire Levaillant, *Wilson's Theorem Modulo p^2 Derived from Faulhaber Polynomials*,
  INTEGERS 24 (2024), Article A87, pp. 1–17, Theorems 1 and 2 and the argument after
  Corollary 1 (§2, pp. 8–9). <https://math.colgate.edu/~integers/y87/y87.pdf>
* T. Clausen, *Theorem*, Astronomische Nachrichten 17, no. 22 (1840), pp. 351–352;
  C. von Staudt, *Beweis eines Lehrsatzes, die Bernoullischen Zahlen betreffend*,
  Journal für die reine und angewandte Mathematik 21 (1840), pp. 372–374
  (the von Staudt–Clausen theorem used for the denominators).
* J. W. L. Glaisher, *On the residues of the sums of products of the first p − 1 numbers and
  their powers, to modulus p^2 or p^3*, Quart. J. Math. 31 (1900), pp. 321–353
  (the Bernoulli form of the Wilson congruence).
* Z-H. Sun, *Congruences concerning Bernoulli numbers and Bernoulli polynomials*,
  Discrete Applied Mathematics 105 (2000), pp. 193–223 (the power-sum reduction to evaluation
  at `p`, credited to Sun by Levaillant on p. 9 before equation (21)).
* `MathlibExt.Algebra.Polynomial.SquareComposition`
  (`Polynomial.expand_contract_of_comp_neg_X_eq`),
  `MathlibExt.NumberTheory.Bernoulli.SumModPrime` (`padicValuation_bernoulli_le_one`), and
  `MathlibExt.NumberTheory.WilsonFermatQuotient`
  (`wilson_mod_prime_sq`, `isCoprime_intCast_of_mem_Icc`).
-/

namespace MathlibExt.NumberTheory.WilsonFaulhaberWanted

open Finset Polynomial
open MetaMathlibExt (padicValuation_bernoulli_le_one)

private noncomputable def powerSumPoly (m : ℕ) : ℚ[X] :=
  C ((m + 1 : ℚ)⁻¹) * (Polynomial.bernoulli (m + 1) - C (_root_.bernoulli (m + 1)))

private noncomputable def triangularPoly : ℚ[X] := C (1 / 2) * X * (X - 1)

private theorem powerSumPoly_eval (m n : ℕ) (hm : m ≠ 0) :
    (powerSumPoly m).eval ((n : ℚ) + 1) = ∑ k ∈ Icc 1 n, (k : ℚ) ^ m := by
  have h := Polynomial.sum_range_pow_eq_bernoulli_sub (n + 1) m
  simp only [Nat.cast_add, Nat.cast_one] at h
  rw [powerSumPoly, eval_mul, eval_C, eval_sub, eval_C, ← h, inv_mul_cancel_left₀ (by positivity)]
  have hs : Icc 1 n = Ico 1 (n + 1) := by ext k; simp
  rw [hs, sum_Ico_eq_sub _ (by omega)]
  simp [hm]

private theorem triangularPoly_eval (n : ℕ) :
    triangularPoly.eval ((n : ℚ) + 1) = ((n * (n + 1) / 2 : ℕ) : ℚ) := by
  have h := Nat.cast_choose_two (K := ℚ) (n + 1)
  rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm (n + 1) n] at h
  rw [h]
  simp only [triangularPoly, eval_mul, eval_C, eval_X, eval_sub, eval_one,
    Nat.cast_add, Nat.cast_one]
  ring

private theorem powerSumPoly_derivative (m : ℕ) :
    (powerSumPoly m).derivative = Polynomial.bernoulli m := by
  rw [powerSumPoly, derivative_C_mul, map_sub, derivative_C, sub_zero,
    derivative_bernoulli_add_one, show (m + 1 : ℚ[X]) = C ((m : ℚ) + 1) by simp,
    ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by positivity), map_one, one_mul]

private theorem powerSumPoly_reflect {m : ℕ} (hm : Even (m + 1)) :
    (powerSumPoly m).comp (1 - X) = powerSumPoly m := by
  simp [powerSumPoly, mul_comp, sub_comp, bernoulli_comp_one_sub_X, hm.neg_one_pow]

private theorem powerSumPoly_coeff_integral {p l : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpl : p = 2 * l + 1) (j : ℕ) : Rat.padicValuation p ((powerSumPoly p).coeff j) ≤ 1 := by
  let v := Rat.padicValuation p
  have hp : p.Prime := Fact.out
  have hp1 : ¬p ∣ p + 1 := fun h => hp.not_dvd_one (by simpa using Nat.dvd_sub h (dvd_refl p))
  have hv_inv (m : ℕ) (hm : ¬ p ∣ m) : v ((m : ℚ)⁻¹) = 1 := by
    have h : v (m : ℚ) = 1 := by
      rw [Rat.padicValuation_natCast, Int.padicValuation_eq_one_iff, Int.natCast_dvd_natCast]
      exact hm
    rw [map_inv₀, h, inv_one]
  have hv_two : v ((2 : ℚ)⁻¹) = 1 := by
    exact_mod_cast hv_inv 2 (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))
  have hv_p : v ((p : ℚ) * _root_.bernoulli (p - 1)) = 1 := by
    have hl : 0 < l := by have := hp.two_le; omega
    have h : p - 1 = 2 * l := by omega
    rw [map_mul, Rat.padicValuation_self, h, Bernoulli.padicValuation_bernoulli hl (by rw [h]),
      ← WithZero.exp_add]
    simp
  -- For a positive coefficient index, only the term with `j = 2` uses `B_(p-1)`.
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [powerSumPoly, coeff_zero_eq_eval_zero]
  simp only [powerSumPoly, coeff_C_mul, coeff_sub, coeff_C, ite_eq_right hj.ne', sub_zero]
  rw [map_mul, ← Nat.cast_add_one, hv_inv _ hp1, one_mul, coeff_bernoulli]
  split_ifs with hjp
  · by_cases h : j = 2
    · subst j
      rw [Nat.cast_choose_two, Nat.cast_add, Nat.cast_one,
        show p + 1 - 2 = p - 1 by omega]
      rw [show _root_.bernoulli (p - 1) * ((p + 1 : ℚ) * (p + 1 - 1) / 2) =
          ((p : ℚ) * _root_.bernoulli (p - 1)) * ((p + 1) * (2 : ℚ)⁻¹) by ring,
        map_mul, hv_p, one_mul, map_mul, hv_two, mul_one, ← Nat.cast_add_one]
      exact_mod_cast Int.padicValuation_le_one p (p + 1 : ℕ)
    · rw [map_mul]
      apply mul_le_one' _ _
      · exact padicValuation_bernoulli_le_one hpl (by omega) (by omega)
      · exact_mod_cast Int.padicValuation_le_one p ((p + 1).choose j)
  · simp

private theorem exists_faulhaber {p l : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpl : p = 2 * l + 1) :
    ∃ F : ℚ[X], F.comp triangularPoly = powerSumPoly p ∧
      ∀ i, Rat.padicValuation p (F.coeff i) ≤ 1 := by
  let G := powerSumPoly p
  let H := G.comp (X + C (1 / 2))
  let U : ℚ[X] := C 2 * X + C (1 / 4)
  let F := (H.contract 2).comp U
  have hsym : G.comp (1 - X) = G := powerSumPoly_reflect ⟨l + 1, by omega⟩
  have href : H.comp (-X) = H := by
    have hhalf : 1 - C (1 / 2 : ℚ) = C (1 / 2) := by
      rw [← map_one C, ← map_sub]
      norm_num
    have h : (1 - X : ℚ[X]).comp (X + C (1 / 2)) = -X + C (1 / 2) := by
      simp only [sub_comp, one_comp, X_comp]
      rw [sub_add_eq_sub_sub_swap, hhalf]
      ring
    calc
      H.comp (-X) = G.comp (-X + C (1 / 2)) := by simp [H, comp_assoc]
      _ = (G.comp (1 - X)).comp (X + C (1 / 2)) := by rw [comp_assoc, h]
      _ = H := by rw [hsym]
  have hU : U.comp triangularPoly = (X - C (1 / 2)) ^ 2 := by
    have h2 : C (2 : ℚ) * C (1 / 2) = 1 := by rw [← map_mul]; norm_num
    have h4 : C (1 / 2 : ℚ) ^ 2 = C (1 / 4) := by rw [← map_pow]; norm_num
    simp only [U, add_comp, mul_comp, C_comp, X_comp, triangularPoly, ← mul_assoc, h2, one_mul]
    rw [sub_sq, h4]
    have hlin : (2 : ℚ[X]) * C (1 / 2) = 1 := by
      rw [← (map_ofNat (C : ℚ →+* ℚ[X]) 2)]
      exact h2
    rw [mul_right_comm (2 : ℚ[X]), hlin, one_mul]
    ring
  refine ⟨F, ?_, ?_⟩
  · have hshift : (X + C (1 / 2) : ℚ[X]).comp (X - C (1 / 2)) = X := by simp
    have hpow : ((X : ℚ[X]) ^ 2).comp (X - C (1 / 2)) = (X - C (1 / 2)) ^ 2 := by simp
    dsimp only [F]
    rw [comp_assoc, hU, ← hpow, ← comp_assoc, ← expand_eq_comp_X_pow,
      expand_contract_of_comp_neg_X_eq href]
    dsimp only [H]
    rw [comp_assoc, hshift, comp_X]
  · let S := (Rat.padicValuation p).integer
    have hG : G ∈ lifts S.subtype := (lifts_iff_coeff_lifts G).mpr fun j =>
      ⟨⟨G.coeff j, ((Rat.padicValuation p).mem_integer_iff _).mpr
        (powerSumPoly_coeff_integral hp2 hpl j)⟩, rfl⟩
    obtain ⟨g, hg⟩ := (mem_lifts G).mp hG
    have hp : p.Prime := Fact.out
    have htwo : ¬p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
    have hinv : (1 / 2 : ℚ) ∈ S := by
      rw [(Rat.padicValuation p).mem_integer_iff, Rat.padicValuation_le_one_iff,
        show (1 / 2 : ℚ).den = 2 by norm_num]
      exact htwo
    let half : S := ⟨1 / 2, hinv⟩
    let U' : S[X] := C 2 * X + C (half ^ 2)
    let H' : S[X] := g.comp (X + C half)
    have hH' : H'.map S.subtype = H := by simp [H', map_comp, hg, H, half]
    have hU' : U'.map S.subtype = U := by
      norm_num [U', U, half]
      rfl
    have hF : ((H'.contract 2).comp U').map S.subtype = F := by
      simp [map_comp, map_contract (by decide : 2 ≠ 0), hH', hU', F]
    intro i
    rw [← hF, coeff_map]
    exact ((Rat.padicValuation p).mem_integer_iff _).mp
      (((H'.contract 2).comp U').coeff i).property

private theorem valuation_le_one_norm {p : ℕ} [Fact p.Prime] {r : ℚ}
    (hr : Rat.padicValuation p r ≤ 1) : padicNorm p r ≤ 1 := by
  have h := Padic.norm_rat_le_one (p := p) (Rat.padicValuation_le_one_iff.mp hr)
  rw [Padic.eq_padicNorm] at h
  exact_mod_cast h

private theorem quadratic_coeff {p l : ℕ} (hp : p.Prime) (hpl : p = 2 * l + 1)
    {F : ℚ[X]} (hF : F.comp triangularPoly = powerSumPoly p) :
    F.coeff 2 / 2 = (p : ℚ) * _root_.bernoulli (p - 1) := by
  have hodd : Odd p := ⟨l, by omega⟩
  have hpgt := hp.one_lt
  have h0 : triangularPoly.eval 0 = 0 := by simp [triangularPoly]
  have h1 : triangularPoly.derivative.eval 0 = -1 / 2 := by
    norm_num [triangularPoly, derivative_mul]
  have h := congrArg derivative hF
  rw [derivative_comp, powerSumPoly_derivative] at h
  have hf1 : F.coeff 1 = 0 := by
    have hc := congrArg (eval 0) h
    simp only [eval_mul, eval_comp, h0, h1, ← coeff_zero_eq_eval_zero, coeff_derivative,
      zero_add] at hc
    rw [coeff_zero_eq_eval_zero, bernoulli_eval_zero, bernoulli_eq_zero_of_odd hodd hpgt] at hc
    norm_num at hc
    linarith
  have hc := congrArg (fun Q : ℚ[X] => Q.derivative.eval 0) h
  simp only [derivative_mul, derivative_comp, eval_add, eval_mul, eval_comp, h0, h1,
    ← coeff_zero_eq_eval_zero, coeff_derivative, Nat.cast_one, zero_add, hf1, mul_zero,
    zero_mul] at hc
  rw [coeff_bernoulli, ite_eq_left hp.one_le, Nat.choose_one_right] at hc
  norm_num at hc ⊢
  linarith

private theorem factorial_sub_power_sum_norm {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    padicNorm p ((Nat.factorial (p - 1) : ℚ) -
        ((∑ k ∈ Icc 1 (p - 1), (k : ℚ) ^ (p - 1)) - p)) ≤ (p : ℚ) ^ (-2 : ℤ) := by
  have hp : p.Prime := Fact.out
  have hq (k : Icc 1 (p - 1)) :
      (p : ZMod (p ^ 2)) *
          (Int.fermatQuotient p hp (k.1 : ℤ) (isCoprime_intCast_of_mem_Icc hp k.2) :
            ZMod (p ^ 2)) = (k.1 : ZMod (p ^ 2)) ^ (p - 1) - 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod (p ^ 2)))
      (Int.natCast_mul_fermatQuotient p hp (k.1 : ℤ) (isCoprime_intCast_of_mem_Icc hp k.2))
  have hs := wilson_mod_prime_sq p hp hp2
  rw [mul_sum] at hs
  simp_rw [hq] at hs
  rw [sum_attach (f := fun k : ℕ => (k : ZMod (p ^ 2)) ^ (p - 1) - 1),
    sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc] at hs
  rw [show p - 1 + 1 - 1 = p - 1 by omega, Nat.cast_sub hp.one_le, Nat.cast_one] at hs
  have hsum : (Nat.factorial (p - 1) : ZMod (p ^ 2)) =
      (∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2)) ^ (p - 1)) - p := by
    rw [hs]; ring
  have hdvd : ((p ^ 2 : ℕ) : ℤ) ∣ ((Nat.factorial (p - 1) : ℤ) -
      ((∑ k ∈ Icc 1 (p - 1), (k : ℤ) ^ (p - 1)) - p)) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    exact sub_eq_zero.mpr hsum
  exact_mod_cast (padicNorm.dvd_iff_norm_le (p := p)).mp hdvd

private theorem power_sum_sub_bernoulli_norm {p l : ℕ} [Fact p.Prime]
    (hpl : p = 2 * l + 1) :
    padicNorm p ((∑ k ∈ Icc 1 (p - 1), (k : ℚ) ^ (p - 1)) -
        (p : ℚ) * _root_.bernoulli (p - 1)) ≤ (p : ℚ) ^ (-2 : ℤ) := by
  have hp : p.Prime := Fact.out
  have hP : 0 < (p : ℚ) := by exact_mod_cast hp.pos
  have hpn : p - 1 + 1 = p := by omega
  have hs : Icc 1 (p - 1) = Ico 1 p := by ext k; simp; omega
  rw [hs, sum_Ico_eq_sub _ hp.one_le]
  simp only [range_one, sum_singleton, Nat.cast_zero,
    zero_pow (Nat.sub_ne_zero_of_lt hp.one_lt), sub_zero]
  rw [_root_.sum_range_pow, hpn, ← Nat.cast_add_one, hpn]
  let a (i : ℕ) := _root_.bernoulli i * (p.choose i : ℚ) * (p : ℚ) ^ (p - i) / p
  change padicNorm p ((∑ i ∈ range p, a i) - _) ≤ _
  have ha : a (p - 1) = (p : ℚ) * _root_.bernoulli (p - 1) := by
    dsimp only [a]
    rw [show p - (p - 1) = 1 by omega, pow_one, mul_div_cancel_right₀ _ hP.ne',
      ← Nat.choose_symm (by omega : p - 1 ≤ p), show p - (p - 1) = 1 by omega,
      Nat.choose_one_right]
    ring
  have hsplit := sum_range_succ a (p - 1)
  rw [hpn] at hsplit
  rw [hsplit, ← ha, add_sub_cancel_right]
  apply padicNorm.sum_le' _ (zpow_nonneg hP.le _)
  intro i hi
  have hi' := mem_range.mp hi
  have hbi := valuation_le_one_norm (padicValuation_bernoulli_le_one hpl
    (j := i) (by omega) (by omega))
  have hterm : ∃ r : ℚ, padicNorm p r ≤ 1 ∧ a i = (p : ℚ) ^ 2 * r := by
    -- If the power of `p` is only two, the binomial coefficient supplies the canceled `p`.
    by_cases h : p - i = 2
    · obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := i) (by omega) (by omega)
      refine ⟨_root_.bernoulli i * c, ?_, ?_⟩
      · rw [padicNorm.mul]
        simpa using mul_le_mul hbi (padicNorm.of_nat c) (padicNorm.nonneg _) zero_le_one
      · dsimp only [a]
        rw [hc, Nat.cast_mul, h]
        field_simp
    · have he : p - i = 2 + (p - i - 3) + 1 := by omega
      refine ⟨_root_.bernoulli i * p.choose i * (p : ℚ) ^ (p - i - 3), ?_, ?_⟩
      · rw [← Nat.cast_pow, mul_assoc, ← Nat.cast_mul, padicNorm.mul]
        simpa using mul_le_mul hbi (padicNorm.of_nat (p := p) (p.choose i * p ^ (p - i - 3)))
          (padicNorm.nonneg _) zero_le_one
      · have hpow : (p : ℚ) ^ (p - i) = ((p : ℚ) ^ 2 * p ^ (p - i - 3)) * p := by
          calc
            _ = (p : ℚ) ^ (2 + (p - i - 3) + 1) := congrArg ((p : ℚ) ^ ·) he
            _ = _ := by rw [pow_succ, pow_add]
        dsimp only [a]
        rw [hpow, ← mul_assoc, mul_div_cancel_right₀ _ hP.ne']
        ring
  obtain ⟨r, hr, hir⟩ := hterm
  rw [hir, padicNorm.mul]
  calc
    _ ≤ padicNorm p ((p : ℚ) ^ 2) * 1 := mul_le_mul_of_nonneg_left hr (padicNorm.nonneg _)
    _ = (p : ℚ) ^ (-2 : ℤ) := by simp [pow_two, zpow_neg]

/-- **Theorem 2**: let `p = 2l + 1` be an odd prime. The Faulhaber polynomial
`F ∈ ℚ[X]` with `∑_{k=1}^{n} k^p = F(n(n+1)/2)` for all `n` exists, and its coefficients
`c_i(l)` of `X^(i+1)` (`1 ≤ i ≤ l`) satisfy (i) `c_i(l) ∈ ℤ_p` and
(ii) `(p - 1)! ≡ c_1(l)/2 - p (mod p^2)`, both read in `ℚ` through the `p`-adic norm.
At `n = p - 1`, the identity evaluates `F` at `a = p(p - 1)/2` as in equation (3)
of the paper, without a separate claim about the degree or which coefficients vanish.

Source: Claire Levaillant, *Wilson's Theorem Modulo p^2 Derived from Faulhaber
Polynomials*, INTEGERS 24 (2024), Article A87, Theorem 2. -/
public theorem faulhaber_coeff_integral_and_wilson (p l : ℕ) (hp : p.Prime)
    (hpl : p = 2 * l + 1) :
    (∃ F : Polynomial ℚ, ∀ n : ℕ,
        ∑ k ∈ Finset.Icc 1 n, (k : ℚ) ^ p = F.eval ((n * (n + 1) / 2 : ℕ) : ℚ)) ∧
      ∀ F : Polynomial ℚ, (∀ n : ℕ,
          ∑ k ∈ Finset.Icc 1 n, (k : ℚ) ^ p = F.eval ((n * (n + 1) / 2 : ℕ) : ℚ)) →
        (∀ i ∈ Finset.Icc 1 l, padicNorm p (F.coeff (i + 1)) ≤ 1) ∧
          padicNorm p ((Nat.factorial (p - 1) : ℚ) - (F.coeff 2 / 2 - p)) ≤
            (p : ℚ) ^ (-2 : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨F, hcomp, hint⟩ := exists_faulhaber hp2 hpl
  have hEval (n : ℕ) := powerSumPoly_eval p n hp.ne_zero
  refine ⟨⟨F, fun n => ?_⟩, fun Q hQ => ?_⟩
  · have hn := hEval n
    rw [← hcomp, eval_comp, triangularPoly_eval] at hn
    exact hn.symm
  have hQcomp : Q.comp triangularPoly = powerSumPoly p := by
    apply eq_of_infinite_eval_eq
    refine (Set.infinite_range_of_injective (f := fun n : ℕ => (n : ℚ) + 1) ?_).mono ?_
    · intro a b h
      exact_mod_cast add_right_cancel h
    · rintro _ ⟨n, rfl⟩
      change (Q.comp triangularPoly).eval ((n : ℚ) + 1) = _
      rw [eval_comp, triangularPoly_eval, hEval]
      exact (hQ n).symm
  have hEQ : Q = F := by
    have hzero : (Q - F).comp triangularPoly = 0 := by rw [sub_comp, hQcomp, hcomp, sub_self]
    apply sub_eq_zero.mp
    refine (comp_eq_zero_iff.mp hzero).resolve_right fun ⟨_, hc⟩ => ?_
    have h0 := congrArg (eval (0 : ℚ)) hc
    have h2 := congrArg (eval (2 : ℚ)) hc
    norm_num [triangularPoly] at h0 h2
  refine ⟨fun i _ => hEQ ▸ valuation_le_one_norm (hint (i + 1)), ?_⟩
  rw [quadratic_coeff hp hpl hQcomp]
  have hw := factorial_sub_power_sum_norm (p := p) hp2
  have hb := power_sum_sub_bernoulli_norm hpl
  have hbound := padicNorm.nonarchimedean.trans (max_le hw hb)
  convert hbound using 2
  ring

end MathlibExt.NumberTheory.WilsonFaulhaberWanted
