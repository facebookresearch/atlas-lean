/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Primality

/-!
# Nonsquare discriminants of truncated logarithmic polynomials

We prove that the discriminants of the truncated logarithmic polynomials of degrees
`3 * q`, `5 * q`, and `7 * q` are nonsquares for every prime `q`.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Truncated logarithmic polynomial.** For a natural number $n$, the truncated logarithmic
polynomial is $F_n(x) = 1 + x + \frac{x^2}{2} + \dots + \frac{x^n}{n} \in \mathbb{Q}[x]$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public noncomputable def truncatedLogPolynomial (n : ℕ) : ℚ[X] :=
  1 + ∑ j ∈ Finset.Icc 1 n, C ((j : ℚ)⁻¹) * X ^ j

/-- **Least common multiple of $1, \dots, n$.** For a natural number $n$, $L_n$ is the least common
multiple $\operatorname{lcm}(1, 2, \dots, n)$ of the integers from $1$ to $n$; in particular
$L_0 = 1$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public def truncatedLogLcm (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

/-- **Least common multiple of $1, 2, 3, 4$.** The least common multiple of the integers from $1$
to $4$ is $L_4 = \operatorname{lcm}(1, 2, 3, 4) = 12$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public theorem truncatedLogLcm_four : truncatedLogLcm 4 = 12 := by
  decide

/-- **Scaled truncated logarithmic polynomial.** For a natural number $n$, let
$L_n = \operatorname{lcm}(1, 2, \dots, n)$. The scaled truncated logarithmic polynomial is the
integer polynomial $\tilde F_n(x) = L_n + \sum_{j=1}^{n} (L_n / j)\, x^j$, where each quotient
$L_n / j$ is an integer.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public noncomputable def scaledTruncatedLogPolynomial (n : ℕ) : ℤ[X] :=
  C (truncatedLogLcm n : ℤ) + ∑ j ∈ Finset.Icc 1 n, C ((truncatedLogLcm n / j : ℕ) : ℤ) * X ^ j

/-- **The scaled truncated logarithmic polynomial is $L_n F_n$.** For a natural number $n$, let
$L_n = \operatorname{lcm}(1, 2, \dots, n)$, let $F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the
truncated logarithmic polynomial and let $\tilde F_n \in \mathbb{Z}[x]$ be the scaled truncated
logarithmic polynomial. Mapping the coefficients of $\tilde F_n$ from $\mathbb{Z}$ to
$\mathbb{Q}$ gives the polynomial $L_n F_n$ in $\mathbb{Q}[x]$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public theorem map_scaledTruncatedLogPolynomial (n : ℕ) :
    (scaledTruncatedLogPolynomial n).map (Int.castRingHom ℚ) =
      C (truncatedLogLcm n : ℚ) * truncatedLogPolynomial n := by
  simp only [scaledTruncatedLogPolynomial, truncatedLogPolynomial, Polynomial.map_add,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, mul_add, mul_one,
    Finset.mul_sum]
  refine congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun j hj => ?_)
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hj0 : (j : ℚ) ≠ 0 := by positivity
  have hdvd : j ∣ truncatedLogLcm n := Finset.dvd_lcm (s := Finset.Icc 1 n) (f := id) hj
  rw [← mul_assoc, ← C_mul]
  congr 2
  simp only [eq_intCast, Int.cast_natCast]
  rw [Nat.cast_div hdvd hj0, div_eq_mul_inv]

/-- **Resultant product for truncated logarithmic polynomials.** For a natural number $n$, let
$F_n(x) = 1 + x + \frac{x^2}{2} + \dots + \frac{x^n}{n}$, let
$L_n = \operatorname{lcm}(1, \dots, n)$, and let $\tilde F_n = L_n F_n \in \mathbb{Z}[x]$. The
integer $\mathcal{P}_n$ is the resultant $\operatorname{Res}(1 + x + \dots + x^{n-1}, \tilde F_n)$.
For $n \ge 1$ the polynomial $1 + x + \dots + x^{n-1} = F_n'$ is monic, so
$\mathcal{P}_n = \prod_{\theta} \tilde F_n(\theta)$, the product over the roots $\theta$ of $F_n'$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Equation (5). -/
public noncomputable def truncatedLogResultantProduct (n : ℕ) : ℤ :=
  resultant (∑ k ∈ Finset.range n, (X : ℤ[X]) ^ k) (scaledTruncatedLogPolynomial n)

namespace not_isSquare_discr_truncatedLog_three_five_seven_mul

private noncomputable def geomPoly {R : Type*} [Semiring R] (n : ℕ) : R[X] :=
  ∑ j ∈ Finset.range n, X ^ j

private lemma geomPoly_coeff {R : Type*} [Semiring R] (n j : ℕ) :
    (geomPoly n : R[X]).coeff j = if j < n then 1 else 0 := by
  classical
  simp [geomPoly, coeff_X_pow, Finset.mem_range]

private lemma geomPoly_degree {R : Type*} [Semiring R] [Nontrivial R] {n : ℕ} (hn : 0 < n) :
    (geomPoly n : R[X]).natDegree = n - 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun j hj => by
      simp [geomPoly_coeff, show ¬j < n by omega]
  · simp [geomPoly_coeff, show n - 1 < n by omega]

private lemma trunc_coeff (n j : ℕ) :
    (truncatedLogPolynomial n).coeff j =
      if j = 0 then 1 else if j ≤ n then (j : ℚ)⁻¹ else 0 := by
  classical
  by_cases h0 : j = 0
  · subst j
    simp [truncatedLogPolynomial, coeff_X_pow, mul_ite, Finset.mem_Icc]
  · have hj : 1 ≤ j := by omega
    simp only [truncatedLogPolynomial, coeff_add, coeff_one, h0, ↓reduceIte, zero_add,
      finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_Icc, hj, true_and]

private lemma trunc_degree {n : ℕ} (hn : 0 < n) :
    (truncatedLogPolynomial n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun j hj => by
      simp [trunc_coeff, show j ≠ 0 by omega, hj.not_ge]
  · simp [trunc_coeff, hn.ne']

private lemma trunc_derivative (n : ℕ) : (truncatedLogPolynomial n).derivative = geomPoly n := by
  ext j
  rw [coeff_derivative, trunc_coeff, geomPoly_coeff]
  have hj : (j + 1 : ℕ) ≠ 0 := by omega
  simp only [hj, ↓reduceIte]
  by_cases h : j < n
  · simp [h, Nat.succ_le_of_lt h, show (j : ℚ) + 1 ≠ 0 by positivity]
  · simp [h, show ¬j + 1 ≤ n by omega]

private lemma lcm_ne_zero (n : ℕ) : truncatedLogLcm n ≠ 0 :=
  Nat.lcmUpto_ne_zero n

private lemma geomPoly_map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (n : ℕ) :
    (geomPoly n).map f = geomPoly n := by
  simp [geomPoly, Polynomial.map_sum]

private lemma scaled_degree {n : ℕ} (hn : 0 < n) :
    (scaledTruncatedLogPolynomial n).natDegree = n := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  rw [← natDegree_map_eq_of_injective hinj,
    map_scaledTruncatedLogPolynomial, natDegree_C_mul, trunc_degree hn]
  exact_mod_cast lcm_ne_zero n

private noncomputable def signedProduct (n : ℕ) : ℤ :=
  (-1) ^ (n * (n - 1) / 2) * n * truncatedLogResultantProduct n

private lemma discr_mul_lcm {n : ℕ} (hn : 0 < n) :
    (truncatedLogPolynomial n).discr * (truncatedLogLcm n : ℚ) ^ (n - 1) =
      (signedProduct n : ℚ) := by
  have hd : 0 < (truncatedLogPolynomial n).natDegree := by rwa [trunc_degree hn]
  have hres := resultant_deriv (natDegree_pos_iff_degree_pos.mp hd)
  rw [resultant_comm, trunc_derivative, leadingCoeff, trunc_degree hn,
    trunc_coeff, ite_eq_right hn.ne', ite_eq_left le_rfl] at hres
  have hpar : Even (n * (n - 1)) := by
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · exact hk ▸ Even.mul_right (even_two_mul k) _
    · have : n - 1 = 2 * k := by omega
      rw [this]
      exact Even.mul_left (even_two_mul k) _
  rw [hpar.neg_one_pow, one_mul] at hres
  have hprod : (truncatedLogResultantProduct n : ℚ) =
      (truncatedLogLcm n : ℚ) ^ (n - 1) * resultant (geomPoly n) (truncatedLogPolynomial n)
        (n - 1) n := by
    change (↑(resultant (geomPoly n : ℤ[X]) (scaledTruncatedLogPolynomial n)) : ℚ) = _
    rw [geomPoly_degree hn, scaled_degree hn]
    change Int.castRingHom ℚ (resultant _ _ _ _) = _
    rw [← resultant_map_map, geomPoly_map, map_scaledTruncatedLogPolynomial, resultant_C_mul_right]
  rw [signedProduct, Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, hprod, hres]
  have hs : (-1 : ℚ) ^ (n * (n - 1) / 2) * (-1) ^ (n * (n - 1) / 2) = 1 := by
    rw [← mul_pow]; simp
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    _ = _ := by
      symm
      calc
        _ = ((-1 : ℚ) ^ (n * (n - 1) / 2) * (-1) ^ (n * (n - 1) / 2)) *
            ((n : ℚ) * (n : ℚ)⁻¹) *
            ((truncatedLogPolynomial n).discr * (truncatedLogLcm n : ℚ) ^ (n - 1)) := by ring
        _ = _ := by simp [hs, hnQ]

private lemma square_signedProduct {n : ℕ} (hn : Odd n)
    (h : IsSquare (truncatedLogPolynomial n).discr) : IsSquare (signedProduct n) := by
  obtain ⟨k, hk⟩ := hn
  have he : n - 1 = k + k := by omega
  rw [← Rat.isSquare_intCast_iff, ← discr_mul_lcm (by omega), he, pow_add]
  exact h.mul ⟨_, rfl⟩

private noncomputable def reducedPoly (p m : ℕ) (withConstant : Bool) : (ZMod p)[X] :=
  C (if withConstant then 1 else 0) + ∑ j ∈ Finset.Icc 1 m, C ((j : ZMod p)⁻¹) * X ^ j

private lemma reducedPoly_coeff (p m j : ℕ) (b : Bool) :
    (reducedPoly p m b).coeff j =
      if j = 0 then (if b then 1 else 0) else if j ≤ m then (j : ZMod p)⁻¹ else 0 := by
  classical
  by_cases h0 : j = 0
  · subst j
    cases b <;> simp [reducedPoly, coeff_X_pow, mul_ite, Finset.mem_Icc]
  · have hj : 1 ≤ j := by omega
    cases b <;> simp [reducedPoly, coeff_X_pow, mul_ite, Finset.mem_Icc, h0, hj, coeff_one]

private lemma scaled_coeff (n j : ℕ) :
    (scaledTruncatedLogPolynomial n).coeff j =
      if j = 0 then (truncatedLogLcm n : ℤ) else
        if j ≤ n then (↑(truncatedLogLcm n / j) : ℤ) else 0 := by
  classical
  by_cases h0 : j = 0
  · subst j
    simp [scaledTruncatedLogPolynomial, coeff_X_pow, mul_ite, Finset.mem_Icc]
  · have hj : 1 ≤ j := by omega
    simp [scaledTruncatedLogPolynomial, coeff_X_pow, mul_ite, Finset.mem_Icc, h0, hj]

private lemma lcm_dvd {n j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) : j ∣ truncatedLogLcm n :=
  Finset.dvd_lcm (s := Finset.Icc 1 n) (f := id) (Finset.mem_Icc.mpr ⟨hj, hjn⟩)

private lemma lcm_quotient_ne_zero {p e n : ℕ} [Fact p.Prime]
    (hlo : p ^ e ≤ n) (hhi : n < p ^ (e + 1)) :
    (↑(truncatedLogLcm n / p ^ e) : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  have hdpos : 0 < p ^ e := pow_pos hp.pos _
  have hd : p ^ e ∣ truncatedLogLcm n := lcm_dvd hdpos hlo
  have hn : n ≠ 0 := (hdpos.trans_le hlo).ne' 
  rw [ne_eq, ZMod.natCast_eq_zero_iff, Nat.dvd_div_iff_mul_dvd hd, ← pow_succ,
    hp.pow_dvd_iff_le_factorization (lcm_ne_zero n)]
  change ¬e + 1 ≤ (Nat.lcmUpto n).factorization p
  rw [Nat.factorization_lcmUpto n hp, (Nat.log_eq_iff (Or.inr ⟨hp.one_lt, hn⟩)).2 ⟨hlo, hhi⟩]
  omega

private lemma expand_prime_pow {p : ℕ} [Fact p.Prime] (e : ℕ) (f : (ZMod p)[X]) :
    expand (ZMod p) (p ^ e) f = f ^ p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', expand_mul, ih, ZMod.expand_card, ← pow_mul, mul_comm]

-- Reduction keeps exactly the coefficients whose denominator is divisible by the
-- largest power of p at most n. Frobenius accounts for the resulting exponents.
private lemma scaled_mod {p e n : ℕ} [Fact p.Prime]
    (hlo : p ^ e ≤ n) (hhi : n < p ^ (e + 1)) :
    (scaledTruncatedLogPolynomial n).map (Int.castRingHom (ZMod p)) =
      C (↑(truncatedLogLcm n / p ^ e) : ZMod p) *
        reducedPoly p (n / p ^ e) (e == 0) ^ p ^ e := by
  have hp : p.Prime := Fact.out
  have hd : 0 < p ^ e := pow_pos hp.pos _
  ext j
  rw [coeff_map, scaled_coeff, coeff_C_mul, ← expand_prime_pow, coeff_expand hd]
  by_cases hj0 : j = 0
  · subst j
    simp only [↓reduceIte, dvd_zero, Nat.zero_div, reducedPoly_coeff, Int.coe_castRingHom,
      Int.cast_natCast, beq_iff_eq]
    by_cases he : e = 0
    · simp [he]
    · have hpL : p ∣ truncatedLogLcm n :=
        (dvd_pow_self p he).trans (lcm_dvd (by omega) hlo)
      simp [he, (ZMod.natCast_eq_zero_iff _ _).2 hpL]
  · simp only [hj0, ↓reduceIte, apply_ite, map_zero, Int.coe_castRingHom, Int.cast_natCast]
    by_cases hj : j ≤ n
    · rw [ite_eq_left hj]
      have hjL := lcm_dvd (by omega : 1 ≤ j) hj
      by_cases hdiv : p ^ e ∣ j
      · rw [ite_eq_left hdiv, reducedPoly_coeff]
        have hjq : 0 < j / p ^ e :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hdiv) hd
        have hjm : j / p ^ e ≤ n / p ^ e := Nat.div_le_div_right hj
        have hlt : j / p ^ e < p := by
          apply (Nat.div_lt_iff_lt_mul hd).2
          exact hj.trans_lt (by simpa [pow_succ'] using hhi)
        have hz : (↑(j / p ^ e) : ZMod p) ≠ 0 := by
          rw [ne_eq, ZMod.natCast_eq_zero_iff]
          exact fun h => hlt.not_ge (Nat.le_of_dvd hjq h)
        rw [ite_eq_right hjq.ne', ite_eq_left hjm, ← div_eq_mul_inv, eq_div_iff hz,
          ← Nat.cast_mul]
        congr 1
        calc
          truncatedLogLcm n / j * (j / p ^ e) =
              (truncatedLogLcm n / j * j) / p ^ e := by
                rw [Nat.mul_div_assoc _ hdiv]
          _ = truncatedLogLcm n / p ^ e := by rw [Nat.div_mul_cancel hjL]
      · rw [ite_eq_right hdiv, mul_zero, ZMod.natCast_eq_zero_iff]
        by_contra h
        have hcop : (truncatedLogLcm n / j).Coprime (p ^ e) :=
          (hp.coprime_iff_not_dvd.mpr h).symm.pow_right _
        apply hdiv
        apply hcop.symm.dvd_of_dvd_mul_left
        rw [Nat.div_mul_cancel hjL]
        exact lcm_dvd hd hlo
    · rw [ite_eq_right hj]
      by_cases hdiv : p ^ e ∣ j
      · rw [ite_eq_left hdiv, reducedPoly_coeff]
        have hjq : 0 < j / p ^ e :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hdiv) hd
        have hlt : ¬j / p ^ e ≤ n / p ^ e := by
          intro h
          have hm := Nat.mul_le_mul_right (p ^ e) h
          rw [Nat.div_mul_cancel hdiv] at hm
          exact hj (hm.trans (Nat.div_mul_le_self _ _))
        simp [hjq.ne', hlt]
      · simp [hdiv]

private lemma reducedPoly_degree {p m : ℕ} [Fact p.Prime] (hm : 0 < m) (hlt : m < p)
    (b : Bool) : (reducedPoly p m b).natDegree = m := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun j hj => by
      simp [reducedPoly_coeff, show j ≠ 0 by omega, hj.not_ge]
  · have hz : (m : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact fun h => hlt.not_ge (Nat.le_of_dvd hm h)
    simp [reducedPoly_coeff, hm.ne', hz]

-- The monic derivative permits dropping the padding in the Sylvester resultant
-- after reduction, even when the leading coefficient of the scaled polynomial vanishes.
private lemma mod_resultant {p e n : ℕ} [Fact p.Prime]
    (hlo : p ^ e ≤ n) (hhi : n < p ^ (e + 1)) :
    (truncatedLogResultantProduct n : ZMod p) =
      (↑(truncatedLogLcm n / p ^ e) : ZMod p) ^ (n - 1) *
        resultant (geomPoly n) (reducedPoly p (n / p ^ e) (e == 0)) ^ p ^ e := by
  have hp : p.Prime := Fact.out
  have hd : 0 < p ^ e := pow_pos hp.pos _
  have hn := hd.trans_le hlo
  have hm : 0 < n / p ^ e := Nat.div_pos hlo hd
  have hlt : n / p ^ e < p := (Nat.div_lt_iff_lt_mul hd).2 (by simpa [pow_succ'] using hhi)
  let g := reducedPoly p (n / p ^ e) (e == 0)
  have hg : g.natDegree = n / p ^ e := reducedPoly_degree hm hlt _
  have hle : (g ^ p ^ e).natDegree ≤ n := by
    rw [natDegree_pow, hg]
    simpa [mul_comm] using Nat.div_mul_le_self n (p ^ e)
  have hf : (geomPoly n : (ZMod p)[X]).Monic :=
    monic_geom_sum_X hn.ne'
  change Int.castRingHom (ZMod p) (resultant (geomPoly n) (scaledTruncatedLogPolynomial n)) = _
  rw [geomPoly_degree hn, scaled_degree hn, ← resultant_map_map, geomPoly_map,
    scaled_mod hlo hhi, resultant_C_mul_right]
  change _ * resultant (geomPoly n) (g ^ p ^ e) (n - 1) n = _
  have hpad := resultant_add_right_deg (geomPoly n) (g ^ p ^ e) (n - 1)
    (g ^ p ^ e).natDegree (n - (g ^ p ^ e).natDegree) le_rfl
  rw [Nat.add_sub_of_le hle, ← geomPoly_degree (R := ZMod p) hn,
    coeff_natDegree, hf.leadingCoeff, one_pow, one_mul] at hpad
  rw [← geomPoly_degree (R := ZMod p) hn, hpad,
    resultant_pow_right _ _ _ _ le_rfl (pow_ne_zero _ (leadingCoeff_ne_zero.mpr
      (fun h => by simp [h, hm.ne'.symm] at hg)))]

private lemma not_square_prime_mul {p : ℕ} [Fact p.Prime] {z : ℤ}
    (hz : (z : ZMod p) ≠ 0) : ¬ IsSquare ((p : ℤ) * z) := by
  rintro ⟨w, hw⟩
  have hwp : (w : ZMod p) = 0 := by
    have h := congrArg (Int.castRingHom (ZMod p)) hw
    simpa using h.symm
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hwp
  have hpc : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hz' : z = (p : ℤ) * k * k := by
    apply mul_left_cancel₀ hpc
    rw [hw, hk]
    ring
  exact hz (by simp [hz'])

private lemma square_lcm_signedProduct {n : ℕ} (hn : 0 < n) (he : Even n)
    (h : IsSquare (truncatedLogPolynomial n).discr) :
    IsSquare ((truncatedLogLcm n : ℤ) * signedProduct n) := by
  obtain ⟨k, hk⟩ := he
  rw [← Rat.isSquare_intCast_iff, Int.cast_mul, ← discr_mul_lcm hn, Int.cast_natCast]
  have hexp : (n - 1) + 1 = k + k := by omega
  have hpow : (truncatedLogLcm n : ℚ) *
      ((truncatedLogPolynomial n).discr * (truncatedLogLcm n : ℚ) ^ (n - 1)) =
      (truncatedLogPolynomial n).discr * ((truncatedLogLcm n : ℚ) ^ k *
        (truncatedLogLcm n : ℚ) ^ k) := by
    rw [← pow_add, ← hexp, pow_succ]
    ring
  rw [hpow]
  exact h.mul ⟨_, rfl⟩

private lemma nonsquare_of_odd_mul {p m : ℕ} [Fact p.Prime] (hodd : Odd (m * p))
    (hm : (m : ZMod p) ≠ 0) (hP : (truncatedLogResultantProduct (m * p) : ZMod p) ≠ 0) :
    ¬ IsSquare (truncatedLogPolynomial (m * p)).discr := by
  intro h
  have hs := square_signedProduct hodd h
  let z := (-1 : ℤ) ^ ((m * p) * (m * p - 1) / 2) * (m : ℤ) *
    truncatedLogResultantProduct (m * p)
  have hz : (z : ZMod p) ≠ 0 := by
    dsimp [z]
    push_cast
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hm) hP
  apply not_square_prime_mul hz
  convert hs using 1
  simp only [z, signedProduct, Nat.cast_mul]
  ring

private lemma resultant_geom_X {p n : ℕ} [Fact p.Prime] (hn : 0 < n) :
    resultant (geomPoly n : (ZMod p)[X]) X = (-1) ^ (n - 1) := by
  have h := resultant_X_pow_right (geomPoly n : (ZMod p)[X]) (geomPoly n).natDegree 1 le_rfl
  rw [pow_one, mul_one, pow_one, geomPoly_degree hn, geomPoly_coeff, ite_eq_left hn] at h
  simpa only [geomPoly_degree hn, natDegree_X, mul_one] using h

private lemma reducedPoly_monomial {p e n : ℕ} [Fact p.Prime] (he : e ≠ 0)
    (hlo : p ^ e ≤ n) (hhalf : n < 2 * p ^ e) :
    reducedPoly p (n / p ^ e) (e == 0) = X := by
  have hd : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos _
  have hm : n / p ^ e = 1 := by
    have hlo' := Nat.div_pos hlo hd
    have hhi' := (Nat.div_lt_iff_lt_mul hd).2 hhalf
    omega
  simp [hm, he, reducedPoly]

private lemma mod_resultant_monomial {p e n : ℕ} [Fact p.Prime] (he : e ≠ 0)
    (hlo : p ^ e ≤ n) (hhi : n < p ^ (e + 1)) (hhalf : n < 2 * p ^ e) :
    (truncatedLogResultantProduct n : ZMod p) =
      (↑(truncatedLogLcm n / p ^ e) : ZMod p) ^ (n - 1) * ((-1) ^ (n - 1)) ^ p ^ e := by
  have hn := (pow_pos (Fact.out : p.Prime).pos e).trans_le hlo
  rw [mod_resultant hlo hhi, reducedPoly_monomial he hlo hhalf, resultant_geom_X hn]

private lemma monomial_resultant_ne_zero {p e n : ℕ} [Fact p.Prime] (he : e ≠ 0)
    (hlo : p ^ e ≤ n) (hhi : n < p ^ (e + 1)) (hhalf : n < 2 * p ^ e) :
    (truncatedLogResultantProduct n : ZMod p) ≠ 0 := by
  rw [mod_resultant_monomial he hlo hhi hhalf]
  exact mul_ne_zero (pow_ne_zero _ (lcm_quotient_ne_zero hlo hhi))
    (pow_ne_zero _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))

private lemma odd_mod_obstruction {p e n : ℕ} [Fact p.Prime] (hodd : Odd n)
    (hlo : p ^ e ≤ n) (hhi : n < p ^ (e + 1))
    (hns : ¬ IsSquare ((-1 : ZMod p) ^ (n * (n - 1) / 2) * (n : ZMod p) *
      resultant (geomPoly n) (reducedPoly p (n / p ^ e) (e == 0)) ^ p ^ e)) :
    ¬ IsSquare (truncatedLogPolynomial n).discr := by
  intro h
  have hs := (square_signedProduct hodd h).map (Int.castRingHom (ZMod p))
  change IsSquare (signedProduct n : ZMod p) at hs
  rw [signedProduct, Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, mod_resultant hlo hhi, ← mul_left_comm] at hs
  have hs' : IsSquare ((↑(truncatedLogLcm n / p ^ e) : ZMod p) ^ (n - 1)) := by
    obtain ⟨k, hk⟩ := hodd
    rw [show n - 1 = k + k by omega, pow_add]
    exact IsSquare.mul_self _
  have h0 := pow_ne_zero (n - 1) (lcm_quotient_ne_zero hlo hhi)
  apply hns
  simpa only [mul_div_cancel_left₀ _ h0] using hs.div hs'

private lemma nonsquare_of_odd_monomial {p e n : ℕ} [Fact p.Prime] (he : e ≠ 0)
    (hodd : Odd n) (hlo : p ^ e ≤ n) (hhi : n < p ^ (e + 1)) (hhalf : n < 2 * p ^ e)
    (hns : ¬ IsSquare ((-1 : ZMod p) ^ (n * (n - 1) / 2) * (n : ZMod p))) :
    ¬ IsSquare (truncatedLogPolynomial n).discr := by
  have hn := (pow_pos (Fact.out : p.Prime).pos e).trans_le hlo
  have heven : Even (n - 1) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  apply odd_mod_obstruction hodd hlo hhi
  rwa [reducedPoly_monomial he hlo hhalf, resultant_geom_X hn, heven.neg_one_pow, one_pow, mul_one]

private lemma nonsquare_of_even_monomial {p n : ℕ} [Fact p.Prime] (he : Even n)
    (hlo : p ≤ n) (hhalf : n < 2 * p) (hnp : (n : ZMod p) ≠ 0) :
    ¬ IsSquare (truncatedLogPolynomial n).discr := by
  intro h
  have hp : p.Prime := Fact.out
  have hhi : n < p ^ (1 + 1) := by
    rw [show 1 + 1 = 2 by decide, pow_two]
    exact hhalf.trans_le (Nat.mul_le_mul_right _ hp.two_le)
  have hlo' : p ^ 1 ≤ n := by simpa using hlo
  have hP := monomial_resultant_ne_zero (p := p) (e := 1) one_ne_zero hlo' hhi
    (by simpa using hhalf)
  have hq := lcm_quotient_ne_zero hlo' hhi
  rw [pow_one] at hq
  have hd := lcm_dvd hp.one_le hlo
  have hL : (truncatedLogLcm n : ℤ) = (p : ℤ) * ↑(truncatedLogLcm n / p) := by
    exact_mod_cast (Nat.mul_div_cancel' hd).symm
  let z := (↑(truncatedLogLcm n / p) : ℤ) * signedProduct n
  have hz : (z : ZMod p) ≠ 0 := by
    simp only [z, signedProduct, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast]
    exact mul_ne_zero hq
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hnp) hP)
  apply not_square_prime_mul hz
  rw [← mul_assoc, ← hL]
  exact square_lcm_signedProduct (hp.pos.trans_le hlo) he h

private lemma not_square_of_euler {p : ℕ} [Fact p.Prime] {x : ZMod p}
    (hp : Odd p) (hx : x ^ ((p - 1) / 2) ≠ 0) (h1 : x ^ ((p - 1) / 2) ≠ 1) :
    ¬ IsSquare x := by
  rintro ⟨a, rfl⟩
  have ha : a ≠ 0 := by
    intro ha
    apply hx
    have hp' : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hp'' : p % 2 = 1 := Nat.odd_iff.mp hp
    simp [ha, zero_pow (show (p - 1) / 2 ≠ 0 by omega)]
  apply h1
  have hexp : (p - 1) / 2 + (p - 1) / 2 = p - 1 := by
    have := Nat.odd_iff.mp hp
    omega
  rw [mul_pow, ← pow_add, hexp, ZMod.pow_card_sub_one_eq_one ha]

private noncomputable def integralLog (m : ℕ) : ℤ[X] :=
  scaledTruncatedLogPolynomial m - C (truncatedLogLcm m : ℤ)

private lemma integralLog_map {p m : ℕ} [Fact p.Prime] (hm : 0 < m) (hmp : m < p) :
    (integralLog m).map (Int.castRingHom (ZMod p)) =
      C (truncatedLogLcm m : ZMod p) * reducedPoly p m false := by
  have hlo : p ^ 0 ≤ m := by simpa using Nat.succ_le_of_lt hm
  rw [integralLog, Polynomial.map_sub, scaled_mod hlo (by simpa using hmp), map_C]
  simp only [pow_zero, Nat.div_one, beq_self_eq_true, pow_one, Int.coe_castRingHom,
    Int.cast_natCast]
  simp [reducedPoly, mul_add]

-- The certificate tests the derivative roots modulo p all at once.
private lemma nonsquare_of_bezout {p m k : ℕ} [Fact p.Prime] (hm : 0 < m) (hmp : m < p)
    (hodd : Odd (m * p)) (hk : (k : ZMod p) ≠ 0)
    {a b : ℤ[X]} (hab : a * (X ^ m - 1) + b * integralLog m = C (k : ℤ)) :
    ¬ IsSquare (truncatedLogPolynomial (m * p)).discr := by
  have hp : p.Prime := Fact.out
  have hn : 0 < m * p := Nat.mul_pos hm hp.pos
  have hlo : p ^ 1 ≤ m * p := by
    simpa [pow_one] using Nat.mul_le_mul_right p hm
  have hhi : m * p < p ^ (1 + 1) := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_right hmp hp.pos
  let g := reducedPoly p m false
  have hG : IsCoprime ((X : (ZMod p)[X]) ^ m - 1) g := by
    have hc := congrArg (Polynomial.map (Int.castRingHom (ZMod p))) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow,
      map_X, Polynomial.map_one, integralLog_map hm hmp, map_C, Int.coe_castRingHom,
      Int.cast_natCast] at hc
    refine ⟨C (k : ZMod p)⁻¹ * a.map (Int.castRingHom (ZMod p)),
      C (k : ZMod p)⁻¹ * b.map (Int.castRingHom (ZMod p)) * C (truncatedLogLcm m : ZMod p),
      ?_⟩
    dsimp [g]
    calc
      _ = C (k : ZMod p)⁻¹ *
          (a.map (Int.castRingHom (ZMod p)) * (X ^ m - 1) +
            b.map (Int.castRingHom (ZMod p)) *
              (C (truncatedLogLcm m : ZMod p) * reducedPoly p m false)) := by ring
      _ = 1 := by rw [hc, ← C_mul, inv_mul_cancel₀ hk, map_one]
  have hdiv : (geomPoly (m * p) : (ZMod p)[X]) ∣ (X ^ m - 1) ^ p := by
    refine ⟨X - 1, ?_⟩
    rw [sub_pow_char, ← pow_mul, one_pow]
    exact (geom_sum_mul (X : (ZMod p)[X]) (m * p)).symm
  have hc := (hG.pow_left).of_isCoprime_of_dvd_left hdiv
  have hr : resultant (geomPoly (m * p) : (ZMod p)[X]) g ≠ 0 :=
    fun h => (resultant_eq_zero_iff.mp h).2 hc
  have hmz : (m : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun h => hmp.not_ge (Nat.le_of_dvd hm h)
  apply nonsquare_of_odd_mul hodd hmz
  rw [mod_resultant hlo hhi, pow_one p, Nat.mul_div_cancel _ hp.pos]
  exact mul_ne_zero (pow_ne_zero _ (by simpa using lcm_quotient_ne_zero hlo hhi))
    (pow_ne_zero _ hr)

private lemma sum_Icc_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ j ∈ Finset.range n, f (j + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [Nat.add_comm 1]

private lemma bezout_three :
    (-143 - 84 * X - 60 * X ^ 2) * (X ^ 3 - 1) +
      (-14 - 3 * X + 30 * X ^ 2) * integralLog 3 = C (143 : ℤ) := by
  have h : truncatedLogLcm 3 = 6 := by decide
  norm_num [integralLog, scaledTruncatedLogPolynomial, h, sum_Icc_eq_range, Finset.sum_range_succ]
  ring

private lemma bezout_five :
    (-456773207 - 245985840 * X - 168764220 * X ^ 2 - 130143330 * X ^ 3 -
      106920360 * X ^ 4) * (X ^ 5 - 1) +
      (-4099764 - 762855 * X - 421040 * X ^ 2 - 292260 * X ^ 3 + 8910030 * X ^ 4) *
        integralLog 5 = C (456773207 : ℤ) := by
  have h : truncatedLogLcm 5 = 60 := by decide
  norm_num [integralLog, scaledTruncatedLogPolynomial, h, sum_Icc_eq_range, Finset.sum_range_succ]
  ring

private lemma bezout_seven :
    (-1274923517273587269 - 666043881614227200 * X - 450050897823093000 * X ^ 2 -
      342597056786903380 * X ^ 3 - 278388344308239340 * X ^ 4 - 235648423054899400 * X ^ 5 -
      205099001564805600 * X ^ 6) * (X ^ 7 - 1) +
      (-1585818765748160 - 278640373847570 * X - 147780835890884 * X ^ 2 -
        99604157211755 * X ^ 3 - 75181470092540 * X ^ 4 - 60562423956230 * X ^ 5 +
        3418316692746760 * X ^ 6) * integralLog 7 = C (1274923517273587269 : ℤ) := by
  have h : truncatedLogLcm 7 = 420 := by decide
  norm_num [integralLog, scaledTruncatedLogPolynomial, h, sum_Icc_eq_range, Finset.sum_range_succ]
  ring

-- Repeated prime factors are checked over fields in which the derivative splits.
private lemma resultant_geom_split {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {a : R} (ha : IsPrimitiveRoot a (n + 1)) (g : R[X]) :
    resultant (geomPoly (n + 1)) g = ∏ j ∈ Finset.range n, g.eval (a ^ (j + 1)) := by
  have h := X_pow_sub_C_eq_prod ha (Nat.succ_pos n) (one_pow (n + 1) : (1 : R) ^ _ = 1)
  rw [C_1, ← geom_sum_mul, Finset.prod_range_succ', pow_zero, mul_one, C_1] at h
  have hf : (geomPoly (n + 1) : R[X]) = ∏ j ∈ Finset.range n, (X - C (a ^ (j + 1))) :=
    mul_right_cancel₀ (X_sub_C_ne_zero 1) (by simpa only [geomPoly, C_1, mul_one] using h)
  rw [hf, resultant_prod_left _ _ _ _ (by
    simpa only [leadingCoeff_X_sub_C, Finset.prod_const_one] using (one_ne_zero : (1 : R) ≠ 0))
    le_rfl]
  exact Finset.prod_congr rfl fun j _ => by
    rw [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ le_rfl]

private def evalReducedProduct (p n : ℕ) (a : ZMod p) : ZMod p :=
  ∏ j ∈ Finset.range (n - 1), (1 + ∑ i ∈ Finset.range n,
    ((i + 1 : ℕ) : ZMod p)⁻¹ * (a ^ (j + 1)) ^ (i + 1))

private lemma nonsquare_of_split {p n : ℕ} [Fact p.Prime] (hodd : Odd n) (hnp : n < p)
    {a : ZMod p} (ha : IsPrimitiveRoot a n)
    (hns : ¬ IsSquare ((-1 : ZMod p) ^ (n * (n - 1) / 2) * (n : ZMod p) *
      evalReducedProduct p n a)) :
    ¬ IsSquare (truncatedLogPolynomial n).discr := by
  obtain _ | n := n
  · simp at hodd
  apply odd_mod_obstruction (e := 0) hodd (by simp) (by simpa using hnp)
  rw [pow_zero, Nat.div_one]
  change ¬ IsSquare ((-1 : ZMod p) ^ ((n + 1) * (n + 1 - 1) / 2) * (↑(n + 1) : ZMod p) *
    resultant (geomPoly (n + 1)) (reducedPoly p (n + 1) true) ^ 1)
  rw [pow_one, resultant_geom_split ha]
  simpa [evalReducedProduct, reducedPoly, Polynomial.eval_finsetSum,
    sum_Icc_eq_range] using hns

private lemma nonsquare_nine : ¬ IsSquare (truncatedLogPolynomial 9).discr := by
  let _ : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  have ha : IsPrimitiveRoot (2 : ZMod 73) 9 := by
    refine (IsPrimitiveRoot.iff (by decide)).2 ⟨by decide, fun k hk1 hk2 => ?_⟩
    interval_cases k <;> decide
  apply nonsquare_of_split (by decide) (by decide) ha
  have hr : evalReducedProduct 73 9 2 = 51 := by decide +kernel
  rw [hr]
  exact not_square_of_euler (by decide) (by decide) (by decide)

private lemma nonsquare_twenty_five : ¬ IsSquare (truncatedLogPolynomial 25).discr := by
  let _ : Fact (Nat.Prime 101) := ⟨by norm_num⟩
  have ha : IsPrimitiveRoot (5 : ZMod 101) 25 := by
    refine (IsPrimitiveRoot.iff (by decide)).2 ⟨by decide, fun k hk1 hk2 => ?_⟩
    interval_cases k <;> decide
  apply nonsquare_of_split (by decide) (by decide) ha
  have hr : evalReducedProduct 101 25 5 = 3 := by decide +kernel
  rw [hr]
  exact not_square_of_euler (by decide) (by decide) (by decide)

set_option maxRecDepth 4096 in
private lemma nonsquare_forty_nine : ¬ IsSquare (truncatedLogPolynomial 49).discr := by
  let _ : Fact (Nat.Prime 197) := ⟨by norm_num⟩
  have ha : IsPrimitiveRoot (16 : ZMod 197) 49 := by
    refine (IsPrimitiveRoot.iff (by decide)).2 ⟨by decide, fun k hk1 hk2 => ?_⟩
    interval_cases k <;> decide
  apply nonsquare_of_split (by decide) (by decide) ha
  have hr : evalReducedProduct 197 49 16 = 74 := by decide +kernel
  rw [hr]
  exact not_square_of_euler (by decide) (by decide) (by decide)

private lemma nonsquare_six : ¬ IsSquare (truncatedLogPolynomial 6).discr := by
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact nonsquare_of_even_monomial (p := 5) (by decide) (by decide) (by decide) (by decide)

private lemma nonsquare_ten : ¬ IsSquare (truncatedLogPolynomial 10).discr := by
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact nonsquare_of_even_monomial (p := 7) (by decide) (by decide) (by decide) (by decide)

private lemma nonsquare_fourteen : ¬ IsSquare (truncatedLogPolynomial 14).discr := by
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact nonsquare_of_even_monomial (p := 11) (by decide) (by decide) (by decide) (by decide)

private lemma nonsquare_fifteen : ¬ IsSquare (truncatedLogPolynomial 15).discr := by
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact nonsquare_of_odd_mul (p := 3) (m := 5) (by decide) (by decide)
    (monomial_resultant_ne_zero (e := 2) (by decide) (by decide) (by decide) (by decide))

private lemma nonsquare_thirty_three : ¬ IsSquare (truncatedLogPolynomial 33).discr := by
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact nonsquare_of_odd_mul (p := 3) (m := 11) (by decide) (by decide)
    (monomial_resultant_ne_zero (e := 3) (by decide) (by decide) (by decide) (by decide))

private lemma nonsquare_thirty_five : ¬ IsSquare (truncatedLogPolynomial 35).discr := by
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact nonsquare_of_odd_mul (p := 5) (m := 7) (by decide) (by decide)
    (monomial_resultant_ne_zero (e := 2) (by decide) (by decide) (by decide) (by decide))

private lemma nonsquare_thirty_nine : ¬ IsSquare (truncatedLogPolynomial 39).discr := by
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact nonsquare_of_odd_mul (p := 3) (m := 13) (by decide) (by decide)
    (monomial_resultant_ne_zero (e := 3) (by decide) (by decide) (by decide) (by decide))

private lemma nonsquare_seventy_seven : ¬ IsSquare (truncatedLogPolynomial 77).discr := by
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact nonsquare_of_odd_mul (p := 7) (m := 11) (by decide) (by decide)
    (monomial_resultant_ne_zero (e := 2) (by decide) (by decide) (by decide) (by decide))

private lemma nonsquare_fifty_five : ¬ IsSquare (truncatedLogPolynomial 55).discr := by
  let _ : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  exact nonsquare_of_odd_monomial (p := 29) (e := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private lemma nonsquare_505 : ¬ IsSquare (truncatedLogPolynomial 505).discr := by
  let _ : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  exact nonsquare_of_odd_monomial (p := 17) (e := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private lemma nonsquare_685 : ¬ IsSquare (truncatedLogPolynomial 685).discr := by
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact nonsquare_of_odd_mul (p := 5) (m := 137) (by decide) (by decide)
    (monomial_resultant_ne_zero (e := 4) (by decide) (by decide) (by decide) (by decide))

private lemma nonsquare_15005 : ¬ IsSquare (truncatedLogPolynomial 15005).discr := by
  let _ : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  refine nonsquare_of_odd_monomial (p := 97) (e := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  have hs : (-1 : ZMod 97) ^ (15005 * (15005 - 1) / 2) = 1 := by
    exact Even.neg_one_pow (by decide)
  rw [hs, one_mul]
  exact not_square_of_euler (by decide) (by decide) (by decide)

private lemma nonsquare_8195100661997347 :
    ¬ IsSquare (truncatedLogPolynomial 8195100661997347).discr := by
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine nonsquare_of_odd_monomial (p := 3) (e := 33)
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  have hs : (-1 : ZMod 3) ^ (8195100661997347 * (8195100661997347 - 1) / 2) = -1 := by
    exact Odd.neg_one_pow (by decide)
  rw [hs]
  exact not_square_of_euler (by decide) (by decide) (by decide)

private lemma large_exception_prime : Nat.Prime 1170728665999621 := by
  primality (cert := .witnesses [
    .lucas { root := 10, primeFactors := [2, 3, 5, 7, 13, 214419169597] },
    .lucas { root := 2, primeFactors := [2, 3, 1231, 14515243] },
    .lucas { root := 13, primeFactors := [2, 3, 7, 345601] },
    .lucas { root := 29, primeFactors := [2, 3, 5] }]) [show Nat.Prime 1231 by norm_num]

private lemma nonsquare_three {q : ℕ} (hq : q.Prime) :
    ¬ IsSquare (truncatedLogPolynomial (3 * q)).discr := by
  have htwo := hq.two_le
  by_cases hqle : q ≤ 3
  · interval_cases q
    · exact nonsquare_six
    · exact nonsquare_nine
  have hlt : 3 < q := by omega
  have hodd := (by decide : Odd 3).mul (hq.odd_of_ne_two (by omega))
  let _ : Fact q.Prime := ⟨hq⟩
  by_cases hk : q ∣ 143
  · have hfac : 143 = 11 * 13 := by decide
    rw [hfac, hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 13)] at hk
    rcases hk with rfl | rfl
    · exact nonsquare_thirty_three
    · exact nonsquare_thirty_nine
  exact nonsquare_of_bezout (by decide) hlt hodd (mt (ZMod.natCast_eq_zero_iff _ _).mp hk)
    bezout_three

private lemma nonsquare_five {q : ℕ} (hq : q.Prime) :
    ¬ IsSquare (truncatedLogPolynomial (5 * q)).discr := by
  have htwo := hq.two_le
  by_cases hqle : q ≤ 5
  · interval_cases q
    · exact nonsquare_ten
    · exact nonsquare_fifteen
    · norm_num at hq
    · exact nonsquare_twenty_five
  have hlt : 5 < q := by omega
  have hodd := (by decide : Odd 5).mul (hq.odd_of_ne_two (by omega))
  let _ : Fact q.Prime := ⟨hq⟩
  by_cases hk : q ∣ 456773207
  · have hfac : 456773207 = 11 * (101 * (137 * 3001)) := by decide
    simp only [hfac, hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 101),
      Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 137),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3001)] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact nonsquare_fifty_five
    · exact nonsquare_505
    · exact nonsquare_685
    · exact nonsquare_15005
  exact nonsquare_of_bezout (by decide) hlt hodd (mt (ZMod.natCast_eq_zero_iff _ _).mp hk)
    bezout_five

private lemma nonsquare_seven {q : ℕ} (hq : q.Prime) :
    ¬ IsSquare (truncatedLogPolynomial (7 * q)).discr := by
  have htwo := hq.two_le
  by_cases hqle : q ≤ 7
  · interval_cases q
    · exact nonsquare_fourteen
    · exact nonsquare_three (q := 7) (by decide)
    · norm_num at hq
    · exact nonsquare_thirty_five
    · norm_num at hq
    · exact nonsquare_forty_nine
  have hlt : 7 < q := by omega
  have hodd := (by decide : Odd 7).mul (hq.odd_of_ne_two (by omega))
  let _ : Fact q.Prime := ⟨hq⟩
  by_cases hk : q ∣ 1274923517273587269
  · have hfac : 1274923517273587269 = 3 ^ 2 * (11 ^ 2 * 1170728665999621) := by decide
    rw [hfac] at hk
    rcases hq.dvd_mul.mp hk with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 3)).mp (hq.dvd_of_dvd_pow h)
      omega
    rcases hq.dvd_mul.mp h with h | h
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 11)).mp
        (hq.dvd_of_dvd_pow h)
      exact nonsquare_seventy_seven
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq large_exception_prime).mp h
      exact nonsquare_8195100661997347
  exact nonsquare_of_bezout (by decide) hlt hodd (mt (ZMod.natCast_eq_zero_iff _ _).mp hk)
    bezout_seven

end not_isSquare_discr_truncatedLog_three_five_seven_mul

/-- **Nonsquare discriminants of $F_{3q}$, $F_{5q}$ and $F_{7q}$.** Let
$F_n(x) = 1 + x + x^2/2 + \cdots + x^n/n$ be the truncated logarithmic polynomial. For every
prime $q$, if $n = 3q$, $n = 5q$ or $n = 7q$, then the discriminant of $F_n$ is not a square in
$\mathbb{Q}$.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Proposition 2
(`integers-2025-A39-prop-2`). -/
public theorem not_isSquare_discr_truncatedLog_three_five_seven_mul {q n : ℕ}
    (hq : q.Prime) (hn : n = 3 * q ∨ n = 5 * q ∨ n = 7 * q) :
    ¬ IsSquare (truncatedLogPolynomial n).discr := by
  rcases hn with rfl | rfl | rfl
  · exact not_isSquare_discr_truncatedLog_three_five_seven_mul.nonsquare_three hq
  · exact not_isSquare_discr_truncatedLog_three_five_seven_mul.nonsquare_five hq
  · exact not_isSquare_discr_truncatedLog_three_five_seven_mul.nonsquare_seven hq

end

end MetaMathlibExt
