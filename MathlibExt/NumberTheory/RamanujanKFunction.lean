/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProductSum
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProductDifference
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Ramanujan's function $k$

The product defining `ramanujanK` satisfies a modular equation relating its values at
$q$ and $q^2$ throughout the open unit disk. For $0 < |q| < 1$, the difference of the
ratios $k(q)/k(q^2)$ and $k(q^2)/k(q)$ is an eta quotient. The proof expresses the
ratios in terms of theta products and groups the Euler factors modulo five and ten.

## References

* Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's Function*,
  INTEGERS 26 (2026), Article A41, pp. 1–7, Section 1, Lemma 3, and Theorem 4.
* A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
  Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
  INTEGERS 24 (2024), Article A103, pp. 1–17, Equation (5) and Lemma 2, Equations (6)–(7).
* C. Adiga, B. C. Berndt, S. Bhargava, and G. N. Watson, *Chapter 16 of Ramanujan's Second
  Notebook: Theta-Functions and q-Series*, Mem. Amer. Math. Soc. 53 (1985), no. 315, pp. 1–85,
  Entries 19 and 29 (Jacobi triple product and theta addition formulas).
-/

namespace MetaMathlibExt

open QPochhammer

@[expose] public section

/-- **Ramanujan's function $k(q)$.** For a complex number $q$, Ramanujan's function is
$$
k(q) = \frac{q\,(q;q^{10})_\infty (q^2;q^{10})_\infty (q^8;q^{10})_\infty (q^9;q^{10})_\infty}
{(q^3;q^{10})_\infty (q^4;q^{10})_\infty (q^6;q^{10})_\infty (q^7;q^{10})_\infty},
$$
where $(a;x)_\infty$ is the raw infinite q-Pochhammer product $\prod_{n \ge 0} (1 - a x^n)$
(equal to $1$ by convention when this product does not converge unconditionally), and a
quotient by $0$ is read as $0$.

For $|q| < 1$ this is the product representation of $k(q) = r(q)\,r(q^2)^2$, where $r$ is the
Rogers–Ramanujan continued fraction.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Section 1 (product representation of `k(q)`). -/
noncomputable def ramanujanK (q : ℂ) : ℂ :=
  q * (qPochhammerInfRaw q (q ^ 10) * qPochhammerInfRaw (q ^ 2) (q ^ 10) *
        qPochhammerInfRaw (q ^ 8) (q ^ 10) * qPochhammerInfRaw (q ^ 9) (q ^ 10)) /
    (qPochhammerInfRaw (q ^ 3) (q ^ 10) * qPochhammerInfRaw (q ^ 4) (q ^ 10) *
        qPochhammerInfRaw (q ^ 6) (q ^ 10) * qPochhammerInfRaw (q ^ 7) (q ^ 10))

/-- **Ramanujan's function $k$ vanishes at $0$.** Ramanujan's function satisfies $k(0) = 0$.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Section 1 (product representation of `k(q)`). -/
theorem ramanujanK_zero : ramanujanK 0 = 0 := by
  simp [ramanujanK]

end

namespace ramanujanK_sq_relation

local notation "P" => qPochhammerInfRaw
local notation "θ" => ramanujanThetaRaw

private lemma norm_pow_lt {q : ℂ} (hq : ‖q‖ < 1) {n : ℕ} (hn : n ≠ 0) : ‖q ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hq hn

private lemma poch_ne_zero {a Q : ℂ} (ha : ‖a‖ < 1) (hQ : ‖Q‖ < 1) : P a Q ≠ 0 := by
  simp only [qPochhammerInfRaw, sub_eq_add_neg]
  apply tprod_one_add_ne_zero_of_summable
  · intro n h
    have heq : a * Q ^ n = 1 := by linear_combination -h
    have hlt : ‖a * Q ^ n‖ < 1 := by
      rw [norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (norm_nonneg a) (pow_le_one₀ (norm_nonneg Q) hQ.le)).trans_lt ha
    simp [heq] at hlt
  · simpa [norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg Q) hQ).mul_left ‖a‖

private lemma poch_pair {Q : ℂ} (hQ : ‖Q‖ < 1) (a : ℂ) :
    P a Q * P (-a) Q = P (a ^ 2) (Q ^ 2) := by
  apply ((hasProd_qPochhammerInf a Q hQ).mul (hasProd_qPochhammerInf (-a) Q hQ)).unique
  exact (hasProd_qPochhammerInf (a ^ 2) (Q ^ 2) (norm_pow_lt hQ two_ne_zero)).congr_fun
    fun n => by ring

private lemma twice_triangle (n : ℤ) :
    2 * ((n * (n - 1) / 2).toNat : ℤ) = n * (n - 1) := by
  have hn : 0 ≤ n * (n - 1) := by
    rcases le_or_gt n 0 with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
    · exact mul_nonneg h.le (by omega)
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn (by decide))]
  exact Int.two_mul_ediv_two_of_even (Int.even_mul_pred_self n)

-- The Jacobi triple product in the parameters of Ramanujan's bilateral series.
private lemma theta_prod {t z : ℂ} (ht : ‖t‖ < 1) (hz : z ≠ 0) :
    θ (z * t) (z⁻¹ * t) =
      P (t ^ 2) (t ^ 2) * (P (-(z * t)) (t ^ 2) * P (-(z⁻¹ * t)) (t ^ 2)) := by
  have hterm (n : ℤ) : ramanujanThetaTerm (z * t) (z⁻¹ * t) n =
      z ^ n * t ^ (n * n).toNat := by
    let u := (n * (n + 1) / 2).toNat
    let v := (n * (n - 1) / 2).toNat
    have hu : 2 * (u : ℤ) = n * (n + 1) := by
      simpa only [u, show -n * (-n - 1) = n * (n + 1) by ring] using twice_triangle (-n)
    have hv : 2 * (v : ℤ) = n * (n - 1) := twice_triangle n
    change (z * t) ^ u * (z⁻¹ * t) ^ v = _
    rw [mul_pow, mul_pow, mul_mul_mul_comm, ← pow_add]
    congr 1
    · rw [← zpow_natCast z u, ← zpow_natCast z⁻¹ v, inv_zpow', ← zpow_add₀ hz]
      congr 1
      linarith
    · congr 1
      apply Int.ofNat_inj.mp
      push_cast
      rw [Int.toNat_of_nonneg (mul_self_nonneg n)]
      linarith
  obtain ⟨-, -, hj⟩ := Analysis.SpecialFunctions.JacobiTripleProduct.jacobi_triple_product z t hz ht
  rw [ramanujanThetaRaw]
  simp_rw [hterm]
  rw [hj, ← mul_assoc]
  have ht₂ := norm_pow_lt ht two_ne_zero
  apply HasProd.tprod_eq
  apply (((hasProd_qPochhammerInf _ _ ht₂).mul (hasProd_qPochhammerInf _ _ ht₂)).mul
    (hasProd_qPochhammerInf _ _ ht₂)).congr_fun
  intro n
  simp only [neg_mul, sub_neg_eq_add, pow_add, pow_mul]
  ring

private noncomputable def euler (q : ℂ) : ℂ := P (q ^ 10) (q ^ 10)

private noncomputable def minusTheta (q : ℂ) (i : ℕ) : ℂ := θ (-q ^ i) (-q ^ (10 - i))

private noncomputable def plusTheta (q : ℂ) (i : ℕ) : ℂ := θ (q ^ i) (q ^ (10 - i))

private lemma theta_prod_of_mul_eq_sq {t a b : ℂ} (ht : ‖t‖ < 1) (ht0 : t ≠ 0)
    (ha : a ≠ 0) (hab : a * b = t ^ 2) :
    θ a b = P (t ^ 2) (t ^ 2) * (P (-a) (t ^ 2) * P (-b) (t ^ 2)) := by
  have h₁ : a / t * t = a := div_mul_cancel₀ _ ht0
  have h₂ : (a / t)⁻¹ * t = b := by
    rw [inv_div]
    field_simp
    linear_combination -hab
  simpa only [h₁, h₂] using theta_prod ht (div_ne_zero ha ht0)

private lemma theta_ten {q a b : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha : a ≠ 0)
    (hab : a * b = q ^ 10) :
    θ a b = euler q * (P (-a) (q ^ 10) * P (-b) (q ^ 10)) := by
  simpa only [← pow_mul, euler] using theta_prod_of_mul_eq_sq
    (norm_pow_lt (n := 5) hq (by decide)) (pow_ne_zero 5 hq0) ha
    (by simpa only [← pow_mul] using hab)

private noncomputable def pair (q : ℂ) (i : ℕ) : ℂ :=
  P (q ^ i) (q ^ 10) * P (q ^ (10 - i)) (q ^ 10)

private lemma minus_eq {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {i : ℕ} (hi : i ≤ 10) :
    minusTheta q i = euler q * pair q i := by
  have hm : q ^ i * q ^ (10 - i) = q ^ 10 := by rw [← pow_add, Nat.add_sub_of_le hi]
  simpa only [minusTheta, pair, neg_neg] using
    theta_ten (b := -q ^ (10 - i)) hq hq0 (neg_ne_zero.mpr (pow_ne_zero i hq0))
      (by simpa only [neg_mul_neg] using hm)

private lemma euler_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : euler q ≠ 0 :=
  poch_ne_zero (norm_pow_lt hq (by decide)) (norm_pow_lt hq (by decide))

private lemma minus_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (i : ℕ) (hi : 0 < i := by decide) (hi' : i < 10 := by decide) : minusTheta q i ≠ 0 := by
  rw [minus_eq hq hq0 hi'.le, pair]
  have hQ := norm_pow_lt (n := 10) hq (by decide)
  exact mul_ne_zero (euler_ne_zero hq) (mul_ne_zero
    (poch_ne_zero (norm_pow_lt hq hi.ne') hQ) (poch_ne_zero (norm_pow_lt hq (by omega)) hQ))

-- Pairing factors with opposite signs doubles the exponents.
private lemma theta_pair {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (i : ℕ) (hi : i ≤ 10 := by decide) :
    minusTheta q i * plusTheta q i =
      (euler q ^ 2 / euler (q ^ 2)) * minusTheta (q ^ 2) i := by
  have hm : q ^ i * q ^ (10 - i) = q ^ 10 := by rw [← pow_add, Nat.add_sub_of_le hi]
  have h₂ := norm_pow_lt hq two_ne_zero
  rw [minus_eq hq hq0 hi, plusTheta, theta_ten hq hq0 (pow_ne_zero i hq0) hm,
    minus_eq h₂ (pow_ne_zero 2 hq0) hi]
  have hQ := norm_pow_lt (n := 10) hq (by decide)
  have hp (j : ℕ) : P (q ^ j) (q ^ 10) * P (-q ^ j) (q ^ 10) =
      P ((q ^ 2) ^ j) ((q ^ 2) ^ 10) := by
    simpa only [← pow_mul, mul_comm j 2, mul_comm 10 2] using poch_pair hQ (q ^ j)
  unfold pair
  rw [← hp, ← hp]
  field_simp [euler_ne_zero h₂]

private lemma k_eq {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    ramanujanK q = q * minusTheta q 1 * minusTheta q 2 / (minusTheta q 3 * minusTheta q 4) := by
  simp (disch := decide) only [minus_eq hq hq0, ramanujanK, pair, pow_one]
  field_simp [euler_ne_zero hq]

-- The even and odd parts of the theta product for two opposite choices of signs.
private lemma dissection {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (i m n : ℕ) (h : i + m + n = 5) :
    let j := i + 2 * m
    let evenPart := minusTheta (q ^ 2) (i + n) * minusTheta (q ^ 2) (i + m)
    let oddPart := q ^ i * minusTheta (q ^ 2) m * minusTheta (q ^ 2) n
    minusTheta q i * plusTheta q j = evenPart - oddPart ∧
      plusTheta q i * minusTheta q j = evenPart + oddPart := by
  dsimp only
  let j := i + 2 * m
  have prodPow {a b c : ℕ} (h : a + b = 2 * c) :
      q ^ a * q ^ b = (q ^ 2) ^ c := by rw [← pow_mul, ← pow_add, h]
  have divPow {a b c : ℕ} (h : a = b + 2 * c) :
      q ^ a / q ^ b = (q ^ 2) ^ c := by
    rw [h, pow_add, pow_mul, mul_div_cancel_left₀ _ (pow_ne_zero b hq0)]
  have sqPow {a c : ℕ} (h : 2 * i + (10 - i) + a = 2 * c) :
      (q ^ i) ^ 2 * q ^ (10 - i) * q ^ a = (q ^ 2) ^ c := by
    rw [← pow_mul, ← pow_add, ← pow_add, ← pow_mul]
    congr 1
    omega
  have hj : j = i + 2 * m := rfl
  have hi₁ : q ^ i * q ^ (10 - i) = q ^ 10 := by rw [← pow_add]; congr 1; omega
  have hj₁ : q ^ j * q ^ (10 - j) = q ^ 10 := by rw [← pow_add]; congr 1; omega
  have h₁ := ramanujanTheta_mul_of_mul_eq
    (a := -q ^ i) (b := -q ^ (10 - i)) (c := q ^ j) (d := q ^ (10 - j))
    (neg_ne_zero.mpr (pow_ne_zero i hq0))
    (by rw [neg_mul_neg, hi₁]; exact norm_pow_lt hq (by decide))
    (by rw [neg_mul_neg, hi₁, hj₁])
  have h₂ := ramanujanTheta_mul_of_mul_eq
    (a := q ^ i) (b := q ^ (10 - i)) (c := -q ^ j) (d := -q ^ (10 - j))
    (pow_ne_zero i hq0) (by rw [hi₁]; exact norm_pow_lt hq (by decide))
    (by rw [neg_mul_neg, hi₁, hj₁])
  simpa only [minusTheta, plusTheta, neg_mul, mul_neg, div_neg, neg_div, neg_sq,
    prodPow (show i + (10 - j) = 2 * (i + n) by omega),
    prodPow (show i + j = 2 * (i + m) by omega),
    prodPow (show 10 - i + j = 2 * (10 - (i + n)) by omega),
    prodPow (show 10 - i + (10 - j) = 2 * (10 - (i + m)) by omega),
    divPow hj, divPow (show 10 - j = i + 2 * n by omega),
    sqPow (show 2 * i + (10 - i) + (10 - j) = 2 * (10 - m) by omega),
    sqPow (show 2 * i + (10 - i) + j = 2 * (10 - n) by omega), sub_eq_add_neg, ← hj] using
    And.intro h₁ h₂

-- Eliminate the products with positive theta parameters. Capital letters denote the
-- four negative-parameter theta values at q, and lower-case letters those at q².
private lemma eliminate {q H A B C D a b c d A' B' C' D' : ℂ}
    (hC : C ≠ 0) (hD : D ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hA₂ : A * A' = H * a) (hB₂ : B * B' = H * b)
    (hC₂ : C * C' = H * c) (hD₂ : D * D' = H * d)
    (hodd : A * C' - A' * C = -2 * q * a * c)
    (hpos : B' * D = d * c + q ^ 2 * a * b)
    (hneg : B * D' = d * c - q ^ 2 * a * b) :
    let X := q * A * B / (C * D)
    let Y := q ^ 2 * a * b / (c * d)
    X ^ 2 - Y + 2 * X * Y + X ^ 2 * Y + Y ^ 2 = 0 := by
  have h₁ : H * (c * A ^ 2 - a * C ^ 2) + 2 * q * a * c * A * C = 0 := by
    linear_combination A * C * hodd - A ^ 2 * hC₂ + C ^ 2 * hA₂
  have h₂ : (c * d + q ^ 2 * a * b) * B = H * b * D := by
    linear_combination D * hB₂ - B * hpos
  have h₃ : (c * d - q ^ 2 * a * b) * D = H * d * B := by
    linear_combination B * hD₂ - D * hneg
  dsimp only
  field_simp [hC, hD, hc, hd]
  linear_combination q ^ 2 * B * b * D * d * h₁ +
    q ^ 2 * A ^ 2 * B * c * d * h₂ - q ^ 2 * a * b * C ^ 2 * D * h₃

end ramanujanK_sq_relation

open ramanujanK_sq_relation

/-- **Modular equation of degree 2 for Ramanujan's function $k$.** For every complex number $q$
with $|q| < 1$, the values $X = k(q)$ and $Y = k(q^2)$ of Ramanujan's function satisfy
$X^2 - Y + 2XY + X^2 Y + Y^2 = 0$.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Theorem 4 (`integers-2026-A41-thm-4`). -/
public theorem ramanujanK_sq_relation (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanK q ^ 2 - ramanujanK (q ^ 2) + 2 * ramanujanK q * ramanujanK (q ^ 2) +
        ramanujanK q ^ 2 * ramanujanK (q ^ 2) + ramanujanK (q ^ 2) ^ 2 = 0 := by
  by_cases hq0 : q = 0
  · simp [hq0, ramanujanK_zero]
  have hq₂ := norm_pow_lt hq two_ne_zero
  have hq₂0 := pow_ne_zero 2 hq0
  rw [k_eq hq hq0, k_eq hq₂ hq₂0]
  -- Use the pairs of residues (1, 3) and (2, 4) modulo 10.
  have h₁ := dissection hq hq0 1 1 3 (by decide)
  have h₂ := dissection hq hq0 2 1 2 (by decide)
  apply eliminate (minus_ne_zero hq hq0 3) (minus_ne_zero hq hq0 4)
    (minus_ne_zero hq₂ hq₂0 3) (minus_ne_zero hq₂ hq₂0 4)
    (theta_pair hq hq0 1) (theta_pair hq hq0 2) (theta_pair hq hq0 3) (theta_pair hq hq0 4)
    _ h₂.2 h₂.1
  linear_combination h₁.1 - h₁.2

namespace ramanujanK_div_sub_div_sq

local notation "P" => qPochhammerInfRaw
local notation "θ" => ramanujanThetaRaw

private lemma plusTheta_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (i : ℕ) (hi : 0 < i := by decide) (hi' : i < 10 := by decide) : plusTheta q i ≠ 0 := by
  intro h
  have h₂ := norm_pow_lt hq two_ne_zero
  have hz := theta_pair hq hq0 i hi'.le
  rw [h, mul_zero] at hz
  exact mul_ne_zero (div_ne_zero (pow_ne_zero 2 (euler_ne_zero hq)) (euler_ne_zero h₂))
    (minus_ne_zero h₂ (pow_ne_zero 2 hq0) i hi hi') hz.symm

-- Converting the negative-parameter theta values at q² to paired values at q
-- cancels the negative-parameter values in the quotient.
private lemma k_ratio {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    ramanujanK q / ramanujanK (q ^ 2) =
      (plusTheta q 3 * plusTheta q 4) / (q * plusTheta q 1 * plusTheta q 2) := by
  have h₂ := norm_pow_lt hq two_ne_zero
  have hE := div_ne_zero (pow_ne_zero 2 (euler_ne_zero hq)) (euler_ne_zero h₂)
  have hpair (i : ℕ) (hi : i ≤ 10 := by decide) :
      minusTheta (q ^ 2) i = minusTheta q i * plusTheta q i / (euler q ^ 2 / euler (q ^ 2)) := by
    apply (eq_div_iff hE).2
    rw [mul_comm]
    exact (theta_pair hq hq0 i hi).symm
  rw [k_eq hq hq0, k_eq h₂ (pow_ne_zero 2 hq0), hpair 1, hpair 2, hpair 3, hpair 4]
  field_simp [hq0, euler_ne_zero hq, euler_ne_zero h₂,
    minus_ne_zero hq hq0 1, minus_ne_zero hq hq0 2,
    minus_ne_zero hq hq0 3, minus_ne_zero hq hq0 4,
    plusTheta_ne_zero hq hq0 1, plusTheta_ne_zero hq hq0 2,
    plusTheta_ne_zero hq hq0 3, plusTheta_ne_zero hq hq0 4]

-- The common Pochhammer factors at the four nonzero residues modulo five.
private noncomputable def levelFiveFactors (q s : ℂ) : ℂ :=
  P (s * q ^ 1) (q ^ 5) * P (s * q ^ 2) (q ^ 5) *
    P (s * q ^ 3) (q ^ 5) * P (s * q ^ 4) (q ^ 5)

private lemma euler_split_five {q : ℂ} (hq : ‖q‖ < 1) :
    P q q = P (q ^ 5) (q ^ 5) * levelFiveFactors q 1 := by
  rw [qPochhammerInfRaw_split q q hq 5]
  simp only [levelFiveFactors, Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.val_succ,
    Fin.val_zero, Nat.reduceAdd, one_mul, mul_one, ← pow_succ', pow_one]
  ring

private lemma plusTheta_prod {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    plusTheta q 3 * plusTheta q 4 * (plusTheta q 1 * plusTheta q 2) =
      euler q ^ 4 * levelFiveFactors q (-1) := by
  have hθ (i : ℕ) (hi : i ≤ 10 := by decide) :
      plusTheta q i = euler q * (P (-q ^ i) (q ^ 10) * P (-q ^ (10 - i)) (q ^ 10)) :=
    theta_ten hq hq0 (pow_ne_zero _ hq0) (by rw [← pow_add, Nat.add_sub_of_le hi])
  have hsplit (i : ℕ) : P (-q ^ i) (q ^ 5) = P (-q ^ i) (q ^ 10) * P (-q ^ (i + 5)) (q ^ 10) := by
    have h₅ := norm_pow_lt (n := 5) hq (by decide)
    simpa only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one,
      ← pow_mul, Nat.reduceMul, neg_mul, ← pow_add, Nat.add_zero] using
      qPochhammerInfRaw_split (-q ^ i) _ h₅ 2
  rw [hθ 1, hθ 2, hθ 3, hθ 4]
  simp only [levelFiveFactors, neg_one_mul, Nat.reduceSub, hsplit, Nat.reduceAdd]
  ring

private lemma theta_prod_five {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (s : ℂ) (hs : s * s = 1) :
    θ (s * q ^ 1) (s * q ^ 4) * θ (s * q ^ 2) (s * q ^ 3) =
      P (q ^ 5) (q ^ 5) ^ 2 * levelFiveFactors q (-s) := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (q ^ 5) zero_lt_two
  have ht0 : t ≠ 0 := by rintro rfl; exact pow_ne_zero 5 hq0 (by simpa using ht.symm)
  have htn : ‖t‖ < 1 := (sq_lt_one_iff₀ (norm_nonneg _)).mp (by
    rw [← norm_pow, ht]
    exact norm_pow_lt hq (by decide))
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hθ (i j : ℕ) (hij : i + j = 5 := by decide) :
      θ (s * q ^ i) (s * q ^ j) = P (q ^ 5) (q ^ 5) * (P (-s * q ^ i) (q ^ 5) *
        P (-s * q ^ j) (q ^ 5)) := by
    simpa only [ht, neg_mul] using theta_prod_of_mul_eq_sq htn ht0
      (mul_ne_zero hs0 (pow_ne_zero _ hq0)) (b := s * q ^ j)
      (by rw [mul_mul_mul_comm, hs, one_mul, ← pow_add, hij, ht])
  rw [hθ 1 4, hθ 2 3, levelFiveFactors]
  ring

-- The sum and difference formulas at parameters (q, q⁴, q², q³).
private lemma theta_dissection_five {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (plusTheta q 3 * plusTheta q 4) ^ 2 - (q * plusTheta q 1 * plusTheta q 2) ^ 2 =
      P (q ^ 5) (q ^ 5) ^ 4 * levelFiveFactors q 1 * levelFiveFactors q (-1) := by
  let S := θ (q ^ 1) (q ^ 4) * θ (q ^ 2) (q ^ 3)
  let T := θ (-q ^ 1) (-q ^ 4) * θ (-q ^ 2) (-q ^ 3)
  let A := plusTheta q 3 * plusTheta q 4
  let B := q * plusTheta q 1 * plusTheta q 2
  have hab : q ^ 1 * q ^ 4 = q ^ 2 * q ^ 3 := by rw [← pow_add, ← pow_add]
  have hn : ‖q ^ 1 * q ^ 4‖ < 1 := by rw [← pow_add]; exact norm_pow_lt hq (by decide)
  have hsum : S + T = 2 * A := by
    have h := ramanujanTheta_mul_add_mul_neg hab hn
    simp only [← pow_add, Nat.reduceAdd] at h
    simpa only [S, T, A, plusTheta, Nat.reduceSub, mul_assoc] using h
  have hsub : S - T = 2 * B := by
    have h42 : q ^ 4 / q ^ 2 = q ^ 2 := by field_simp
    have h43 : q ^ 4 / q ^ 3 = q ^ 1 := by field_simp
    have h := ramanujanTheta_mul_sub_mul_neg hab hn (pow_ne_zero _ hq0) (pow_ne_zero _ hq0)
    simp only [h42, h43, ← pow_mul, Nat.reduceMul, ← pow_add, Nat.reduceAdd] at h
    rw [show S - T = _ from h]
    dsimp only [B, plusTheta]
    simp only [Nat.reduceSub, pow_one]
    ring
  have hs : S = A + B := by linear_combination (hsum + hsub) / 2
  have ht : T = A - B := by linear_combination (hsum - hsub) / 2
  have hp := theta_prod_five hq hq0 1 (by simp)
  have hm := theta_prod_five hq hq0 (-1) (by norm_num)
  simp only [one_mul, neg_one_mul, neg_neg] at hp hm
  change A ^ 2 - B ^ 2 = _
  calc
    _ = S * T := by rw [hs, ht]; ring
    _ = _ := by rw [show S = _ from hp, show T = _ from hm]; ring

end ramanujanK_div_sub_div_sq

open ramanujanK_div_sub_div_sq in
/-- **Ramanujan's function $k$ at $q$ and $q^2$ as an eta quotient.** For every complex number
$q$ with $0 < |q| < 1$, Ramanujan's function $k$ satisfies
$$
\frac{k(q)}{k(q^2)} - \frac{k(q^2)}{k(q)} =
\frac{(q;q)_\infty (q^5;q^5)_\infty^3}{q\,(q^{10};q^{10})_\infty^4},
$$
where $(a;x)_\infty = \prod_{n \ge 0} (1 - a x^n)$ is the infinite q-Pochhammer product.

Source: Russelle Guadalupe, *New Proofs of Certain Theta Function Identities via Ramanujan's
Function*, INTEGERS 26 (2026), Article A41, Lemma 3 (`integers-2026-A41-lem-3`). -/
public theorem ramanujanK_div_sub_div_sq (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    ramanujanK q / ramanujanK (q ^ 2) - ramanujanK (q ^ 2) / ramanujanK q =
      qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 5) (q ^ 5) ^ 3 /
        (q * qPochhammerInfRaw (q ^ 10) (q ^ 10) ^ 4) := by
  let A := plusTheta q 3 * plusTheta q 4
  let B := q * plusTheta q 1 * plusTheta q 2
  have hA : A ≠ 0 := mul_ne_zero (plusTheta_ne_zero hq hq0 3) (plusTheta_ne_zero hq hq0 4)
  have hB : B ≠ 0 := mul_ne_zero (mul_ne_zero hq0 (plusTheta_ne_zero hq hq0 1))
    (plusTheta_ne_zero hq hq0 2)
  have hr : ramanujanK q / ramanujanK (q ^ 2) = A / B := k_ratio hq hq0
  have hs : ramanujanK (q ^ 2) / ramanujanK q = B / A := by
    rw [← inv_div (ramanujanK q), hr, inv_div]
  have hden : A * B = q * (euler q ^ 4 * levelFiveFactors q (-1)) := by
    rw [← plusTheta_prod hq hq0]
    dsimp only [A, B]
    ring
  rw [hr, hs]
  calc
    _ = (A ^ 2 - B ^ 2) / (A * B) := by field_simp
    _ = _ := by
      have hEuler : q * euler q ^ 4 ≠ 0 := mul_ne_zero hq0 (pow_ne_zero 4 (euler_ne_zero hq))
      apply (div_eq_div_iff (mul_ne_zero hA hB) hEuler).2
      rw [show A ^ 2 - B ^ 2 = _ from theta_dissection_five hq hq0, hden, euler_split_five hq]
      ring

end MetaMathlibExt
