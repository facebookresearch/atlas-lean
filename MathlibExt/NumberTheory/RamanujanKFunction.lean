/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProduct
import Mathlib.Tactic.LinearCombination

/-!
# Ramanujan's function $k$

The product defining `ramanujanK` satisfies a modular equation relating its values at
$q$ and $q^2$ throughout the open unit disk.
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

private lemma theta_ten {q a b : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha : a ≠ 0)
    (hab : a * b = q ^ 10) :
    θ a b = euler q * (P (-a) (q ^ 10) * P (-b) (q ^ 10)) := by
  have h₁ : a / q ^ 5 * q ^ 5 = a := div_mul_cancel₀ _ (pow_ne_zero _ hq0)
  have h₂ : (a / q ^ 5)⁻¹ * q ^ 5 = b := by
    rw [inv_div]
    field_simp
    linear_combination -hab
  have h := theta_prod (norm_pow_lt (n := 5) hq (by decide)) (div_ne_zero ha (pow_ne_zero 5 hq0))
  simpa only [h₁, h₂, ← pow_mul, euler] using h

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

end MetaMathlibExt
