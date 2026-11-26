/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import all MathlibExt.Combinatorics.Enumerative.Partition.ReciprocalEulerDissection
import all MathlibExt.Combinatorics.Enumerative.Partition.EulerQuotientThreeDissection

/-!
# The 2-dissection of $f_1^4$

The main result is `qEulerProduct_fourth_two_dissection`, the 2-dissection of the fourth
power of the Euler product as an identity of integer power series.
-/

open PowerSeries

namespace MetaMathlibExt

namespace qEulerProduct_fourth_two_dissection

open one_div_f1_pow_four_eight_twelve_two_dissection

/-- Squaring the alternating square theta series and splitting the double sum by the parity
of the two indices gives the Euler-function form of the 2-dissection. -/
private lemma analytic_dissection {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    eulerFunction q ^ 4 * eulerFunction (q ^ 2) ^ 2 * eulerFunction (q ^ 4) ^ 2 *
        eulerFunction (q ^ 8) ^ 4 =
      eulerFunction (q ^ 4) ^ 12 - 4 * q * eulerFunction (q ^ 2) ^ 4 *
        eulerFunction (q ^ 8) ^ 8 := by
  have h2 := norm_sq_lt h
  have hs := sum_square (qEulerProduct_sq_div_three_dissection.square_sum h)
  have he := sum_square (theta_sum h2)
  have ho := (sum_square (shifted_sum (pow_ne_zero 2 hq) h2)).mul_left (-q)
  let term (p : ℤ × ℤ) := (-1 : ℂ) ^ p.1 * q ^ (p.1 * p.1) * ((-1 : ℂ) ^ p.2 * q ^ (p.2 * p.2))
  have hd := HasSum.sum (f := term ∘ parityEquiv)
    (he.congr_fun fun (a, b) ↦ by
      change (-1 : ℂ) ^ (a + b) * q ^ ((a + b) * (a + b)) *
          ((-1 : ℂ) ^ (a - b) * q ^ ((a - b) * (a - b))) =
          (q ^ 2) ^ (a * a) * (q ^ 2) ^ (b * b)
      have hneg : (-1 : ℂ) ^ (a + b) * (-1 : ℂ) ^ (a - b) = 1 := by
        rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), show (a + b) + (a - b) = 2 * a by ring,
          zpow_mul]
        norm_num
      have hq : q ^ ((a + b) * (a + b)) * q ^ ((a - b) * (a - b)) =
          (q ^ 2) ^ (a * a) * (q ^ 2) ^ (b * b) := by
        rw [← zpow_add₀ hq, ← zpow_add₀ (pow_ne_zero 2 hq)]
        rw [← zpow_natCast q 2, ← zpow_mul]
        congr 1
        ring
      have hcomb : (-1 : ℂ) ^ (a + b) * q ^ ((a + b) * (a + b)) *
          ((-1 : ℂ) ^ (a - b) * q ^ ((a - b) * (a - b))) =
            ((-1 : ℂ) ^ (a + b) * (-1 : ℂ) ^ (a - b)) *
              (q ^ ((a + b) * (a + b)) * q ^ ((a - b) * (a - b))) := by ring
      rw [hcomb, hneg, hq, one_mul])
    (ho.congr_fun fun (a, b) ↦ by
      change (-1 : ℂ) ^ (a + b + 1) * q ^ ((a + b + 1) * (a + b + 1)) *
          ((-1 : ℂ) ^ (a - b) * q ^ ((a - b) * (a - b))) =
          -q * ((q ^ 2) ^ (a * a + a) * (q ^ 2) ^ (b * b + b))
      have hneg : (-1 : ℂ) ^ (a + b + 1) * (-1 : ℂ) ^ (a - b) = -1 := by
        rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
          show (a + b + 1) + (a - b) = 2 * a + 1 by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
          zpow_mul]
        norm_num
      have hq : q ^ ((a + b + 1) * (a + b + 1)) * q ^ ((a - b) * (a - b)) =
          q * ((q ^ 2) ^ (a * a + a) * (q ^ 2) ^ (b * b + b)) := by
        rw [← zpow_add₀ hq, ← zpow_add₀ (pow_ne_zero 2 hq), ← zpow_natCast q 2, ← zpow_mul,
          ← zpow_one_add₀ hq]
        congr 1
        ring
      have hcomb : (-1 : ℂ) ^ (a + b + 1) * q ^ ((a + b + 1) * (a + b + 1)) *
          ((-1 : ℂ) ^ (a - b) * q ^ ((a - b) * (a - b))) =
            ((-1 : ℂ) ^ (a + b + 1) * (-1 : ℂ) ^ (a - b)) *
              (q ^ ((a + b + 1) * (a + b + 1)) * q ^ ((a - b) * (a - b))) := by ring
      rw [hcomb, hneg, hq]
      ring)
  have hid := hs.unique (parityEquiv.hasSum_iff.mp hd)
  have h2ne := euler_ne h2
  have h4ne := euler_ne (norm_sq_lt h2)
  have h8ne := euler_ne (norm_sq_lt (norm_sq_lt h2))
  simp only [← pow_mul] at hid h4ne h8ne
  norm_num1 at hid h4ne h8ne
  field_simp [euler_ne h, h2ne, h4ne, h8ne] at hid
  linear_combination hid

/-- The dissection with the shifted term moved to the left, for transfer to power series. -/
private lemma dissection_add :
    qEulerProduct 1 ^ 4 * qEulerProduct 2 ^ 2 * qEulerProduct 4 ^ 2 * qEulerProduct 8 ^ 4 +
        4 * X * qEulerProduct 2 ^ 4 * qEulerProduct 8 ^ 8 = qEulerProduct 4 ^ 12 := by
  have h1 : Represents (qEulerProduct 1) (fun q ↦ eulerFunction q) := by
    simpa using represents_euler 1 one_ne_zero
  have h2 := represents_euler 2 two_ne_zero
  have h4 := represents_euler 4 (by decide)
  have h8 := represents_euler 8 (by decide)
  have hc : Represents 4 (fun _ ↦ (4 : ℂ)) := by simpa using represents_const 4
  have hmain := h4.pow 12
  have hcorr := ((hc.mul represents_X).mul (h2.pow 4)).mul (h8.pow 8)
  have hlhs := (((h1.pow 4).mul (h2.pow 2)).mul (h4.pow 2)).mul (h8.pow 4)
  have hsum := hlhs.add hcorr
  refine hsum.eq_of_eval hmain fun q hq h ↦ ?_
  have hdis := analytic_dissection hq h
  simp only [id_eq]
  linear_combination hdis

end qEulerProduct_fourth_two_dissection

local notation "𝔣" => qEulerProduct

/-- **The 2-dissection of $f_1^4$.** For $k \ge 1$ let $f_k = \prod_{m \ge 1} (1 - q^{km})$, an
integer power series in $q$. Then
$$f_1^4 f_2^2 f_4^2 f_8^4 = f_4^{12} - 4 q f_2^4 f_8^8.$$
Dividing by $f_2^2 f_4^2 f_8^4$ gives
$f_1^4 = \frac{f_4^{10}}{f_2^2 f_8^4} - 4q \frac{f_2^2 f_8^4}{f_4^2}$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Lemma 1, (7)
(`integers-2025-A69-lem-1`). -/
public theorem qEulerProduct_fourth_two_dissection :
    𝔣 1 ^ 4 * 𝔣 2 ^ 2 * 𝔣 4 ^ 2 * 𝔣 8 ^ 4 = 𝔣 4 ^ 12 - 4 * X * 𝔣 2 ^ 4 * 𝔣 8 ^ 8 := by
  have h := qEulerProduct_fourth_two_dissection.dissection_add
  linear_combination h

end MetaMathlibExt
