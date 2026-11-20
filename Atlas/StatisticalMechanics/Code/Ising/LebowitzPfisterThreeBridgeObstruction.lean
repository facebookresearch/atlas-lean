/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.LebowitzPfisterTwoBridgeVariance

namespace StatMech.Ising

noncomputable section



def threeBridgeTiltVariance (t a b c : Real) : Real :=
  (t - 1) * (t + 1) *
      (-2 * a ^ 2 * t ^ 2 + a ^ 2 - 2 * a * b * t ^ 3 +
        2 * a * b * t + 2 * a * c * t ^ 4 - 4 * a * t -
        b ^ 2 * t ^ 4 + 2 * b ^ 2 * t ^ 2 + 4 * b * c * t ^ 3 -
        2 * b + 3 * c ^ 2 * t ^ 4 + 6 * c * t ^ 3 -
        6 * c * t - 3) /
    (1 + a * t + b * t ^ 2 + c * t ^ 3) ^ 2



def threeBridgeVarianceSkewPolynomial (t a b c : Real) : Real :=
  -a ^ 3 * b * t ^ 4 + a ^ 3 + 2 * a ^ 2 * b * c * t ^ 6 -
    3 * a ^ 2 * b * c * t ^ 4 + a ^ 2 * c * t ^ 4 +
    4 * a ^ 2 * c * t ^ 2 + a * b ^ 3 * t ^ 4 +
    3 * a * b ^ 2 * t ^ 4 - 2 * a * b ^ 2 * t ^ 2 +
    3 * a * b * c ^ 2 * t ^ 8 - 2 * a * b * c ^ 2 * t ^ 6 +
    2 * a * b * t ^ 2 - 3 * a * b - 2 * a * c ^ 2 * t ^ 6 +
    9 * a * c ^ 2 * t ^ 4 - a - b ^ 3 * c * t ^ 8 -
    4 * b ^ 2 * c * t ^ 6 - b ^ 2 * c * t ^ 4 +
    b * c ^ 3 * t ^ 8 - 9 * b * c * t ^ 4 +
    2 * b * c * t ^ 2 - 3 * c ^ 3 * t ^ 8 +
    6 * c ^ 3 * t ^ 6 - 6 * c * t ^ 2 + 3 * c




def threeBridgeVarianceSkewBernsteinCoeff
    (a b c : Real) : Fin 5 -> Real
  | 0 => a ^ 3 - 3 * a * b - a + 3 * c
  | 1 =>
      (2 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 5 * a * b - 2 * a +
        b * c + 3 * c) / 2
  | 2 =>
      -(a ^ 3 * b - 6 * a ^ 3 + 3 * a ^ 2 * b * c - 13 * a ^ 2 * c -
        a * b ^ 3 + 3 * a * b ^ 2 + 12 * a * b - 9 * a * c ^ 2 +
        6 * a + b ^ 2 * c + 3 * b * c) / 6
  | 3 =>
      -(a * b - 2 * a - 3 * c) * (a - b + c - 1) *
        (a + b + c + 1) / 2
  | 4 =>
      -(a - b + c - 1) * (a + b + c + 1) *
        (a * b - a - b * c - 3 * c)


theorem threeBridgeVarianceSkewPolynomial_eq_bernstein
    (t a b c : Real) :
    threeBridgeVarianceSkewPolynomial t a b c =
      threeBridgeVarianceSkewBernsteinCoeff a b c 0 * (1 - t ^ 2) ^ 4 +
      4 * threeBridgeVarianceSkewBernsteinCoeff a b c 1 * t ^ 2 *
        (1 - t ^ 2) ^ 3 +
      6 * threeBridgeVarianceSkewBernsteinCoeff a b c 2 * (t ^ 2) ^ 2 *
        (1 - t ^ 2) ^ 2 +
      4 * threeBridgeVarianceSkewBernsteinCoeff a b c 3 * (t ^ 2) ^ 3 *
        (1 - t ^ 2) +
      threeBridgeVarianceSkewBernsteinCoeff a b c 4 * (t ^ 2) ^ 4 := by
  unfold threeBridgeVarianceSkewPolynomial
    threeBridgeVarianceSkewBernsteinCoeff
  ring



theorem threeBridgeVarianceSkewPolynomial_nonpos_of_bernstein
    {t a b c : Real} (ht0 : 0 <= t) (ht1 : t <= 1)
    (hcoeff : forall i, threeBridgeVarianceSkewBernsteinCoeff a b c i <= 0) :
    threeBridgeVarianceSkewPolynomial t a b c <= 0 := by
  rw [threeBridgeVarianceSkewPolynomial_eq_bernstein]
  have htSq : 0 <= t ^ 2 := sq_nonneg t
  have htSqOne : t ^ 2 <= 1 := by nlinarith
  have hone : 0 <= 1 - t ^ 2 := sub_nonneg.mpr htSqOne
  have h0 := hcoeff (0 : Fin 5)
  have h1 := hcoeff (1 : Fin 5)
  have h2 := hcoeff (2 : Fin 5)
  have h3 := hcoeff (3 : Fin 5)
  have h4 := hcoeff (4 : Fin 5)
  have hterm0 :
      threeBridgeVarianceSkewBernsteinCoeff a b c 0 *
          (1 - t ^ 2) ^ 4 <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg h0 (pow_nonneg hone 4)
  have hterm1 :
      4 * threeBridgeVarianceSkewBernsteinCoeff a b c 1 * t ^ 2 *
          (1 - t ^ 2) ^ 3 <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h1) htSq)
      (pow_nonneg hone 3)
  have hterm2 :
      6 * threeBridgeVarianceSkewBernsteinCoeff a b c 2 * (t ^ 2) ^ 2 *
          (1 - t ^ 2) ^ 2 <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h2)
        (pow_nonneg htSq 2))
      (pow_nonneg hone 2)
  have hterm3 :
      4 * threeBridgeVarianceSkewBernsteinCoeff a b c 3 * (t ^ 2) ^ 3 *
          (1 - t ^ 2) <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h3)
        (pow_nonneg htSq 3)) hone
  have hterm4 :
      threeBridgeVarianceSkewBernsteinCoeff a b c 4 * (t ^ 2) ^ 4 <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg h4 (pow_nonneg htSq 4)
  linarith



theorem threeBridge_cube_inequality
    {u v w : Real}
    (hu0 : 0 <= u) (hu1 : u <= 1)
    (hv0 : 0 <= v) (hv1 : v <= 1)
    (hw0 : 0 <= w) (hw1 : w <= 1) :
    (u * v + u * w + v * w - 1) * (u + v + w) <=
      u * v * w * (u * v + u * w + v * w + 3) := by
  have huv1 : u * v <= 1 := mul_le_one₀ hu1 hv0 hv1
  have huu1 : u ^ 2 <= 1 := by
    simpa [pow_two] using mul_le_one₀ hu1 hu0 hu1
  have hvv1 : v ^ 2 <= 1 := by
    simpa [pow_two] using mul_le_one₀ hv1 hv0 hv1
  have hB0 : 0 <= (u + v) * (1 - u * v) :=
    mul_nonneg (add_nonneg hu0 hv0) (sub_nonneg.mpr huv1)
  have hB2 : 0 <= (1 - u ^ 2) * (1 - v ^ 2) :=
    mul_nonneg (sub_nonneg.mpr huu1) (sub_nonneg.mpr hvv1)
  have hB1 :
      0 <= (1 - u ^ 2) * (1 - v ^ 2) +
        2 * (u + v) * (1 - u * v) := by
    exact add_nonneg hB2
      (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hu0 hv0))
        (sub_nonneg.mpr huv1))
  apply sub_nonneg.mp
  rw [show
      u * v * w * (u * v + u * w + v * w + 3) -
          (u * v + u * w + v * w - 1) * (u + v + w) =
        (u + v) * (1 - u * v) * (1 - w) ^ 2 +
          ((1 - u ^ 2) * (1 - v ^ 2) +
            2 * (u + v) * (1 - u * v)) * w * (1 - w) +
          (1 - u ^ 2) * (1 - v ^ 2) * w ^ 2 by ring]
  exact add_nonneg
    (add_nonneg
      (mul_nonneg hB0 (sq_nonneg (1 - w)))
      (mul_nonneg (mul_nonneg hB1 hw0) (sub_nonneg.mpr hw1)))
    (mul_nonneg hB2 (sq_nonneg w))





theorem threeBridgeTiltVariance_le_neg_iff
    {t a b c : Real} (ht0 : 0 < t) (ht1 : t < 1)
    (hPp : 1 + a * t + b * t ^ 2 + c * t ^ 3 ≠ 0)
    (hPm : 1 - a * t + b * t ^ 2 - c * t ^ 3 ≠ 0) :
    threeBridgeTiltVariance t a b c <=
        threeBridgeTiltVariance (-t) a b c <->
      threeBridgeVarianceSkewPolynomial t a b c <= 0 := by
  let Pp := 1 + a * t + b * t ^ 2 + c * t ^ 3
  let Pm := 1 - a * t + b * t ^ 2 - c * t ^ 3
  let F := threeBridgeVarianceSkewPolynomial t a b c
  let C := 4 * t * (t - 1) * (t + 1)
  have hPp0 : Pp ≠ 0 := by simpa [Pp] using hPp
  have hPm0 : Pm ≠ 0 := by simpa [Pm] using hPm
  have hPp' : 0 < Pp ^ 2 := sq_pos_of_ne_zero hPp0
  have hPm' : 0 < Pm ^ 2 := sq_pos_of_ne_zero hPm0
  have hden : 0 < Pm ^ 2 * Pp ^ 2 := mul_pos hPm' hPp'
  have hC : C < 0 := by
    dsimp [C]
    have hleft : 0 < 4 * t := mul_pos (by norm_num) ht0
    have hmid : t - 1 < 0 := sub_neg.mpr ht1
    have hright : 0 < t + 1 := by linarith
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hleft hmid) hright
  have hdiff :
      threeBridgeTiltVariance (-t) a b c -
          threeBridgeTiltVariance t a b c =
        C * F / (Pm ^ 2 * Pp ^ 2) := by
    unfold threeBridgeTiltVariance
    simp only [neg_sq, neg_mul, mul_neg]
    rw [show 1 + -(a * t) + b * t ^ 2 + c * (-t) ^ 3 = Pm by
      dsimp [Pm]; ring]
    rw [show 1 + a * t + b * t ^ 2 + c * t ^ 3 = Pp by rfl]
    field_simp [hPp0, hPm0]
    dsimp [C, F, threeBridgeVarianceSkewPolynomial]
    ring
  constructor
  · intro hvar
    have hnonneg : 0 <= C * F / (Pm ^ 2 * Pp ^ 2) := by
      rw [← hdiff]
      exact sub_nonneg.mpr hvar
    have hnum : 0 <= C * F := by
      have hm := mul_nonneg hnonneg hden.le
      rw [div_mul_cancel₀ _ hden.ne'] at hm
      exact hm
    by_contra hF
    have hFpos : 0 < F := lt_of_not_ge hF
    exact (not_lt_of_ge hnum) (mul_neg_of_neg_of_pos hC hFpos)
  · intro hF
    apply sub_nonneg.mp
    rw [hdiff]
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos hC.le hF) hden.le




theorem threeBridge_basicCoefficientBounds_insufficient :
    let a : Real := 1 / 10
    let b : Real := 1 / 10
    let c : Real := 1
    0 <= a ∧ a <= 1 ∧ 0 <= b ∧ b <= 1 ∧ 0 <= c ∧ c <= 1 ∧
      a * a <= b ∧ b * a <= c ∧
      threeBridgeTiltVariance (-1 / 2) a b c <
        threeBridgeTiltVariance (1 / 2) a b c := by
  norm_num [threeBridgeTiltVariance]

end

end StatMech.Ising
