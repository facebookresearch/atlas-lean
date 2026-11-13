/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterThreeBridgeClosure
import Code.Ising.LebowitzPfisterStrongMarkedSite











namespace StatMech.Ising

noncomputable section


def fourBridgeTiltVariance (t a b c d : Real) : Real :=
  (t - 1) * (t + 1) *
      (-3 * a ^ 2 * t ^ 2 + a ^ 2 - 4 * a * b * t ^ 3 +
        2 * a * b * t + 6 * a * d * t ^ 5 - 4 * a * d * t ^ 3 -
        6 * a * t - 2 * b ^ 2 * t ^ 4 + 2 * b ^ 2 * t ^ 2 -
        2 * b * c * t ^ 5 + 4 * b * c * t ^ 3 +
        2 * b * d * t ^ 6 + 2 * b * d * t ^ 4 - 2 * b * t ^ 2 -
        2 * b - c ^ 2 * t ^ 6 + 3 * c ^ 2 * t ^ 4 +
        6 * c * d * t ^ 5 + 4 * c * t ^ 3 - 6 * c * t +
        4 * d ^ 2 * t ^ 6 + 12 * d * t ^ 4 - 12 * d * t ^ 2 - 4) /
    (1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4) ^ 2



def fourBridgeTiltMean (t a b c d : Real) : Real :=
  4 * t + (1 - t ^ 2) *
    (a + 2 * b * t + 3 * c * t ^ 2 + 4 * d * t ^ 3) /
      (1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4)



theorem hasDerivAt_fourBridgeTiltMean_tanh
    (r a b c d : Real)
    (hP : 1 + a * Real.tanh r + b * Real.tanh r ^ 2 +
      c * Real.tanh r ^ 3 + d * Real.tanh r ^ 4 ≠ 0) :
    HasDerivAt (fun u => fourBridgeTiltMean (Real.tanh u) a b c d)
      (fourBridgeTiltVariance (Real.tanh r) a b c d) r := by
  let t := Real.tanh r
  let U : Real -> Real := fun u => 1 - u ^ 2
  let Q : Real -> Real := fun u =>
    a + 2 * b * u + 3 * c * u ^ 2 + 4 * d * u ^ 3
  let P : Real -> Real := fun u =>
    1 + a * u + b * u ^ 2 + c * u ^ 3 + d * u ^ 4
  have hU : HasDerivAt U (-2 * t) t := by
    dsimp [U]
    convert (hasDerivAt_const t 1).sub ((hasDerivAt_id t).pow 2) using 1 <;>
      simp [id_eq] <;> ring
  have hQ : HasDerivAt Q
      (2 * b + 6 * c * t + 12 * d * t ^ 2) t := by
    dsimp [Q]
    convert (((hasDerivAt_const t a).add
      ((hasDerivAt_id t).const_mul (2 * b))).add
      (((hasDerivAt_id t).pow 2).const_mul (3 * c))).add
      (((hasDerivAt_id t).pow 3).const_mul (4 * d)) using 1 <;>
      simp [id_eq] <;> ring
  have hPderiv : HasDerivAt P
      (a + 2 * b * t + 3 * c * t ^ 2 + 4 * d * t ^ 3) t := by
    dsimp [P]
    convert ((((hasDerivAt_const t 1).add
      ((hasDerivAt_id t).const_mul a)).add
      (((hasDerivAt_id t).pow 2).const_mul b)).add
      (((hasDerivAt_id t).pow 3).const_mul c)).add
      (((hasDerivAt_id t).pow 4).const_mul d) using 1 <;>
      simp [id_eq] <;> ring
  have hP' : P t ≠ 0 := by simpa [P, t] using hP
  have houter := ((hasDerivAt_id t).const_mul 4).add
    ((hU.mul hQ).div hPderiv hP')
  have htderiv : HasDerivAt Real.tanh (1 - t ^ 2) r := by
    have h := hasDerivAt_tanh r
    convert h using 1
    dsimp [t]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos r).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq r]
  have hcomp := houter.comp r htderiv
  change HasDerivAt
    (fun u => 4 * Real.tanh u +
      U (Real.tanh u) * Q (Real.tanh u) / P (Real.tanh u)) _ r at hcomp
  convert hcomp using 1
  change fourBridgeTiltVariance t a b c d = _
  let den := 1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4
  let q := a + 2 * b * t + 3 * c * t ^ 2 + 4 * d * t ^ 3
  let qp := 2 * b + 6 * c * t + 12 * d * t ^ 2
  have hden : den ≠ 0 := by simpa [den, t] using hP
  dsimp [U, Q, P, fourBridgeTiltVariance]
  simp only [mul_one]
  change
    (t - 1) * (t + 1) *
        (-3 * a ^ 2 * t ^ 2 + a ^ 2 - 4 * a * b * t ^ 3 +
          2 * a * b * t + 6 * a * d * t ^ 5 - 4 * a * d * t ^ 3 -
          6 * a * t - 2 * b ^ 2 * t ^ 4 + 2 * b ^ 2 * t ^ 2 -
          2 * b * c * t ^ 5 + 4 * b * c * t ^ 3 +
          2 * b * d * t ^ 6 + 2 * b * d * t ^ 4 - 2 * b * t ^ 2 -
          2 * b - c ^ 2 * t ^ 6 + 3 * c ^ 2 * t ^ 4 +
          6 * c * d * t ^ 5 + 4 * c * t ^ 3 - 6 * c * t +
          4 * d ^ 2 * t ^ 6 + 12 * d * t ^ 4 - 12 * d * t ^ 2 - 4) /
        den ^ 2 =
      (4 + (((-2 * t) * q + (1 - t ^ 2) * qp) * den -
        (1 - t ^ 2) * q * q) / den ^ 2) * (1 - t ^ 2)
  field_simp [hden]
  ring


def fourBridgeVarianceSkewPolynomial (t a b c d : Real) : Real :=
  -a ^ 3 * b * t ^ 4 - 6 * a ^ 3 * d * t ^ 6 +
    3 * a ^ 3 * d * t ^ 4 + a ^ 3 + 2 * a ^ 2 * b * c * t ^ 6 -
    3 * a ^ 2 * b * c * t ^ 4 - 9 * a ^ 2 * c * d * t ^ 8 +
    2 * a ^ 2 * c * d * t ^ 6 + a ^ 2 * c * t ^ 4 +
    4 * a ^ 2 * c * t ^ 2 + a * b ^ 3 * t ^ 4 +
    a * b ^ 2 * d * t ^ 8 + 4 * a * b ^ 2 * d * t ^ 6 +
    3 * a * b ^ 2 * t ^ 4 - 2 * a * b ^ 2 * t ^ 2 +
    3 * a * b * c ^ 2 * t ^ 8 - 2 * a * b * c ^ 2 * t ^ 6 -
    2 * a * b * d ^ 2 * t ^ 10 + 9 * a * b * d ^ 2 * t ^ 8 +
    16 * a * b * d * t ^ 6 - 10 * a * b * d * t ^ 4 +
    2 * a * b * t ^ 2 - 3 * a * b - 4 * a * c ^ 2 * d * t ^ 10 -
    a * c ^ 2 * d * t ^ 8 - 2 * a * c ^ 2 * t ^ 6 +
    9 * a * c ^ 2 * t ^ 4 - 3 * a * d ^ 3 * t ^ 12 +
    6 * a * d ^ 3 * t ^ 10 + 9 * a * d ^ 2 * t ^ 8 -
    4 * a * d ^ 2 * t ^ 6 + 11 * a * d * t ^ 4 -
    10 * a * d * t ^ 2 - a - b ^ 3 * c * t ^ 8 +
    2 * b ^ 2 * c * d * t ^ 10 - 3 * b ^ 2 * c * d * t ^ 8 -
    4 * b ^ 2 * c * t ^ 6 - b ^ 2 * c * t ^ 4 +
    b * c ^ 3 * t ^ 8 + 3 * b * c * d ^ 2 * t ^ 12 -
    2 * b * c * d ^ 2 * t ^ 10 + 10 * b * c * d * t ^ 8 -
    16 * b * c * d * t ^ 6 - 9 * b * c * t ^ 4 +
    2 * b * c * t ^ 2 - c ^ 3 * d * t ^ 12 -
    3 * c ^ 3 * t ^ 8 + 6 * c ^ 3 * t ^ 6 +
    c * d ^ 3 * t ^ 12 + 10 * c * d ^ 2 * t ^ 10 -
    11 * c * d ^ 2 * t ^ 8 + 4 * c * d * t ^ 6 -
    9 * c * d * t ^ 4 - 6 * c * t ^ 2 + 3 * c



def fourBridgeVarianceSkewBernsteinCoeff
    (a b c d : Real) : Fin 7 -> Real
  | 0 => a ^ 3 - 3 * a * b - a + 3 * c
  | 1 =>
      (3 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 8 * a * b -
        5 * a * d - 3 * a + b * c + 6 * c) / 3
  | 2 =>
      -(a ^ 3 * b - 3 * a ^ 3 * d - 15 * a ^ 3 +
        3 * a ^ 2 * b * c - 21 * a ^ 2 * c - a * b ^ 3 +
        7 * a * b ^ 2 + 10 * a * b * d + 35 * a * b -
        9 * a * c ^ 2 + 39 * a * d + 15 * a + b ^ 2 * c -
        b * c + 9 * c * d - 15 * c) / 15
  | 3 =>
      -(2 * a ^ 3 * b - 3 * a ^ 3 * d - 10 * a ^ 3 +
        5 * a ^ 2 * b * c - a ^ 2 * c * d - 22 * a ^ 2 * c -
        2 * a * b ^ 3 - 2 * a * b ^ 2 * d + 4 * a * b ^ 2 +
        a * b * c ^ 2 + 12 * a * b * d + 20 * a * b -
        17 * a * c ^ 2 + 2 * a * d ^ 2 + 28 * a * d + 10 * a +
        4 * b ^ 2 * c + 8 * b * c * d + 8 * b * c -
        3 * c ^ 3 + 16 * c * d) / 10
  | 4 =>
      -(6 * a ^ 3 * b - 15 * a ^ 3 + 12 * a ^ 2 * b * c +
        3 * a ^ 2 * c * d - 46 * a ^ 2 * c - 6 * a * b ^ 3 -
        13 * a * b ^ 2 * d + 2 * a * b ^ 2 + 3 * a * b * c ^ 2 -
        9 * a * b * d ^ 2 + 12 * a * b * d + 25 * a * b +
        a * c ^ 2 * d - 48 * a * c ^ 2 + 3 * a * d ^ 2 +
        34 * a * d + 15 * a + b ^ 3 * c + 3 * b ^ 2 * c * d +
        18 * b ^ 2 * c - b * c ^ 3 + 38 * b * c * d +
        34 * b * c - 15 * c ^ 3 + 11 * c * d ^ 2 +
        42 * c * d + 15 * c) / 15
  | 5 =>
      -(a - b + c - d - 1) * (a + b + c + d + 1) *
        (2 * a * b + 3 * a * d - 3 * a - b * c - 6 * c) / 3
  | 6 =>
      -(a - b + c - d - 1) * (a + b + c + d + 1) *
        (a * b + 3 * a * d - a - b * c + c * d - 3 * c)





theorem fourBridgeVarianceSkewBernsteinCoeff_zero_eq_thirdCumulant
    (a b c d : Real) :
    2 * fourBridgeVarianceSkewBernsteinCoeff a b c d 0 =
      (10 * a + 6 * c) - 3 * (4 + 2 * b) * a + 2 * a ^ 3 := by
  unfold fourBridgeVarianceSkewBernsteinCoeff
  ring



def fourBridgeRankMass (a b c d : Real) : Fin 5 -> Real
  | 0 => (1 - a + b - c + d) / 16
  | 1 => (4 - 2 * a + 2 * c - 4 * d) / 16
  | 2 => (6 - 2 * b + 6 * d) / 16
  | 3 => (4 + 2 * a - 2 * c - 4 * d) / 16
  | 4 => (1 + a + b + c + d) / 16


theorem fourBridgeRankMass_sum (a b c d : Real) :
    fourBridgeRankMass a b c d 0 + fourBridgeRankMass a b c d 1 +
      fourBridgeRankMass a b c d 2 + fourBridgeRankMass a b c d 3 +
      fourBridgeRankMass a b c d 4 = 1 := by
  simp [fourBridgeRankMass]
  ring



theorem fourBridge_endpointSix_eq_rankCross (a b c d : Real) :
    a * b + 3 * a * d - a - b * c + c * d - 3 * c =
      64 * (fourBridgeRankMass a b c d 0 *
          fourBridgeRankMass a b c d 3 -
        fourBridgeRankMass a b c d 1 *
          fourBridgeRankMass a b c d 4) := by
  simp [fourBridgeRankMass]
  ring



theorem fourBridge_endpointFive_eq_rankCross (a b c d : Real) :
    2 * a * b + 3 * a * d - 3 * a - b * c - 6 * c =
      32 * (fourBridgeRankMass a b c d 2 *
          (fourBridgeRankMass a b c d 0 -
            fourBridgeRankMass a b c d 4) +
        3 * (fourBridgeRankMass a b c d 0 *
            fourBridgeRankMass a b c d 3 -
          fourBridgeRankMass a b c d 1 *
            fourBridgeRankMass a b c d 4)) := by
  simp [fourBridgeRankMass]
  ring



theorem fourBridge_endpointFactors_nonpos_of_rank
    {a b c d : Real}
    (h2 : 0 <= fourBridgeRankMass a b c d 2)
    (h04 : fourBridgeRankMass a b c d 0 <=
      fourBridgeRankMass a b c d 4)
    (hcross : fourBridgeRankMass a b c d 0 *
        fourBridgeRankMass a b c d 3 <=
      fourBridgeRankMass a b c d 1 *
        fourBridgeRankMass a b c d 4) :
    2 * a * b + 3 * a * d - 3 * a - b * c - 6 * c <= 0 ∧
      a * b + 3 * a * d - a - b * c + c * d - 3 * c <= 0 := by
  rw [fourBridge_endpointFive_eq_rankCross,
    fourBridge_endpointSix_eq_rankCross]
  constructor
  · have hbias : fourBridgeRankMass a b c d 2 *
        (fourBridgeRankMass a b c d 0 -
          fourBridgeRankMass a b c d 4) <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos h2 (sub_nonpos.mpr h04)
    have hratio : fourBridgeRankMass a b c d 0 *
          fourBridgeRankMass a b c d 3 -
        fourBridgeRankMass a b c d 1 *
          fourBridgeRankMass a b c d 4 <= 0 := sub_nonpos.mpr hcross
    nlinarith
  · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (sub_nonpos.mpr hcross)


theorem fourBridgeVarianceSkewPolynomial_eq_bernstein
    (t a b c d : Real) :
    fourBridgeVarianceSkewPolynomial t a b c d =
      fourBridgeVarianceSkewBernsteinCoeff a b c d 0 * (1 - t ^ 2) ^ 6 +
      6 * fourBridgeVarianceSkewBernsteinCoeff a b c d 1 * t ^ 2 *
        (1 - t ^ 2) ^ 5 +
      15 * fourBridgeVarianceSkewBernsteinCoeff a b c d 2 * (t ^ 2) ^ 2 *
        (1 - t ^ 2) ^ 4 +
      20 * fourBridgeVarianceSkewBernsteinCoeff a b c d 3 * (t ^ 2) ^ 3 *
        (1 - t ^ 2) ^ 3 +
      15 * fourBridgeVarianceSkewBernsteinCoeff a b c d 4 * (t ^ 2) ^ 4 *
        (1 - t ^ 2) ^ 2 +
      6 * fourBridgeVarianceSkewBernsteinCoeff a b c d 5 * (t ^ 2) ^ 5 *
        (1 - t ^ 2) +
      fourBridgeVarianceSkewBernsteinCoeff a b c d 6 * (t ^ 2) ^ 6 := by
  unfold fourBridgeVarianceSkewPolynomial
    fourBridgeVarianceSkewBernsteinCoeff
  ring



theorem fourBridgeVarianceSkewPolynomial_nonpos_of_bernstein
    {t a b c d : Real} (ht0 : 0 <= t) (ht1 : t <= 1)
    (hcoeff : forall i,
      fourBridgeVarianceSkewBernsteinCoeff a b c d i <= 0) :
    fourBridgeVarianceSkewPolynomial t a b c d <= 0 := by
  rw [fourBridgeVarianceSkewPolynomial_eq_bernstein]
  have hs0 : 0 <= t ^ 2 := sq_nonneg t
  have hs1 : t ^ 2 <= 1 := by nlinarith
  have hq0 : 0 <= 1 - t ^ 2 := sub_nonneg.mpr hs1
  have h0 := hcoeff (0 : Fin 7)
  have h1 := hcoeff (1 : Fin 7)
  have h2 := hcoeff (2 : Fin 7)
  have h3 := hcoeff (3 : Fin 7)
  have h4 := hcoeff (4 : Fin 7)
  have h5 := hcoeff (5 : Fin 7)
  have h6 := hcoeff (6 : Fin 7)
  have hterm0 : fourBridgeVarianceSkewBernsteinCoeff a b c d 0 *
      (1 - t ^ 2) ^ 6 <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg h0 (pow_nonneg hq0 6)
  have hterm1 : 6 * fourBridgeVarianceSkewBernsteinCoeff a b c d 1 *
      t ^ 2 * (1 - t ^ 2) ^ 5 <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h1) hs0)
      (pow_nonneg hq0 5)
  have hterm2 : 15 * fourBridgeVarianceSkewBernsteinCoeff a b c d 2 *
      (t ^ 2) ^ 2 * (1 - t ^ 2) ^ 4 <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h2)
        (pow_nonneg hs0 2)) (pow_nonneg hq0 4)
  have hterm3 : 20 * fourBridgeVarianceSkewBernsteinCoeff a b c d 3 *
      (t ^ 2) ^ 3 * (1 - t ^ 2) ^ 3 <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h3)
        (pow_nonneg hs0 3)) (pow_nonneg hq0 3)
  have hterm4 : 15 * fourBridgeVarianceSkewBernsteinCoeff a b c d 4 *
      (t ^ 2) ^ 4 * (1 - t ^ 2) ^ 2 <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h4)
        (pow_nonneg hs0 4)) (pow_nonneg hq0 2)
  have hterm5 : 6 * fourBridgeVarianceSkewBernsteinCoeff a b c d 5 *
      (t ^ 2) ^ 5 * (1 - t ^ 2) <= 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h5)
        (pow_nonneg hs0 5)) hq0
  have hterm6 : fourBridgeVarianceSkewBernsteinCoeff a b c d 6 *
      (t ^ 2) ^ 6 <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg h6 (pow_nonneg hs0 6)
  linarith



theorem fourBridgeTiltVariance_le_neg_iff
    {t a b c d : Real} (ht0 : 0 < t) (ht1 : t < 1)
    (hPp : 1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4 ≠ 0)
    (hPm : 1 - a * t + b * t ^ 2 - c * t ^ 3 + d * t ^ 4 ≠ 0) :
    fourBridgeTiltVariance t a b c d <=
        fourBridgeTiltVariance (-t) a b c d <->
      fourBridgeVarianceSkewPolynomial t a b c d <= 0 := by
  let Pp := 1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4
  let Pm := 1 - a * t + b * t ^ 2 - c * t ^ 3 + d * t ^ 4
  let F := fourBridgeVarianceSkewPolynomial t a b c d
  let C := 4 * t * (t - 1) * (t + 1)
  have hPp0 : Pp ≠ 0 := by simpa [Pp] using hPp
  have hPm0 : Pm ≠ 0 := by simpa [Pm] using hPm
  have hden : 0 < Pm ^ 2 * Pp ^ 2 :=
    mul_pos (sq_pos_of_ne_zero hPm0) (sq_pos_of_ne_zero hPp0)
  have hC : C < 0 := by
    dsimp [C]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (mul_pos (by norm_num) ht0) (sub_neg.mpr ht1))
      (by linarith)
  have hdiff :
      fourBridgeTiltVariance (-t) a b c d -
          fourBridgeTiltVariance t a b c d =
        C * F / (Pm ^ 2 * Pp ^ 2) := by
    unfold fourBridgeTiltVariance
    simp only [neg_sq, neg_mul, mul_neg]
    rw [show 1 + -(a * t) + b * t ^ 2 + c * (-t) ^ 3 +
        d * (-t) ^ 4 = Pm by dsimp [Pm]; ring]
    rw [show 1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4 = Pp by rfl]
    field_simp [hPp0, hPm0]
    dsimp [C, F, fourBridgeVarianceSkewPolynomial]
    ring
  constructor
  · intro hvar
    have hnonneg : 0 <= C * F / (Pm ^ 2 * Pp ^ 2) := by
      rw [<- hdiff]
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

end

end StatMech.Ising
