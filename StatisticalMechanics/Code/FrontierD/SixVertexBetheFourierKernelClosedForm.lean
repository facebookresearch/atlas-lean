/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFourierConvolution





namespace StatMech.FrontierD

noncomputable section



theorem tsum_exp_cos_succ_eq_poisson
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    (∑' n : Nat, Real.exp (-lam) ^ (n + 1) *
      Real.cos ((n + 1 : Real) * alpha)) =
      let r := Real.exp (-lam)
      (r * Real.cos alpha - r ^ 2) /
        (1 - 2 * r * Real.cos alpha + r ^ 2) := by
  let r : Real := Real.exp (-lam)
  let z : Complex :=
    (r : Complex) * Complex.exp ((alpha : Complex) * Complex.I)
  change (∑' n : Nat, r ^ (n + 1) *
      Real.cos ((n + 1 : Real) * alpha)) =
    (r * Real.cos alpha - r ^ 2) /
      (1 - 2 * r * Real.cos alpha + r ^ 2)
  have hr0 : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hzNorm : ‖z‖ < 1 := by
    dsimp [z]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hr1
  have hzsum : HasSum (fun n : Nat => z ^ (n + 1))
      (z * (1 - z)⁻¹) := by
    simpa [pow_succ'] using
      (hasSum_geometric_of_norm_lt_one hzNorm).mul_left z
  have hre := Complex.hasSum_re hzsum
  have hterm (n : Nat) : (z ^ (n + 1)).re =
      r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) := by
    dsimp [z]
    rw [mul_pow, <- Complex.exp_nat_mul]
    rw [show ((n + 1 : Nat) : Complex) *
        ((alpha : Complex) * Complex.I) =
      (((n + 1 : Real) * alpha : Real) : Complex) * Complex.I by
        push_cast
        ring]
    rw [show (r : Complex) ^ (n + 1) =
      ((r ^ (n + 1) : Real) : Complex) by norm_cast]
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, sub_zero]
  have hsum : (∑' n : Nat, r ^ (n + 1) *
      Real.cos ((n + 1 : Real) * alpha)) = (z * (1 - z)⁻¹).re := by
    rw [<- hre.tsum_eq]
    apply tsum_congr
    intro n
    exact (hterm n).symm
  rw [hsum]
  have honeSub : 1 - z ≠ 0 := by
    intro h
    have hzOne : z = 1 := (sub_eq_zero.mp h).symm
    rw [hzOne] at hzNorm
    norm_num at hzNorm
  have hden : Complex.normSq (1 - z) =
      1 - 2 * r * Real.cos alpha + r ^ 2 := by
    rw [Complex.normSq_apply]
    dsimp [z]
    simp only [Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, zero_mul, sub_zero, add_zero]
    nlinarith [Real.sin_sq_add_cos_sq alpha]
  have hdenPos : 0 < 1 - 2 * r * Real.cos alpha + r ^ 2 := by
    rw [<- hden]
    exact Complex.normSq_pos.mpr honeSub
  rw [show z * (1 - z)⁻¹ = z / (1 - z) by rfl, Complex.div_re]
  dsimp [z]
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    zero_mul, sub_zero, add_zero]
  rw [hden]
  have hden' : 1 - r * Real.cos alpha * 2 + r ^ 2 ≠ 0 := by
    nlinarith [hdenPos]
  field_simp [hden']
  nlinarith [Real.sin_sq_add_cos_sq alpha]


theorem sixVertexXiFourier_eq
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexXiFourier lam alpha =
      Real.sinh lam / (Real.cosh lam - Real.cos alpha) := by
  let r : Real := Real.exp (-lam)
  have hr0 : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hseries :
      (∑' n : Nat, r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha)) =
        (r * Real.cos alpha - r ^ 2) /
          (1 - 2 * r * Real.cos alpha + r ^ 2) := by
    simpa only [r] using tsum_exp_cos_succ_eq_poisson hlam alpha
  have hDpos : 0 < 1 - 2 * r * Real.cos alpha + r ^ 2 := by
    have hcos := Real.cos_le_one alpha
    nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)]
  have hXiSeries :
      (∑' n : Nat, sixVertexXiFourierTerm lam n alpha) =
        2 * ∑' n : Nat,
          r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) := by
    rw [<- tsum_mul_left]
    apply tsum_congr
    intro n
    unfold sixVertexXiFourierTerm
    dsimp [r]
    rw [show -((n + 1 : Real) * lam) =
      (n + 1 : Real) * (-lam) by ring]
    rw [<- Real.exp_nat_mul]
    push_cast
    ring
  rw [sixVertexXiFourier, hXiSeries, hseries]
  have hPoisson :
      1 + 2 * ((r * Real.cos alpha - r ^ 2) /
        (1 - 2 * r * Real.cos alpha + r ^ 2)) =
      (1 - r ^ 2) / (1 - 2 * r * Real.cos alpha + r ^ 2) := by
    field_simp [hDpos.ne']
    ring
  rw [hPoisson]
  have hcoshDen : 0 < Real.cosh lam - Real.cos alpha := by
    have hcosh : 1 < Real.cosh lam := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  have hExpNeg : Real.exp (-lam) = (Real.exp lam)⁻¹ := by
    rw [<- Real.exp_neg]
  dsimp [r]
  rw [Real.sinh_eq, Real.cosh_eq, hExpNeg]
  field_simp [Real.exp_ne_zero, hDpos.ne', hcoshDen.ne']
  ring

end

end StatMech.FrontierD
