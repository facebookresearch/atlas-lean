/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSymmetricTailJacobian
import Code.FrontierD.SixVertexBetheKernelQuadrature





namespace StatMech.FrontierD

noncomputable section

def sixVertexSymmetricScatteringPhase
    (c x y : Real) : Real :=
  sixVertexTheta c x y - sixVertexTheta c (-x) y

def sixVertexSymmetricScatteringDerivative
    (c x y : Real) : Real :=
  (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
      sixVertexThetaDerivativeDenominator c x y) -
    (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (-x) /
      sixVertexThetaDerivativeDenominator c (-x) y)

def sixVertexSymmetricScatteringLipschitzConstant (c : Real) : NNReal :=
  2 * Real.toNNReal (sixVertexThetaLeftKernelLipschitzBound c)

theorem hasDerivAt_sixVertexSymmetricScatteringPhase_right
    {c : Real} (hc : 2 < c) (x y : Real) :
    HasDerivAt (sixVertexSymmetricScatteringPhase c x)
      (sixVertexSymmetricScatteringDerivative c x y) y := by
  unfold sixVertexSymmetricScatteringPhase
    sixVertexSymmetricScatteringDerivative
  exact (hasDerivAt_sixVertexTheta_right hc x y).sub
    (hasDerivAt_sixVertexTheta_right hc (-x) y)

theorem continuous_sixVertexSymmetricScatteringDerivative
    {c : Real} (hc : 2 < c) (x : Real) :
    Continuous (sixVertexSymmetricScatteringDerivative c x) := by
  unfold sixVertexSymmetricScatteringDerivative
  apply Continuous.sub
  · apply Continuous.div continuous_const
    · unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
      fun_prop
    · intro y
      exact (sixVertexThetaDerivativeDenominator_pos hc x y).ne'
  · apply Continuous.div continuous_const
    · unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
      fun_prop
    · intro y
      exact (sixVertexThetaDerivativeDenominator_pos hc (-x) y).ne'

private theorem abs_sixVertexThetaRightDerivative_sub_le
    {c : Real} (hc : 2 < c) (x y z : Real) :
    |(-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x y) -
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x z)| ≤
      sixVertexThetaLeftKernelLipschitzBound c * |y - z| := by
  have h := sixVertexRootDensityKernel_div_weight_lipschitz hc x y z
  rw [sixVertexRootDensityKernel_div_weight hc,
    sixVertexRootDensityKernel_div_weight hc] at h
  exact h

theorem lipschitzWith_sixVertexSymmetricScatteringDerivative
    {c : Real} (hc : 2 < c) (x : Real) :
    LipschitzWith (sixVertexSymmetricScatteringLipschitzConstant c)
      (sixVertexSymmetricScatteringDerivative c x) := by
  let L := sixVertexThetaLeftKernelLipschitzBound c
  have hL : 0 ≤ L := (sixVertexThetaLeftKernelLipschitzBound_pos hc).le
  have hcoe : (sixVertexSymmetricScatteringLipschitzConstant c : Real) =
      2 * L := by
    change (2 : Real) * (Real.toNNReal L : Real) = 2 * L
    rw [Real.coe_toNNReal] <;> exact hL
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq, Real.dist_eq, hcoe]
  unfold sixVertexSymmetricScatteringDerivative
  let A : Real → Real := fun u =>
    -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
      sixVertexThetaDerivativeDenominator c x u
  let B : Real → Real := fun u =>
    -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (-x) /
      sixVertexThetaDerivativeDenominator c (-x) u
  have hA : |A y - A z| ≤ L * |y - z| :=
    abs_sixVertexThetaRightDerivative_sub_le hc x y z
  have hB : |B y - B z| ≤ L * |y - z| :=
    abs_sixVertexThetaRightDerivative_sub_le hc (-x) y z
  change |(A y - B y) - (A z - B z)| ≤ 2 * L * |y - z|
  calc
    |(A y - B y) - (A z - B z)| =
        |(A y - A z) - (B y - B z)| := by ring_nf
    _ ≤ |A y - A z| + |B y - B z| := abs_sub _ _
    _ ≤ L * |y - z| + L * |y - z| := add_le_add hA hB
    _ = 2 * L * |y - z| := by ring

theorem abs_sixVertexSymmetricScatteringDerivative_le
    {c : Real} (hc : 2 < c) (x y : Real) :
    |sixVertexSymmetricScatteringDerivative c x y| ≤
      2 * (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) := by
  unfold sixVertexSymmetricScatteringDerivative
  rw [← Real.norm_eq_abs]
  apply (norm_sub_le _ _).trans
  simpa [two_mul] using
    add_le_add
      (norm_sixVertexTheta_rightDerivative_le hc x y)
      (norm_sixVertexTheta_rightDerivative_le hc (-x) y)

theorem intervalIntegral_sixVertexSymmetricScatteringDerivative
    {c : Real} (hc : 2 < c) (x a b : Real) :
    ∫ y in a..b, sixVertexSymmetricScatteringDerivative c x y =
      sixVertexSymmetricScatteringPhase c x b -
        sixVertexSymmetricScatteringPhase c x a := by
  let f := sixVertexSymmetricScatteringPhase c x
  let f' := sixVertexSymmetricScatteringDerivative c x
  have hderiv : deriv f = f' := by
    funext y
    exact (hasDerivAt_sixVertexSymmetricScatteringPhase_right hc x y).deriv
  have hdiff : ∀ y ∈ Set.uIcc a b, DifferentiableAt Real f y := by
    intro y _
    exact (hasDerivAt_sixVertexSymmetricScatteringPhase_right hc x y).differentiableAt
  exact intervalIntegral.integral_deriv_eq_sub' f hderiv hdiff
    (continuous_sixVertexSymmetricScatteringDerivative hc x).continuousOn

def sixVertexSymmetricScatteringBoundaryIncrement
    (c x : Real) : Real :=
  sixVertexSymmetricScatteringPhase c x 0 -
    sixVertexSymmetricScatteringPhase c x (-Real.pi)

theorem sixVertexSymmetricScatteringBoundaryIncrement_eq
    {c : Real} (hc : 2 < c) {x : Real}
    (hx : x ∈ Set.Icc (-Real.pi) 0) :
    sixVertexSymmetricScatteringBoundaryIncrement c x =
      4 * Real.arctan
        ((-Real.sin x) /
          (2 * sixVertexAnisotropyMagnitude c *
            (Real.cos x + sixVertexAnisotropyMagnitude c))) := by
  let d := sixVertexAnisotropyMagnitude c
  let D0 := Real.cos x + 1 + 2 * d
  let Dp := Real.cos x - 1 + 2 * d
  let a := Real.sin x / D0
  let b := Real.sin x / Dp
  let r := (-Real.sin x) / (2 * d * (Real.cos x + d))
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hsin : Real.sin x ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 hx.1
  have hD0 : 0 < D0 := by
    dsimp [D0]
    linarith [Real.neg_one_le_cos x]
  have hDp : 0 < Dp := by
    dsimp [Dp]
    linarith [Real.neg_one_le_cos x]
  have ha : a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hsin hD0.le
  have hb : b ≤ 0 := div_nonpos_of_nonpos_of_nonneg hsin hDp.le
  have hphase0 : sixVertexSymmetricScatteringPhase c x 0 =
      -2 * x + 4 * Real.arctan a := by
    unfold sixVertexSymmetricScatteringPhase sixVertexTheta
      sixVertexThetaDenominator
    dsimp [a, D0, d, sixVertexAnisotropyMagnitude]
    simp only [Real.sin_zero, Real.cos_zero, Real.sin_neg, Real.cos_neg,
      sub_zero]
    rw [show (-Real.sin x) /
        (Real.cos x + 1 - 2 * sixVertexDelta c) =
          -(Real.sin x /
            (Real.cos x + 1 - 2 * sixVertexDelta c)) by ring,
      Real.arctan_neg]
    ring
  have hphasePi : sixVertexSymmetricScatteringPhase c x (-Real.pi) =
      -2 * x + 4 * Real.arctan b := by
    unfold sixVertexSymmetricScatteringPhase sixVertexTheta
      sixVertexThetaDenominator
    dsimp [b, Dp, d, sixVertexAnisotropyMagnitude]
    simp only [Real.sin_neg, Real.sin_pi, neg_zero, Real.cos_neg,
      Real.cos_pi, sub_zero]
    rw [show (-Real.sin x) /
        (Real.cos x + -1 - 2 * sixVertexDelta c) =
          -(Real.sin x /
            (Real.cos x + -1 - 2 * sixVertexDelta c)) by ring,
      Real.arctan_neg]
    ring
  have hatan : Real.arctan a - Real.arctan b = Real.arctan r := by
    have hadd := Real.arctan_add (x := a) (y := -b) (by nlinarith [mul_nonneg_of_nonpos_of_nonpos ha hb])
    rw [Real.arctan_neg] at hadd
    have htrig := Real.sin_sq_add_cos_sq x
    have habpos : 0 < 1 - a * -b := by
      have : 0 ≤ a * b := mul_nonneg_of_nonpos_of_nonpos ha hb
      nlinarith
    have hcd : 0 < Real.cos x + d := by
      linarith [Real.neg_one_le_cos x]
    have habDiff : a - b =
        (-2 * Real.sin x) / (D0 * Dp) := by
      dsimp [a, b]
      field_simp [hD0.ne', hDp.ne']
      dsimp [D0, Dp]
      ring
    have habOne : 1 + a * b =
        (D0 * Dp + Real.sin x ^ 2) / (D0 * Dp) := by
      dsimp [a, b]
      field_simp [hD0.ne', hDp.ne']
    have hdenid : D0 * Dp + Real.sin x ^ 2 =
        4 * d * (Real.cos x + d) := by
      dsimp [D0, Dp]
      nlinarith [htrig]
    have hrational : (a + -b) / (1 - a * -b) = r := by
      rw [show a + -b = a - b by ring,
        show 1 - a * -b = 1 + a * b by ring,
        habDiff, habOne, hdenid]
      dsimp [r]
      field_simp [hD0.ne', hDp.ne', hd.ne', hcd.ne']
      ring
    rw [hrational] at hadd
    exact hadd
  unfold sixVertexSymmetricScatteringBoundaryIncrement
  rw [hphase0, hphasePi]
  calc
    -2 * x + 4 * Real.arctan a - (-2 * x + 4 * Real.arctan b) =
        4 * (Real.arctan a - Real.arctan b) := by ring
    _ = 4 * Real.arctan r := by rw [hatan]
    _ = 4 * Real.arctan
        ((-Real.sin x) /
          (2 * sixVertexAnisotropyMagnitude c *
            (Real.cos x + sixVertexAnisotropyMagnitude c))) := by rfl

def sixVertexSymmetricScatteringBoundaryBound (c : Real) : Real :=
  4 * Real.arctan
    (1 / (2 * sixVertexAnisotropyMagnitude c *
      Real.sqrt (sixVertexAnisotropyMagnitude c ^ 2 - 1)))

private theorem sixVertexSymmetricScatteringBoundaryRatio_le
    {c : Real} (hc : 2 < c) {x : Real}
    (hx : x ∈ Set.Icc (-Real.pi) 0) :
    0 ≤ (-Real.sin x) /
        (2 * sixVertexAnisotropyMagnitude c *
          (Real.cos x + sixVertexAnisotropyMagnitude c)) ∧
    (-Real.sin x) /
        (2 * sixVertexAnisotropyMagnitude c *
          (Real.cos x + sixVertexAnisotropyMagnitude c)) ≤
      1 / (2 * sixVertexAnisotropyMagnitude c *
        Real.sqrt (sixVertexAnisotropyMagnitude c ^ 2 - 1)) := by
  let d := sixVertexAnisotropyMagnitude c
  let s := -Real.sin x
  let t := Real.sqrt (d ^ 2 - 1)
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 ≤ s := neg_nonneg.mpr
    (Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 hx.1)
  have hcd : 0 < Real.cos x + d := by
    linarith [Real.neg_one_le_cos x]
  have hrad : 0 < d ^ 2 - 1 := by nlinarith
  have ht : 0 < t := Real.sqrt_pos.2 hrad
  have htSq : t ^ 2 = d ^ 2 - 1 := Real.sq_sqrt hrad.le
  have htrig := Real.sin_sq_add_cos_sq x
  have hsSq : s ^ 2 = 1 - Real.cos x ^ 2 := by
    dsimp [s]
    nlinarith
  have hsq : (s * t) ^ 2 ≤ (Real.cos x + d) ^ 2 := by
    rw [mul_pow, htSq, hsSq]
    nlinarith [sq_nonneg (d * Real.cos x + 1)]
  have hst : s * t ≤ Real.cos x + d :=
    (sq_le_sq₀ (mul_nonneg hs ht.le) hcd.le).1 hsq
  have hratio : s / (Real.cos x + d) ≤ 1 / t := by
    rw [div_le_iff₀ hcd]
    have hdiv := (le_div_iff₀ ht).2 hst
    simpa [one_div, mul_comm] using hdiv
  have htwoD : 0 < 2 * d := by positivity
  constructor
  · dsimp [s, d]
    positivity
  · change s / (2 * d * (Real.cos x + d)) ≤ 1 / (2 * d * t)
    calc
      s / (2 * d * (Real.cos x + d)) =
          (s / (Real.cos x + d)) / (2 * d) := by
        field_simp [hcd.ne', hd.ne']
      _ ≤ (1 / t) / (2 * d) :=
        div_le_div_of_nonneg_right hratio htwoD.le
      _ = 1 / (2 * d * t) := by
        field_simp [ht.ne', hd.ne']

theorem sixVertexSymmetricScatteringBoundaryBound_nonneg
    {c : Real} (hc : 2 < c) :
    0 ≤ sixVertexSymmetricScatteringBoundaryBound c := by
  let d := sixVertexAnisotropyMagnitude c
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hsqrt : 0 < Real.sqrt (d ^ 2 - 1) :=
    Real.sqrt_pos.2 (by nlinarith)
  unfold sixVertexSymmetricScatteringBoundaryBound
  exact mul_nonneg (by norm_num)
    (Real.arctan_nonneg.2 (by positivity))

theorem sixVertexSymmetricScatteringBoundaryBound_lt_two_pi
    {c : Real} :
    sixVertexSymmetricScatteringBoundaryBound c < 2 * Real.pi := by
  let z := 1 / (2 * sixVertexAnisotropyMagnitude c *
    Real.sqrt (sixVertexAnisotropyMagnitude c ^ 2 - 1))
  have hz := Real.arctan_lt_pi_div_two z
  unfold sixVertexSymmetricScatteringBoundaryBound
  change 4 * Real.arctan z < 2 * Real.pi
  linarith

theorem sixVertexSymmetricScatteringBoundaryIncrement_bounds
    {c : Real} (hc : 2 < c) {x : Real}
    (hx : x ∈ Set.Icc (-Real.pi) 0) :
    0 ≤ sixVertexSymmetricScatteringBoundaryIncrement c x ∧
      sixVertexSymmetricScatteringBoundaryIncrement c x ≤
        sixVertexSymmetricScatteringBoundaryBound c := by
  rw [sixVertexSymmetricScatteringBoundaryIncrement_eq hc hx]
  have hr := sixVertexSymmetricScatteringBoundaryRatio_le hc hx
  constructor
  · exact mul_nonneg (by norm_num) (Real.arctan_nonneg.2 hr.1)
  · unfold sixVertexSymmetricScatteringBoundaryBound
    exact mul_le_mul_of_nonneg_left
      (Real.arctan_le_arctan_iff.2 hr.2) (by norm_num)

end

end StatMech.FrontierD
