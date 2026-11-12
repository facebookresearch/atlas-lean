/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheTailDensity








namespace StatMech.FrontierD

noncomputable section

def sixVertexRootDensityKernelLipschitzBound (c : Real) : Real :=
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  let Q := 4 * (d - 1) ^ 2
  let L := 4 * (d + 1) + 2
  (4 * d * (d + 1) / s) *
    (1 / Q + (d + 1) * L / Q ^ 2)

theorem sixVertexRootDensityKernelLipschitzBound_pos
    {c : Real} (hc : 2 < c) :
    0 < sixVertexRootDensityKernelLipschitzBound c := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  let Q := 4 * (d - 1) ^ 2
  let L := 4 * (d + 1) + 2
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  dsimp [sixVertexRootDensityKernelLipschitzBound]
  positivity

theorem sixVertexRootDensityKernel_lipschitz_left
    {c : Real} (hc : 2 < c) (x z y : Real) :
    |sixVertexRootDensityKernel c x y -
        sixVertexRootDensityKernel c z y| <=
      sixVertexRootDensityKernelLipschitzBound c * |x - z| := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  let Fx := sixVertexBetheIntegratingFactor c x
  let Fz := sixVertexBetheIntegratingFactor c z
  let Fy := sixVertexBetheIntegratingFactor c y
  let Dx := sixVertexThetaDerivativeDenominator c x y
  let Dz := sixVertexThetaDerivativeDenominator c z y
  let Q := 4 * (d - 1) ^ 2
  let L := 4 * (d + 1) + 2
  let A := 4 * d * Fy / s
  let Amax := 4 * d * (d + 1) / s
  let B := 1 / Q + (d + 1) * L / Q ^ 2
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hFx : 0 < Fx := sixVertexBetheIntegratingFactor_pos hc x
  have hFz : 0 < Fz := sixVertexBetheIntegratingFactor_pos hc z
  have hFy : 0 < Fy := sixVertexBetheIntegratingFactor_pos hc y
  have hFzUpper : Fz <= d + 1 :=
    (sixVertexBetheIntegratingFactor_bounds hc z).2
  have hFyUpper : Fy <= d + 1 :=
    (sixVertexBetheIntegratingFactor_bounds hc y).2
  have hDx : 0 < Dx := sixVertexThetaDerivativeDenominator_pos hc x y
  have hDz : 0 < Dz := sixVertexThetaDerivativeDenominator_pos hc z y
  have hDxLower : Q <= Dx :=
    sixVertexThetaDerivativeDenominator_uniform_lower hc x y
  have hDzLower : Q <= Dz :=
    sixVertexThetaDerivativeDenominator_uniform_lower hc z y
  have hDprod : Q ^ 2 <= Dx * Dz := by
    simpa [pow_two] using
      (mul_le_mul hDxLower hDzLower hQ.le hDx.le)
  have hFdiff : |Fx - Fz| <= |x - z| := by
    simpa [Fx, Fz, sixVertexBetheIntegratingFactor] using
      Real.abs_cos_sub_cos_le x z
  have hDdiff : |Dx - Dz| <= L * |x - z| :=
    sixVertexThetaDerivativeDenominator_lipschitz_left hc x z y
  have hfirst : |Fx - Fz| / Dx <= |x - z| / Q := by
    calc
      |Fx - Fz| / Dx <= |x - z| / Dx :=
        div_le_div_of_nonneg_right hFdiff hDx.le
      _ <= |x - z| / Q :=
        div_le_div_of_nonneg_left (abs_nonneg _) hQ hDxLower
  have hsecond : Fz * |Dz - Dx| / (Dx * Dz) <=
      (d + 1) * L * |x - z| / Q ^ 2 := by
    have hnum : Fz * |Dz - Dx| <= (d + 1) * L * |x - z| := by
      have hDdiff' : |Dz - Dx| <= L * |x - z| := by
        simpa [abs_sub_comm] using hDdiff
      have hmul := mul_le_mul hFzUpper hDdiff' (abs_nonneg _)
        (by positivity : 0 <= d + 1)
      calc
        Fz * |Dz - Dx| <= (d + 1) * (L * |x - z|) := hmul
        _ = (d + 1) * L * |x - z| := by ring
    calc
      Fz * |Dz - Dx| / (Dx * Dz) <=
          ((d + 1) * L * |x - z|) / (Dx * Dz) :=
        div_le_div_of_nonneg_right hnum (mul_pos hDx hDz).le
      _ <= ((d + 1) * L * |x - z|) / Q ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hDprod
  have hfrac : |Fx / Dx - Fz / Dz| <= B * |x - z| := by
    have hformula : Fx / Dx - Fz / Dz =
        (Fx - Fz) / Dx + Fz * (Dz - Dx) / (Dx * Dz) := by
      field_simp [hDx.ne', hDz.ne']
      ring
    rw [hformula]
    calc
      |(Fx - Fz) / Dx + Fz * (Dz - Dx) / (Dx * Dz)| <=
          |(Fx - Fz) / Dx| +
            |Fz * (Dz - Dx) / (Dx * Dz)| := abs_add_le _ _
      _ = |Fx - Fz| / Dx + Fz * |Dz - Dx| / (Dx * Dz) := by
        rw [abs_div, abs_of_pos hDx, abs_div, abs_mul,
          abs_of_pos hFz, abs_of_pos (mul_pos hDx hDz)]
      _ <= |x - z| / Q +
          (d + 1) * L * |x - z| / Q ^ 2 := add_le_add hfirst hsecond
      _ = B * |x - z| := by dsimp [B]; ring
  have hA : 0 < A := by dsimp [A]; positivity
  have hAmax : 0 <= Amax := by dsimp [Amax]; positivity
  have hAle : A <= Amax := by
    dsimp [A, Amax]
    apply div_le_div_of_nonneg_right _ hs.le
    exact mul_le_mul_of_nonneg_left hFyUpper (by positivity)
  have hB : 0 <= B := by dsimp [B]; positivity
  have hkernel :
      sixVertexRootDensityKernel c x y -
          sixVertexRootDensityKernel c z y =
        A * (Fx / Dx - Fz / Dz) := by
    unfold sixVertexRootDensityKernel
    dsimp [A, d, s, Fx, Fz, Fy, Dx, Dz]
    ring
  rw [hkernel, abs_mul, abs_of_pos hA]
  calc
    A * |Fx / Dx - Fz / Dz| <= A * (B * |x - z|) :=
      mul_le_mul_of_nonneg_left hfrac hA.le
    _ <= Amax * (B * |x - z|) := by
      exact mul_le_mul_of_nonneg_right hAle
        (mul_nonneg hB (abs_nonneg _))
    _ = sixVertexRootDensityKernelLipschitzBound c * |x - z| := by
      dsimp [sixVertexRootDensityKernelLipschitzBound, Amax, B, Q, L, d, s]
      ring

theorem sixVertexRootDensityKernel_swap (c x y : Real) :
    sixVertexRootDensityKernel c x y = sixVertexRootDensityKernel c y x := by
  unfold sixVertexRootDensityKernel
  rw [sixVertexThetaDerivativeDenominator_swap]
  ring

theorem sixVertexRootDensityKernel_lipschitz_right
    {c : Real} (hc : 2 < c) (x y z : Real) :
    |sixVertexRootDensityKernel c x y -
        sixVertexRootDensityKernel c x z| <=
      sixVertexRootDensityKernelLipschitzBound c * |y - z| := by
  rw [sixVertexRootDensityKernel_swap c x y,
    sixVertexRootDensityKernel_swap c x z]
  exact sixVertexRootDensityKernel_lipschitz_left hc y z x

end

end StatMech.FrontierD
