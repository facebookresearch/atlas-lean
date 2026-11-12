/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSymmetricDominance
import Code.FrontierD.SixVertexBetheFiniteDensityLipschitz









open Finset Matrix

namespace StatMech.FrontierD

noncomputable section



def sixVertexBetheSymmetricJacobianCorrection
    (c : Real) (m : Nat) (q : Fin m → Real) (j : Fin m) : Real :=
  let p := sixVertexEvenSymmetricLift m q
  let i := Fin.natAdd m j
  let ir := Fin.castAdd m j.rev
  4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
      sixVertexThetaDerivativeDenominator c (p i) (p i) +
    (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
      sixVertexThetaDerivativeDenominator c (p i) (p ir))



theorem sixVertexBethePositiveHalfJacobianMatrix_diag_eq_finiteRootDensity
    {N m : Nat} {c : Real} (hN : 0 < N)
    (q : Fin m → Real) (j : Fin m) :
    sixVertexBethePositiveHalfJacobianMatrix N m c q j j =
      2 * Real.pi * N *
          sixVertexFiniteRootDensity c N (m + m)
            (sixVertexEvenSymmetricLift m q) (q j) -
        sixVertexBetheSymmetricJacobianCorrection c m q j := by
  let p := sixVertexEvenSymmetricLift m q
  let i := Fin.natAdd m j
  let ir := Fin.castAdd m j.rev
  let K : Fin (m + m) → Real := fun l =>
    4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p l) /
      sixVertexThetaDerivativeDenominator c (p i) (p l)
  have hi : p i = q j := sixVertexEvenSymmetricLift_natAdd m q j
  have hiMem : i ∈ (Finset.univ : Finset (Fin (m + m))) := Finset.mem_univ i
  have hsum : (∑ l ∈ (Finset.univ : Finset (Fin (m + m))).erase i, K l) =
      (∑ l, K l) - K i := by
    rw [← Finset.sum_erase_add _ _ hiMem]
    ring
  rw [sixVertexBethePositiveHalfJacobianMatrix_diag]
  change (N : Real) + ∑ l ∈ Finset.univ.erase i, K l -
      (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
        sixVertexThetaDerivativeDenominator c (p i) (p ir)) = _
  rw [hsum]
  unfold sixVertexBetheSymmetricJacobianCorrection
  dsimp only
  rw [← hi]
  unfold sixVertexFiniteRootDensity
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring



theorem norm_sixVertexBetheSymmetricJacobianCorrection_le
    {c : Real} (hc : 2 < c) {m : Nat} (q : Fin m → Real) (j : Fin m) :
    ‖sixVertexBetheSymmetricJacobianCorrection c m q j‖ ≤
      2 * (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) := by
  let p := sixVertexEvenSymmetricLift m q
  let i := Fin.natAdd m j
  let ir := Fin.castAdd m j.rev
  unfold sixVertexBetheSymmetricJacobianCorrection
  dsimp only
  calc
    ‖4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
          sixVertexThetaDerivativeDenominator c (p i) (p i) +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
          sixVertexThetaDerivativeDenominator c (p i) (p ir))‖ ≤
        ‖4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
          sixVertexThetaDerivativeDenominator c (p i) (p i)‖ +
        ‖-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
          sixVertexThetaDerivativeDenominator c (p i) (p ir)‖ := norm_add_le _ _
    _ ≤ sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1) +
        sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1) :=
      add_le_add
        (norm_sixVertexTheta_leftDerivative_le hc (p i) (p i))
        (norm_sixVertexTheta_rightDerivative_le hc (p i) (p ir))
    _ = 2 * (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) := by ring



theorem abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le
    {N m : Nat} {c : Real} (hc : 2 < c) (hN : 0 < N)
    {q : Fin m → Real} {j : Fin m} {E mesh : Real}
    (hgap : 0 ≤ sixVertexPositiveHalfRootGap q j)
    (hmesh : sixVertexPositiveHalfRootGap q j ≤ mesh)
    (hcell :
      |sixVertexPositiveHalfRootGap q j *
          sixVertexFiniteRootDensity c N (m + m)
            (sixVertexEvenSymmetricLift m q) (q j) - 1 / N| ≤ E) :
    |sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j -
        2 * Real.pi| ≤
      2 * Real.pi * N * E +
        2 * (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) * mesh := by
  let gap := sixVertexPositiveHalfRootGap q j
  let rho := sixVertexFiniteRootDensity c N (m + m)
    (sixVertexEvenSymmetricLift m q) (q j)
  let corr := sixVertexBetheSymmetricJacobianCorrection c m q j
  have hdiag := sixVertexBethePositiveHalfJacobianMatrix_diag_eq_finiteRootDensity
    (c := c) hN q j
  have hcorr := norm_sixVertexBetheSymmetricJacobianCorrection_le hc q j
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [sixVertexBethePositiveHalfScaledJacobianMatrix] at ⊢
  change sixVertexBethePositiveHalfJacobianMatrix N m c q j j =
      2 * Real.pi * N * rho - corr at hdiag
  rw [hdiag]
  change |(2 * Real.pi * N * rho - corr) * gap - 2 * Real.pi| ≤ _
  have hmain :
      |2 * Real.pi * N * (gap * rho - 1 / N)| ≤
        2 * Real.pi * N * E := by
    rw [abs_mul, abs_of_pos (mul_pos hpi hNreal)]
    exact mul_le_mul_of_nonneg_left hcell (mul_pos hpi hNreal).le
  have hcorrGap : |corr * gap| ≤
      2 * (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) * mesh := by
    rw [abs_mul, ← Real.norm_eq_abs]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    have hR : 0 ≤ 2 * (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) :=
      mul_nonneg (by norm_num)
        (div_nonneg (by linarith) (sub_nonneg.mpr hd.le))
    calc
      ‖corr‖ * |gap| ≤
          (2 * (sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1))) * |gap| :=
        mul_le_mul_of_nonneg_right hcorr (abs_nonneg gap)
      _ = (2 * (sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1))) * gap := by
        rw [abs_of_nonneg hgap]
      _ ≤ (2 * (sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1))) * mesh :=
        mul_le_mul_of_nonneg_left hmesh hR
  calc
    |(2 * Real.pi * N * rho - corr) * gap - 2 * Real.pi| =
        |2 * Real.pi * N * (gap * rho - 1 / N) - corr * gap| := by
      field_simp
      ring
    _ ≤ |2 * Real.pi * N * (gap * rho - 1 / N)| + |corr * gap| :=
      abs_sub _ _
    _ ≤ 2 * Real.pi * N * E +
        2 * (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) * mesh :=
      add_le_add hmain hcorrGap

end

end StatMech.FrontierD
