/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOddSymmetricJacobian
import Code.FrontierD.SixVertexBetheFiniteDensityLipschitz





open Finset Matrix

namespace StatMech.FrontierD

noncomputable section

def sixVertexOddPositiveHalfRootGap
    {m : Nat} (q : Fin m → Real) (k : Fin m) : Real :=
  if hk : k.val = 0 then q k else q k - q ⟨k.val - 1, by omega⟩

theorem sixVertexOddSymmetricLift_positive_mem_Icc
    {m : Nat} {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (j : Fin m) : q j ∈ Set.Icc 0 Real.pi := by
  let i := sixVertexOddPositiveIndex m j
  let z := sixVertexOddCentralIndex m
  have hzi : z < i := by
    rw [Fin.lt_def]
    simp [z, i, sixVertexOddCentralIndex, sixVertexOddPositiveIndex]
    omega
  have hpos : 0 < q j := by
    have hlt := hq.1 hzi
    change sixVertexOddSymmetricLift m q z <
      sixVertexOddSymmetricLift m q i at hlt
    rw [sixVertexOddSymmetricLift_central,
      sixVertexOddSymmetricLift_positive] at hlt
    exact hlt
  have hpi := (hq.2.2 i).2.le
  change sixVertexOddSymmetricLift m q i ≤ Real.pi at hpi
  rw [sixVertexOddSymmetricLift_positive] at hpi
  exact ⟨hpos.le, hpi⟩

theorem sixVertexOddPositiveHalfRootGap_pos_of_open
    {m : Nat} {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (k : Fin m) : 0 < sixVertexOddPositiveHalfRootGap q k := by
  unfold sixVertexOddPositiveHalfRootGap
  split_ifs with hk
  · exact (sixVertexOddSymmetricLift_positive_mem_Icc hq k).1.lt_of_ne
      (fun h => by
        have := hq.1 (show sixVertexOddCentralIndex m <
          sixVertexOddPositiveIndex m k by
            rw [Fin.lt_def]
            simp [sixVertexOddCentralIndex, sixVertexOddPositiveIndex]
            omega)
        rw [sixVertexOddSymmetricLift_central,
          sixVertexOddSymmetricLift_positive, h] at this
        exact (lt_irrefl (q k) this).elim)
  · let kp : Fin m := ⟨k.val - 1, by omega⟩
    have hindex : sixVertexOddPositiveIndex m kp <
        sixVertexOddPositiveIndex m k := by
      rw [Fin.lt_def]
      simp [sixVertexOddPositiveIndex, kp]
      omega
    have hlt := hq.1 hindex
    rw [sixVertexOddSymmetricLift_positive,
      sixVertexOddSymmetricLift_positive] at hlt
    exact sub_pos.mpr hlt

def sixVertexOddPositiveHalfCellLeftIndex
    {m : Nat} (j : Fin m) : Fin ((m + 1) + m) :=
  if hj : j.val = 0 then sixVertexOddCentralIndex m
  else sixVertexOddPositiveIndex m ⟨j.val - 1, by omega⟩

theorem sixVertexOddPositiveHalfCellLeftIndex_val_add_one
    {m : Nat} (j : Fin m) :
    (sixVertexOddPositiveHalfCellLeftIndex j).val + 1 =
      (sixVertexOddPositiveIndex m j).val := by
  unfold sixVertexOddPositiveHalfCellLeftIndex
  split_ifs with hj
  · simp [sixVertexOddCentralIndex, sixVertexOddPositiveIndex, hj]
  · simp [sixVertexOddPositiveIndex]
    omega

theorem sixVertexOddSymmetricLift_positiveHalfCellLeft
    {m : Nat} (q : Fin m → Real) (j : Fin m) :
    sixVertexOddSymmetricLift m q
        (sixVertexOddPositiveHalfCellLeftIndex j) =
      q j - sixVertexOddPositiveHalfRootGap q j := by
  unfold sixVertexOddPositiveHalfCellLeftIndex
    sixVertexOddPositiveHalfRootGap
  split_ifs with hj
  · rw [sixVertexOddSymmetricLift_central]
    ring
  · rw [sixVertexOddSymmetricLift_positive]
    ring

theorem sixVertexCentralQuantumNumber_oddPositiveHalfCell_sub
    {m : Nat} (j : Fin m) :
    sixVertexCentralQuantumNumber (sixVertexOddPositiveIndex m j) -
        sixVertexCentralQuantumNumber
          (sixVertexOddPositiveHalfCellLeftIndex j) = 1 := by
  rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
  have hval := sixVertexOddPositiveHalfCellLeftIndex_val_add_one j
  have hvalReal :
      ((sixVertexOddPositiveHalfCellLeftIndex j).val : Real) + 1 =
        ((sixVertexOddPositiveIndex m j).val : Real) := by exact_mod_cast hval
  linarith

theorem intervalIntegral_sixVertexFiniteRootDensity_oddPositiveHalfCell
    {c : Real} (hc : 2 < c) {N m : Nat} (hN : 0 < N)
    {q : Fin m → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q)) (j : Fin m) :
    ∫ x in q j - sixVertexOddPositiveHalfRootGap q j..q j,
        sixVertexFiniteRootDensity c N ((m + 1) + m)
          (sixVertexOddSymmetricLift m q) x = 1 / N := by
  let p := sixVertexOddSymmetricLift m q
  let il := sixVertexOddPositiveHalfCellLeftIndex j
  let ir := sixVertexOddPositiveIndex m j
  have hl : p il = q j - sixVertexOddPositiveHalfRootGap q j :=
    sixVertexOddSymmetricLift_positiveHalfCellLeft q j
  have hr : p ir = q j := sixVertexOddSymmetricLift_positive m q j
  rw [← hl, ← hr,
    intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub hc hN,
    sixVertexBetheCountingFunction_at_root hN hsol ir,
    sixVertexBetheCountingFunction_at_root hN hsol il, ← sub_div]
  exact congrArg (fun x : Real => x / N)
    (sixVertexCentralQuantumNumber_oddPositiveHalfCell_sub j)

theorem sixVertexOddPositiveHalfRootGap_upper_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N m : Nat} (hN : 0 < N)
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q))
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q) x) (j : Fin m) :
    sixVertexOddPositiveHalfRootGap q j ≤ 1 / ((N : Real) * lower) := by
  let gap := sixVertexOddPositiveHalfRootGap q j
  let rho := sixVertexFiniteRootDensity c N ((m + 1) + m)
    (sixVertexOddSymmetricLift m q)
  have hgap : 0 ≤ gap := (sixVertexOddPositiveHalfRootGap_pos_of_open hopen j).le
  have hmono := intervalIntegral.integral_mono_on
    (show q j - gap ≤ q j by linarith)
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q)).intervalIntegrable _ _)
    (fun x _ => hdensity x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul, sub_sub_cancel] at hmono
  rw [intervalIntegral_sixVertexFiniteRootDensity_oddPositiveHalfCell
    hc hN hsol j] at hmono
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  rw [le_div_iff₀ (mul_pos hNreal hlower)]
  have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
  have hNinv : (N : Real) * (1 / (N : Real)) = 1 := by
    field_simp [hNreal.ne']
  rw [hNinv] at hmul
  nlinarith

def sixVertexBetheOddSymmetricJacobianCorrection
    (c : Real) (m : Nat) (q : Fin m → Real) (j : Fin m) : Real :=
  let p := sixVertexOddSymmetricLift m q
  let i := sixVertexOddPositiveIndex m j
  let ir := sixVertexOddNegativeCoordinateIndex m j
  4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
      sixVertexThetaDerivativeDenominator c (p i) (p i) +
    (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
      sixVertexThetaDerivativeDenominator c (p i) (p ir))

theorem sixVertexBetheOddPositiveHalfJacobianMatrix_diag_eq_finiteRootDensity
    {N m : Nat} {c : Real} (hN : 0 < N)
    (q : Fin m → Real) (j : Fin m) :
    sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j j =
      2 * Real.pi * N * sixVertexFiniteRootDensity c N ((m + 1) + m)
          (sixVertexOddSymmetricLift m q) (q j) -
        sixVertexBetheOddSymmetricJacobianCorrection c m q j := by
  let p := sixVertexOddSymmetricLift m q
  let i := sixVertexOddPositiveIndex m j
  let ir := sixVertexOddNegativeCoordinateIndex m j
  let K : Fin ((m + 1) + m) → Real := fun l =>
    4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p l) /
      sixVertexThetaDerivativeDenominator c (p i) (p l)
  have hi : p i = q j := sixVertexOddSymmetricLift_positive m q j
  have hiMem : i ∈ (Finset.univ : Finset (Fin ((m + 1) + m))) :=
    Finset.mem_univ i
  have hsum : (∑ l ∈ (Finset.univ : Finset (Fin ((m + 1) + m))).erase i,
      K l) = (∑ l, K l) - K i := by
    rw [← Finset.sum_erase_add _ _ hiMem]
    ring
  unfold sixVertexBetheOddPositiveHalfJacobianMatrix
  dsimp only
  have hii : i ≠ ir := by
    intro h
    have hv := congrArg Fin.val h
    simp [i, ir, sixVertexOddPositiveIndex,
      sixVertexOddNegativeCoordinateIndex, sixVertexOddNegativeIndex] at hv
    omega
  rw [sixVertexBetheJacobianMatrix, if_pos rfl,
    sixVertexBetheJacobianMatrix, if_neg hii, hsum]
  unfold sixVertexBetheOddSymmetricJacobianCorrection
  dsimp only
  rw [← hi]
  unfold sixVertexFiniteRootDensity
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem norm_sixVertexBetheOddSymmetricJacobianCorrection_le
    {c : Real} (hc : 2 < c) {m : Nat} (q : Fin m → Real) (j : Fin m) :
    ‖sixVertexBetheOddSymmetricJacobianCorrection c m q j‖ ≤
      2 * (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) := by
  let p := sixVertexOddSymmetricLift m q
  let i := sixVertexOddPositiveIndex m j
  let ir := sixVertexOddNegativeCoordinateIndex m j
  unfold sixVertexBetheOddSymmetricJacobianCorrection
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
    _ = _ := by ring

def sixVertexBetheOddPositiveHalfScaledJacobianMatrix
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    Matrix (Fin m) (Fin m) Real := fun j k =>
  sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j k *
    sixVertexOddPositiveHalfRootGap q k

theorem abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le
    {N m : Nat} {c : Real} (hc : 2 < c) (hN : 0 < N)
    {q : Fin m → Real} {j : Fin m} {E mesh : Real}
    (hgap : 0 ≤ sixVertexOddPositiveHalfRootGap q j)
    (hmesh : sixVertexOddPositiveHalfRootGap q j ≤ mesh)
    (hcell :
      |sixVertexOddPositiveHalfRootGap q j *
          sixVertexFiniteRootDensity c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q) (q j) - 1 / N| ≤ E) :
    |sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j j -
        2 * Real.pi| ≤
      2 * Real.pi * N * E +
        2 * (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) * mesh := by
  let gap := sixVertexOddPositiveHalfRootGap q j
  let rho := sixVertexFiniteRootDensity c N ((m + 1) + m)
    (sixVertexOddSymmetricLift m q) (q j)
  let corr := sixVertexBetheOddSymmetricJacobianCorrection c m q j
  have hdiag :=
    sixVertexBetheOddPositiveHalfJacobianMatrix_diag_eq_finiteRootDensity
      (c := c) hN q j
  have hcorr := norm_sixVertexBetheOddSymmetricJacobianCorrection_le hc q j
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hpi : 0 < 2 * Real.pi := by positivity
  unfold sixVertexBetheOddPositiveHalfScaledJacobianMatrix
  change sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j j =
      2 * Real.pi * N * rho - corr at hdiag
  rw [hdiag]
  change |(2 * Real.pi * N * rho - corr) * gap - 2 * Real.pi| ≤ _
  have hmain : |2 * Real.pi * N * (gap * rho - 1 / N)| ≤
      2 * Real.pi * N * E := by
    rw [abs_mul, abs_of_pos (mul_pos hpi hNreal)]
    exact mul_le_mul_of_nonneg_left hcell (mul_pos hpi hNreal).le
  have hcorrGap : |corr * gap| ≤
      2 * (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) * mesh := by
    rw [abs_mul, ← Real.norm_eq_abs]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    have hR : 0 ≤ 2 * (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) := by positivity
    calc
      ‖corr‖ * |gap| ≤
          (2 * (sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1))) * |gap| :=
        mul_le_mul_of_nonneg_right hcorr (abs_nonneg gap)
      _ = (2 * (sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1))) * gap := by
        rw [abs_of_nonneg hgap]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmesh hR
  calc
    |(2 * Real.pi * N * rho - corr) * gap - 2 * Real.pi| =
        |2 * Real.pi * N * (gap * rho - 1 / N) - corr * gap| := by
      field_simp
      ring
    _ ≤ |2 * Real.pi * N * (gap * rho - 1 / N)| + |corr * gap| :=
      abs_sub _ _
    _ ≤ _ := add_le_add hmain hcorrGap

end

end StatMech.FrontierD
