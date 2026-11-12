/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOddSymmetricDensityJacobian
import Code.FrontierD.SixVertexBetheSymmetricOffDiagonal
import Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate





open Filter Topology

namespace StatMech.FrontierD

noncomputable section

theorem abs_sixVertexOddPositiveHalfGap_mul_finiteRootDensity_sub_inv_width_le
    {c : Real} (hc : 2 < c) {N m : Nat} (hN : 0 < N)
    (hcount : (m + 1) + m ≤ N) {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q)) (j : Fin m) :
    |sixVertexOddPositiveHalfRootGap q j *
          sixVertexFiniteRootDensity c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q) (q j) - 1 / N| ≤
      2 * (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
        sixVertexOddPositiveHalfRootGap q j ^ 2 := by
  have hgap := sixVertexOddPositiveHalfRootGap_pos_of_open hopen j
  have hquad := abs_gap_mul_right_sub_intervalIntegral_le
    (continuous_sixVertexFiniteRootDensity hc N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q))
    (lipschitzWith_sixVertexFiniteRootDensity hc hN hcount
      (sixVertexOddSymmetricLift m q))
    (show q j - sixVertexOddPositiveHalfRootGap q j ≤ q j by linarith)
  rw [intervalIntegral_sixVertexFiniteRootDensity_oddPositiveHalfCell
    hc hN hsol j] at hquad
  simpa only [sub_sub_cancel] using hquad

theorem abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower
    {c : Real} (hc : 2 < c) {N m : Nat} (hN : 0 < N)
    (hcount : (m + 1) + m ≤ N) {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q))
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q) x) (j : Fin m) :
    |sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j j -
        2 * Real.pi| ≤
      sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower := by
  let gap := sixVertexOddPositiveHalfRootGap q j
  let mesh := 1 / ((N : Real) * lower)
  let L := (sixVertexFiniteRootDensityLipschitzConstant c : Real)
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  have hgap : 0 ≤ gap := (sixVertexOddPositiveHalfRootGap_pos_of_open hopen j).le
  have hmesh : gap ≤ mesh :=
    sixVertexOddPositiveHalfRootGap_upper_of_finiteDensityLower
      hc hN hopen hsol hlower hdensity j
  have hcell : |gap * sixVertexFiniteRootDensity c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q) (q j) - 1 / N| ≤
      2 * L * gap ^ 2 :=
    abs_sixVertexOddPositiveHalfGap_mul_finiteRootDensity_sub_inv_width_le
      hc hN hcount hopen hsol j
  have hbase :=
    abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le
      hc hN hgap hmesh hcell
  have hL : 0 ≤ L := NNReal.coe_nonneg _
  have hmesh0 : 0 ≤ mesh := by positivity
  have hsq : gap ^ 2 ≤ mesh ^ 2 := by nlinarith
  unfold sixVertexSymmetricJacobianDiagonalErrorOfLower
  change _ ≤ 4 * Real.pi * N * L * mesh ^ 2 + 2 * R * mesh
  calc
    _ ≤ 2 * Real.pi * N * (2 * L * gap ^ 2) + 2 * R * mesh := hbase
    _ ≤ 4 * Real.pi * N * L * mesh ^ 2 + 2 * R * mesh := by
      have hcoef : 0 ≤ 4 * Real.pi * (N : Real) * L := by positivity
      calc
        2 * Real.pi * N * (2 * L * gap ^ 2) + 2 * R * mesh =
            (4 * Real.pi * N * L) * gap ^ 2 + 2 * R * mesh := by ring
        _ ≤ (4 * Real.pi * N * L) * mesh ^ 2 + 2 * R * mesh :=
          add_le_add (mul_le_mul_of_nonneg_left hsq hcoef) le_rfl
        _ = _ := by ring

theorem sixVertexBetheOddPositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative
    {N m : Nat} {c : Real} {q : Fin m → Real}
    {j k : Fin m} (hjk : j ≠ k) :
    sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j k =
      sixVertexSymmetricScatteringDerivative c (-q j) (-q k) := by
  let p := sixVertexOddSymmetricLift m q
  let i := sixVertexOddPositiveIndex m j
  let l := sixVertexOddPositiveIndex m k
  let lr := sixVertexOddNegativeCoordinateIndex m k
  have hil : i ≠ l := by
    intro h
    apply hjk
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp [i, l, sixVertexOddPositiveIndex] at hv ⊢
    omega
  have hilr : i ≠ lr := by
    intro h
    have hv := congrArg Fin.val h
    simp [i, lr, sixVertexOddPositiveIndex,
      sixVertexOddNegativeCoordinateIndex, sixVertexOddNegativeIndex] at hv
    omega
  have hi : p i = q j := sixVertexOddSymmetricLift_positive m q j
  have hl : p l = q k := sixVertexOddSymmetricLift_positive m q k
  have hlr : p lr = -q k := by
    simp [p, lr, sixVertexOddNegativeCoordinateIndex,
      sixVertexOddSymmetricLift_negative]
  unfold sixVertexBetheOddPositiveHalfJacobianMatrix
  dsimp only
  rw [sixVertexBetheJacobianMatrix, if_neg hil,
    sixVertexBetheJacobianMatrix, if_neg hilr]
  simp only [sixVertexOddSymmetricLift_positive]
  rw [show sixVertexOddSymmetricLift m q
      (sixVertexOddNegativeCoordinateIndex m k) = -q k by
        exact hlr]
  unfold sixVertexSymmetricScatteringDerivative
  have hfactor : sixVertexBetheIntegratingFactor c (-q j) =
      sixVertexBetheIntegratingFactor c (q j) := by
    simp [sixVertexBetheIntegratingFactor]
  have hden : sixVertexThetaDerivativeDenominator c (-q j) (-q k) =
      sixVertexThetaDerivativeDenominator c (q j) (q k) := by
    unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
    simp only [Real.cos_neg, Real.sin_neg]
    ring
  rw [hfactor, hden]
  simp

def sixVertexOddNegativeHalfRootPartition
    {m : Nat} (q : Fin m → Real) (hm : 0 < m) (k : Nat) : Real :=
  if hk : k < m then -q ⟨m - 1 - k, by omega⟩ else 0

theorem sixVertexOddNegativeHalfRootPartition_cellGap
    {m : Nat} (q : Fin m → Real) (hm : 0 < m)
    (k : Nat) (hk : k < m) :
    sixVertexOddNegativeHalfRootPartition q hm (k + 1) -
        sixVertexOddNegativeHalfRootPartition q hm k =
      sixVertexOddPositiveHalfRootGap q ⟨m - 1 - k, by omega⟩ := by
  unfold sixVertexOddNegativeHalfRootPartition
    sixVertexOddPositiveHalfRootGap
  by_cases hlast : k + 1 = m
  · simp only [hk, hlast, lt_self_iff_false, ↓reduceDIte]
    split_ifs with hz
    · ring
    · omega
  · have hsucc : k + 1 < m := by omega
    simp only [hk, hsucc, ↓reduceDIte]
    split_ifs with hz
    · omega
    · have heq : (⟨m - 1 - (k + 1), by omega⟩ : Fin m) =
          ⟨(m - 1 - k) - 1, by omega⟩ := by
        apply Fin.ext
        simp
        omega
      rw [heq]
      ring

theorem abs_sixVertexOddPositiveHalfScatteringEndpointSum_sub_integral_le
    {c : Real} (hc : 2 < c) {m : Nat} (hm : 0 < m)
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    {mesh : Real} (hmesh : ∀ k, sixVertexOddPositiveHalfRootGap q k ≤ mesh)
    (j : Fin m) :
    |∑ k, sixVertexOddPositiveHalfRootGap q k *
          sixVertexSymmetricScatteringDerivative c (-q j) (-q k) -
        ∫ y in -q ⟨m - 1, by omega⟩..0,
          sixVertexSymmetricScatteringDerivative c (-q j) y| ≤
      (sixVertexSymmetricScatteringLipschitzConstant c : Real) *
        mesh * (2 * Real.pi) := by
  let a := sixVertexOddNegativeHalfRootPartition q hm
  let H := sixVertexSymmetricScatteringDerivative c (-q j)
  let L := sixVertexSymmetricScatteringLipschitzConstant c
  have hordered : ∀ k < m, a k ≤ a (k + 1) := by
    intro k hk
    rw [← sub_nonneg, sixVertexOddNegativeHalfRootPartition_cellGap q hm k hk]
    exact (sixVertexOddPositiveHalfRootGap_pos_of_open hopen _).le
  have hquad := abs_leftEndpointSum_sub_intervalIntegral_le
    (continuous_sixVertexSymmetricScatteringDerivative hc (-q j))
    (lipschitzWith_sixVertexSymmetricScatteringDerivative hc (-q j))
    a m (mesh := mesh) hordered (fun k hk => by
      rw [sixVertexOddNegativeHalfRootPartition_cellGap q hm k hk]
      exact hmesh _)
  have hsum :
      (∑ k ∈ Finset.range m, (a (k + 1) - a k) * H (a k)) =
        ∑ k : Fin m, sixVertexOddPositiveHalfRootGap q k * H (-q k) := by
    rw [← Fin.sum_univ_eq_sum_range]
    rw [← Equiv.sum_comp Fin.revPerm
      (fun k : Fin m => sixVertexOddPositiveHalfRootGap q k * H (-q k))]
    apply Finset.sum_congr rfl
    intro k _
    rw [sixVertexOddNegativeHalfRootPartition_cellGap q hm k.val k.isLt]
    have ha : a k.val = -q k.rev := by
      simp [a, sixVertexOddNegativeHalfRootPartition, k.isLt]
      congr 2
      omega
    rw [ha]
    congr 2
    simp [Fin.rev]
    omega
  have ha0 : a 0 = -q ⟨m - 1, by omega⟩ := by
    simp [a, sixVertexOddNegativeHalfRootPartition, hm]
  have ham : a m = 0 := by simp [a, sixVertexOddNegativeHalfRootPartition]
  rw [hsum, ha0, ham] at hquad
  have hlast := sixVertexOddSymmetricLift_positive_mem_Icc hopen
    ⟨m - 1, by omega⟩
  have hL : 0 ≤ (L : Real) := NNReal.coe_nonneg _
  have hmesh0 : 0 ≤ mesh :=
    (sixVertexOddPositiveHalfRootGap_pos_of_open hopen ⟨0, hm⟩).le.trans
      (hmesh ⟨0, hm⟩)
  change _ ≤ (L : Real) * mesh * (2 * Real.pi)
  calc
    _ ≤ (L : Real) * mesh * (0 - -q ⟨m - 1, by omega⟩) := hquad
    _ ≤ (L : Real) * mesh * (2 * Real.pi) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hL hmesh0)
      linarith [hlast.2, Real.pi_pos]

theorem intervalIntegral_sixVertexOddSymmetricScatteringDerivative_root_bounds
    {c : Real} (hc : 2 < c) {m : Nat} {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (j kmax : Fin m) :
    0 ≤ ∫ y in -q kmax..0,
          sixVertexSymmetricScatteringDerivative c (-q j) y ∧
      (∫ y in -q kmax..0,
          sixVertexSymmetricScatteringDerivative c (-q j) y) ≤
        sixVertexSymmetricScatteringBoundaryBound c := by
  let H := sixVertexSymmetricScatteringDerivative c (-q j)
  have hjIcc := sixVertexOddSymmetricLift_positive_mem_Icc hopen j
  have hkIcc := sixVertexOddSymmetricLift_positive_mem_Icc hopen kmax
  have hx : -q j ∈ Set.Icc (-Real.pi) 0 :=
    ⟨neg_le_neg hjIcc.2, neg_nonpos.mpr hjIcc.1⟩
  have hnonneg (y : Real) (hy : y ∈ Set.Icc (-Real.pi) 0) : 0 ≤ H y :=
    sixVertexTheta_right_difference_nonneg hc hx hy
  have horder : -q kmax ≤ 0 := neg_nonpos.mpr hkIcc.1
  have hrootNonneg : 0 ≤ ∫ y in -q kmax..0, H y := by
    apply intervalIntegral.integral_nonneg horder
    intro y hy
    exact hnonneg y ⟨(neg_le_neg hkIcc.2).trans hy.1, hy.2⟩
  have hrootUpper : (∫ y in -q kmax..0, H y) ≤
      ∫ y in -Real.pi..0, H y := by
    apply intervalIntegral.integral_mono_interval
    · linarith [hkIcc.2]
    · exact horder
    · exact le_rfl
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
      exact hnonneg y ⟨hy.1.le, hy.2⟩
    · exact (continuous_sixVertexSymmetricScatteringDerivative hc (-q j))
        |>.intervalIntegrable (-Real.pi) 0
  have hboundary : (∫ y in -Real.pi..0, H y) =
      sixVertexSymmetricScatteringBoundaryIncrement c (-q j) := by
    rw [intervalIntegral_sixVertexSymmetricScatteringDerivative hc]
    rfl
  have hb := sixVertexSymmetricScatteringBoundaryIncrement_bounds hc hx
  constructor
  · exact hrootNonneg
  · rw [hboundary] at hrootUpper
    exact hrootUpper.trans hb.2

theorem abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_of_mesh
    {c : Real} (hc : 2 < c) {N m : Nat} (hm : 0 < m)
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    {mesh : Real} (hmesh : ∀ k, sixVertexOddPositiveHalfRootGap q k ≤ mesh)
    (j : Fin m) :
    |(∑ k ∈ Finset.univ.erase j,
          sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j k) -
        ∫ y in -q ⟨m - 1, by omega⟩..0,
          sixVertexSymmetricScatteringDerivative c (-q j) y| ≤
      ((2 * Real.pi) *
          (sixVertexSymmetricScatteringLipschitzConstant c : Real) +
        2 * (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1))) * mesh := by
  let H := sixVertexSymmetricScatteringDerivative c (-q j)
  let L := (sixVertexSymmetricScatteringLipschitzConstant c : Real)
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  have hgap (k : Fin m) : 0 ≤ sixVertexOddPositiveHalfRootGap q k :=
    (sixVertexOddPositiveHalfRootGap_pos_of_open hopen k).le
  have hquad := abs_sixVertexOddPositiveHalfScatteringEndpointSum_sub_integral_le
    hc hm hopen hmesh j
  have hterm (k : Fin m) :
      |sixVertexOddPositiveHalfRootGap q k * H (-q k)| ≤ 2 * R * mesh := by
    rw [abs_mul, abs_of_nonneg (hgap k)]
    have hH := abs_sixVertexSymmetricScatteringDerivative_le hc (-q j) (-q k)
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    have hR : 0 ≤ 2 * R := by
      dsimp [R]
      positivity
    calc
      sixVertexOddPositiveHalfRootGap q k * |H (-q k)| ≤
          sixVertexOddPositiveHalfRootGap q k * (2 * R) :=
        mul_le_mul_of_nonneg_left hH (hgap k)
      _ ≤ mesh * (2 * R) := mul_le_mul_of_nonneg_right (hmesh k) hR
      _ = _ := by ring
  have hoffEq :
      (∑ k ∈ Finset.univ.erase j,
          sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j k) =
        ∑ k ∈ Finset.univ.erase j,
          sixVertexOddPositiveHalfRootGap q k * H (-q k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : j ≠ k := Ne.symm (Finset.mem_erase.mp hk).1
    rw [sixVertexBetheOddPositiveHalfScaledJacobianMatrix,
      sixVertexBetheOddPositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative
        hkj]
    ring
  have herase :
      (∑ k ∈ Finset.univ.erase j,
          sixVertexOddPositiveHalfRootGap q k * H (-q k)) =
        (∑ k, sixVertexOddPositiveHalfRootGap q k * H (-q k)) -
          sixVertexOddPositiveHalfRootGap q j * H (-q j) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    ring
  rw [hoffEq, herase]
  calc
    |((∑ k, sixVertexOddPositiveHalfRootGap q k * H (-q k)) -
        sixVertexOddPositiveHalfRootGap q j * H (-q j)) -
        ∫ y in -q ⟨m - 1, by omega⟩..0, H y| ≤
      |(∑ k, sixVertexOddPositiveHalfRootGap q k * H (-q k)) -
        ∫ y in -q ⟨m - 1, by omega⟩..0, H y| +
        |sixVertexOddPositiveHalfRootGap q j * H (-q j)| := by
      rw [show ((∑ k, sixVertexOddPositiveHalfRootGap q k * H (-q k)) -
          sixVertexOddPositiveHalfRootGap q j * H (-q j)) -
          (∫ y in -q ⟨m - 1, by omega⟩..0, H y) =
        ((∑ k, sixVertexOddPositiveHalfRootGap q k * H (-q k)) -
          (∫ y in -q ⟨m - 1, by omega⟩..0, H y)) -
          sixVertexOddPositiveHalfRootGap q j * H (-q j) by ring]
      exact abs_sub _ _
    _ ≤ L * mesh * (2 * Real.pi) + 2 * R * mesh :=
      add_le_add hquad (hterm j)
    _ = _ := by ring

theorem sixVertexOddSymmetricBetheRootJacobian_injective_of_scaledDiagonalDominance
    {N m : Nat} {c : Real} (hc : 2 < c) (q : Fin m → Real)
    (hgap : ∀ k, sixVertexOddPositiveHalfRootGap q k ≠ 0)
    (hdom : ∀ j,
      ∑ k ∈ Finset.univ.erase j,
          ‖sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j k‖ <
        ‖sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j j‖) :
    Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m c q) := by
  let A := sixVertexBetheOddPositiveHalfJacobianMatrix N m c q
  let D := Matrix.diagonal (sixVertexOddPositiveHalfRootGap q)
  let B := sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q
  have hdetB : Matrix.det B ≠ 0 := det_ne_zero_of_sum_row_lt_diag hdom
  have hBD : B = A * D := by
    ext j k
    rw [Matrix.mul_diagonal]
    rfl
  have hdetD : Matrix.det D ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => hgap k)
  have hdetA : Matrix.det A ≠ 0 := by
    intro hzero
    apply hdetB
    rw [hBD, Matrix.det_mul, hzero, zero_mul]
  have hmatrix : LinearMap.toMatrix'
      (sixVertexOddSymmetricBetheRootJacobian N m c q).toLinearMap = A := by
    ext j k
    exact sixVertexOddSymmetricBetheRootJacobian_toMatrix'_apply hc q j k
  have hdetJ : LinearMap.det
      (sixVertexOddSymmetricBetheRootJacobian N m c q).toLinearMap ≠ 0 := by
    rw [← LinearMap.det_toMatrix', hmatrix]
    exact hdetA
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hdetJ ((LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker)

theorem sixVertexOddSymmetricBetheRootJacobian_injective_of_sourceBounds
    {N m : Nat} {c : Real} (hc : 2 < c) (q : Fin m → Real)
    (hq : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (G : Fin m → Real) (eps M : Real)
    (heps : 0 ≤ eps) (hM : 0 ≤ M)
    (hmargin : M + 2 * eps < 2 * Real.pi)
    (hdiag : ∀ j,
      |sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j j -
        2 * Real.pi| ≤ eps)
    (hoff : ∀ j,
      |(∑ k ∈ Finset.univ.erase j,
          sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j k) -
        G j| ≤ eps)
    (hG : ∀ j, 0 ≤ G j ∧ G j ≤ M) :
    Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m c q) := by
  apply sixVertexOddSymmetricBetheRootJacobian_injective_of_scaledDiagonalDominance
    hc q (fun k => (sixVertexOddPositiveHalfRootGap_pos_of_open hq k).ne')
  intro j
  let B := sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q
  have hoffNonneg (k : Fin m) (hkj : k ∈ Finset.univ.erase j) :
      0 ≤ B j k := by
    have hne : j ≠ k := Ne.symm (Finset.mem_erase.mp hkj).1
    unfold B sixVertexBetheOddPositiveHalfScaledJacobianMatrix
    apply mul_nonneg
    · rw [sixVertexBetheOddPositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative
        hne]
      exact sixVertexTheta_right_difference_nonneg hc
        ⟨by linarith [(sixVertexOddSymmetricLift_positive_mem_Icc hq j).2],
          by linarith [(sixVertexOddSymmetricLift_positive_mem_Icc hq j).1]⟩
        ⟨by linarith [(sixVertexOddSymmetricLift_positive_mem_Icc hq k).2],
          by linarith [(sixVertexOddSymmetricLift_positive_mem_Icc hq k).1]⟩
    · exact (sixVertexOddPositiveHalfRootGap_pos_of_open hq k).le
  have hsumNorm : (∑ k ∈ Finset.univ.erase j, ‖B j k‖) =
      ∑ k ∈ Finset.univ.erase j, B j k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Real.norm_eq_abs, abs_of_nonneg (hoffNonneg k hk)]
  have hsumUpper : (∑ k ∈ Finset.univ.erase j, B j k) ≤ G j + eps := by
    have h := hoff j
    rw [abs_le] at h
    linarith
  have hdiagLower : 2 * Real.pi - eps ≤ B j j := by
    have h := hdiag j
    rw [abs_le] at h
    linarith
  have hdiagPos : 0 < B j j := by
    have hepsBound : eps < Real.pi := by nlinarith [hmargin, hM, Real.pi_pos]
    linarith [Real.pi_pos]
  rw [hsumNorm, Real.norm_eq_abs, abs_of_pos hdiagPos]
  calc
    (∑ k ∈ Finset.univ.erase j, B j k) ≤ G j + eps := hsumUpper
    _ ≤ M + eps := by linarith [(hG j).2]
    _ < 2 * Real.pi - eps := by linarith
    _ ≤ B j j := hdiagLower

theorem sixVertexOddSymmetricBetheRootJacobian_injective_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hcount : (m + 1) + m ≤ N) {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q))
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q) x)
    (hmargin : sixVertexSymmetricScatteringBoundaryBound c +
      2 * sixVertexSymmetricJacobianTotalErrorOfLower c N lower <
        2 * Real.pi) :
    Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m c q) := by
  let mesh := 1 / ((N : Real) * lower)
  let G : Fin m → Real := fun j =>
    ∫ y in -q ⟨m - 1, by omega⟩..0,
      sixVertexSymmetricScatteringDerivative c (-q j) y
  let D := sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower
  let O := sixVertexSymmetricJacobianOffDiagonalErrorOfLower c N lower
  let eps := sixVertexSymmetricJacobianTotalErrorOfLower c N lower
  let M := sixVertexSymmetricScatteringBoundaryBound c
  have hD : 0 ≤ D := by
    dsimp [D, sixVertexSymmetricJacobianDiagonalErrorOfLower]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hO : 0 ≤ O := by
    dsimp [O, sixVertexSymmetricJacobianOffDiagonalErrorOfLower]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have heps : 0 ≤ eps := by dsimp [eps, sixVertexSymmetricJacobianTotalErrorOfLower]; linarith
  have hM : 0 ≤ M := sixVertexSymmetricScatteringBoundaryBound_nonneg hc
  have hmesh (k : Fin m) : sixVertexOddPositiveHalfRootGap q k ≤ mesh :=
    sixVertexOddPositiveHalfRootGap_upper_of_finiteDensityLower
      hc hN hopen hsol hlower hdensity k
  apply sixVertexOddSymmetricBetheRootJacobian_injective_of_sourceBounds
    hc q hopen G eps M heps hM hmargin
  · intro j
    exact (abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower
      hc hN hcount hopen hsol hlower hdensity j).trans (by
        dsimp [D, eps, sixVertexSymmetricJacobianTotalErrorOfLower]
        linarith)
  · intro j
    have hoff :=
      abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_of_mesh
        (N := N) hc hm hopen hmesh j
    have hoffO : |(∑ k ∈ Finset.univ.erase j,
          sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j k) -
        G j| ≤ O := by
      simpa [G, O, mesh,
        sixVertexSymmetricJacobianOffDiagonalErrorOfLower] using hoff
    exact hoffO.trans (by
      dsimp [O, eps, sixVertexSymmetricJacobianTotalErrorOfLower]
      linarith)
  · intro j
    exact intervalIntegral_sixVertexOddSymmetricScatteringDerivative_root_bounds
      hc hopen j ⟨m - 1, by omega⟩

theorem sixVertexOddSymmetricBetheRootJacobian_injective_of_weightedDensityClose
    {c : Real} (hc : 2 < c) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hcount : (m + 1) + m ≤ N) {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q))
    {rho : Real → Real} {rhoLower eta : Real}
    (hrhoLower : 0 < rhoLower) (hrho : ∀ x, rhoLower ≤ rho x)
    (heta : eta ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) / 2)
    (hclose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N ((m + 1) + m)
          (sixVertexOddSymmetricLift m q) x - rho x)| ≤ eta)
    (hmargin : sixVertexSymmetricScatteringBoundaryBound c +
      2 * sixVertexSymmetricJacobianTotalErrorOfLower c N
        (rhoLower / 2) < 2 * Real.pi) :
    Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m c q) := by
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  have hdensityHalf : ∀ x, rhoLower / 2 ≤
      sixVertexFiniteRootDensity c N ((m + 1) + m)
        (sixVertexOddSymmetricLift m q) x := by
    intro x
    obtain ⟨y, hy, hxy⟩ :=
      (periodic_sixVertexFiniteRootDensity c N ((m + 1) + m)
        (sixVertexOddSymmetricLift m q)).exists_mem_Ioc
          (by positivity : 0 < 2 * Real.pi) x (-Real.pi)
    have hy' : y ∈ Set.Icc (-Real.pi) Real.pi := by
      constructor
      · exact hy.1.le
      · calc y ≤ -Real.pi + 2 * Real.pi := hy.2
             _ = Real.pi := by ring
    have hx := sixVertexFiniteRootDensity_lower_at_of_weighted_close
      hc (sixVertexOddSymmetricLift m q) (hrho y) (hclose y hy')
    change rhoLower - eta / wmin ≤ _ at hx
    have heta' : eta / wmin ≤ rhoLower / 2 := by
      rw [div_le_iff₀ hwmin]
      calc
        eta ≤ rhoLower * wmin / 2 := by simpa [wmin] using heta
        _ = rhoLower / 2 * wmin := by ring
    rw [hxy]
    linarith
  exact sixVertexOddSymmetricBetheRootJacobian_injective_of_finiteDensityLower
    hc hm hN hcount hopen hsol (by linarith) hdensityHalf hmargin

theorem sixVertexContinuationWeightedFiniteDensityGauge_oddJacobianInjective
    {a b : Real} (ha : 2 < a) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hhalf : 2 * ((m + 1) + m) ≤ N)
    (hcount : (m + 1) + m ≤ N)
    (rho : C(Set.Icc a b × Real, Real))
    {rhoLower outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ (t : Set.Icc a b) x,
      rhoLower ≤ sixVertexContinuumDensityAt rho t x)
    (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude t.1 - 1) /
        sixVertexRootDensityScale t.1) / 2)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower
          t.1 N (rhoLower / 2) < 2 * Real.pi)
    (z : SixVertexBetheContinuationSpace a b N ((m + 1) + m))
    (hgauge : sixVertexContinuationWeightedFiniteDensityGauge
      ha N ((m + 1) + m) rho z < outer) :
    Function.Injective
      (sixVertexOddSymmetricBetheRootJacobian N m z.1.1
        (sixVertexOddPositiveHalfProjection m z.1.2)) := by
  let t : Set.Icc a b := ⟨z.1.1, z.2.1⟩
  let q : Fin m → Real := sixVertexOddPositiveHalfProjection m z.1.2
  have hc : 2 < z.1.1 := ha.trans_le z.2.1.1
  have hpopen : SixVertexOpenRootSimplex z.1.2 :=
    sixVertexBetheContinuationSet_subset_open ha hhalf z.2
  have hlift : sixVertexOddSymmetricLift m q = z.1.2 :=
    sixVertexOddSymmetricLift_projection m hpopen.2.1
  have hsol : SixVertexSatisfiesBetheEquations z.1.1 N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q) := by
    rw [hlift]
    exact (sixVertexBetheUpdate_eq_self_iff hN z.1.2).mp z.2.2.2
  apply sixVertexOddSymmetricBetheRootJacobian_injective_of_weightedDensityClose
    hc hm hN hcount (by simpa [hlift] using hpopen) hsol hrhoLower (hrho t)
    (houter t)
  · intro x hx
    have hg := abs_weightedFiniteDensity_sub_le_gauge (N := N) hc z.1.2
      (sixVertexContinuumDensitySection rho z) x hx
    have hgauge' : sixVertexWeightedFiniteDensityGauge hc N ((m + 1) + m)
        z.1.2 (sixVertexContinuumDensitySection rho z) < outer := by
      simpa [sixVertexContinuationWeightedFiniteDensityGauge] using hgauge
    rw [← hlift] at hg
    rw [← hlift] at hgauge'
    exact hg.trans hgauge'.le
  · exact hmargin t

end

end StatMech.FrontierD
