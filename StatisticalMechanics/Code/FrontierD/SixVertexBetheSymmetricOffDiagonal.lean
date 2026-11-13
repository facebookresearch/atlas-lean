/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSymmetricScatteringBound
import Code.FrontierD.SixVertexBetheSymmetricCovering





open Filter Topology

namespace StatMech.FrontierD

noncomputable section

def sixVertexNegativeHalfRootPartition
    {m : Nat} (q : Fin m → Real) (hm : 0 < m) (k : Nat) : Real :=
  if hk : k < m then -q ⟨m - 1 - k, by omega⟩ else q ⟨0, hm⟩

theorem sixVertexNegativeHalfRootPartition_of_lt
    {m : Nat} (q : Fin m → Real) (hm : 0 < m) {k : Nat} (hk : k < m) :
    sixVertexNegativeHalfRootPartition q hm k =
      -q ⟨m - 1 - k, by omega⟩ := by
  simp [sixVertexNegativeHalfRootPartition, hk]

@[simp] theorem sixVertexNegativeHalfRootPartition_end
    {m : Nat} (q : Fin m → Real) (hm : 0 < m) :
    sixVertexNegativeHalfRootPartition q hm m = q ⟨0, hm⟩ := by
  simp [sixVertexNegativeHalfRootPartition]

theorem sixVertexNegativeHalfRootPartition_zero
    {m : Nat} (q : Fin m → Real) (hm : 0 < m) :
    sixVertexNegativeHalfRootPartition q hm 0 = -q ⟨m - 1, by omega⟩ := by
  rw [sixVertexNegativeHalfRootPartition_of_lt q hm hm]
  congr 2

theorem sixVertexNegativeHalfRootPartition_cellGap
    {m : Nat} (q : Fin m → Real) (hm : 0 < m)
    (k : Nat) (hk : k < m) :
    sixVertexNegativeHalfRootPartition q hm (k + 1) -
        sixVertexNegativeHalfRootPartition q hm k =
      sixVertexPositiveHalfRootGap q ⟨m - 1 - k, by omega⟩ := by
  rw [sixVertexNegativeHalfRootPartition_of_lt q hm hk]
  unfold sixVertexPositiveHalfRootGap
  by_cases hlast : k + 1 = m
  · have hnot : ¬ k + 1 < m := by omega
    rw [sixVertexNegativeHalfRootPartition]
    simp only [hnot, ↓reduceDIte]
    split_ifs with hz
    · have heq : (⟨0, hm⟩ : Fin m) = ⟨m - 1 - k, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      rw [heq]
      ring
    · omega
  · have hsucc : k + 1 < m := by omega
    rw [sixVertexNegativeHalfRootPartition_of_lt q hm hsucc]
    split_ifs with hz
    · change m - 1 - k = 0 at hz
      omega
    · have heq : (⟨m - 1 - (k + 1), by omega⟩ : Fin m) =
          ⟨(m - 1 - k) - 1, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      rw [heq]
      ring

theorem sixVertexNegativeHalfRootPartition_ordered
    {m : Nat} {q : Fin m → Real} (hm : 0 < m)
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q)) :
    ∀ k < m, sixVertexNegativeHalfRootPartition q hm k ≤
      sixVertexNegativeHalfRootPartition q hm (k + 1) := by
  intro k hk
  rw [← sub_nonneg,
    sixVertexNegativeHalfRootPartition_cellGap q hm k hk]
  exact (sixVertexPositiveHalfRootGap_pos_of_open hopen _).le

theorem sixVertexNegativeHalfRootPartition_fin
    {m : Nat} (q : Fin m → Real) (hm : 0 < m) (k : Fin m) :
    sixVertexNegativeHalfRootPartition q hm k.val = -q k.rev := by
  rw [sixVertexNegativeHalfRootPartition_of_lt q hm k.isLt]
  congr 2
  apply Fin.ext
  simp only [Fin.rev, Fin.val_mk]
  omega

theorem sixVertexNegativeHalfRootPartition_fin_cellGap
    {m : Nat} (q : Fin m → Real) (hm : 0 < m) (k : Fin m) :
    sixVertexNegativeHalfRootPartition q hm (k.val + 1) -
        sixVertexNegativeHalfRootPartition q hm k.val =
      sixVertexPositiveHalfRootGap q k.rev := by
  rw [sixVertexNegativeHalfRootPartition_cellGap q hm k.val k.isLt]
  congr 1
  apply Fin.ext
  simp only [Fin.rev, Fin.val_mk]
  omega



theorem abs_positiveHalfScatteringEndpointSum_sub_integral_le
    {c : Real} (hc : 2 < c) {m : Nat} (hm : 0 < m)
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    {mesh : Real}
    (hmesh : ∀ k, sixVertexPositiveHalfRootGap q k ≤ mesh)
    (j : Fin m) :
    |∑ k, sixVertexPositiveHalfRootGap q k *
          sixVertexSymmetricScatteringDerivative c (-q j) (-q k) -
        ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩,
          sixVertexSymmetricScatteringDerivative c (-q j) y| ≤
      (sixVertexSymmetricScatteringLipschitzConstant c : Real) *
        mesh * (2 * Real.pi) := by
  let a := sixVertexNegativeHalfRootPartition q hm
  let H := sixVertexSymmetricScatteringDerivative c (-q j)
  let L := sixVertexSymmetricScatteringLipschitzConstant c
  have hquad := abs_leftEndpointSum_sub_intervalIntegral_le
    (continuous_sixVertexSymmetricScatteringDerivative hc (-q j))
    (lipschitzWith_sixVertexSymmetricScatteringDerivative hc (-q j))
    a m (mesh := mesh)
    (sixVertexNegativeHalfRootPartition_ordered hm hopen)
    (fun k hk => by
      rw [sixVertexNegativeHalfRootPartition_cellGap q hm k hk]
      exact hmesh _)
  have hsum :
      (∑ k ∈ Finset.range m, (a (k + 1) - a k) * H (a k)) =
        ∑ k : Fin m, sixVertexPositiveHalfRootGap q k * H (-q k) := by
    rw [← Fin.sum_univ_eq_sum_range]
    have hrev := Equiv.sum_comp Fin.revPerm
      (fun k : Fin m => sixVertexPositiveHalfRootGap q k * H (-q k))
    rw [← hrev]
    apply Finset.sum_congr rfl
    intro k _
    rw [sixVertexNegativeHalfRootPartition_fin_cellGap q hm k]
    rw [show a k.val = -q k.rev by
      exact sixVertexNegativeHalfRootPartition_fin q hm k]
    rfl
  have ha0 : a 0 = -q ⟨m - 1, by omega⟩ :=
    sixVertexNegativeHalfRootPartition_zero q hm
  have ham : a m = q ⟨0, hm⟩ :=
    sixVertexNegativeHalfRootPartition_end q hm
  rw [hsum, ha0, ham] at hquad
  have hfirst := sixVertexEvenSymmetricLift_positive_mem_Icc hopen ⟨0, hm⟩
  have hlast := sixVertexEvenSymmetricLift_positive_mem_Icc hopen
    ⟨m - 1, by omega⟩
  have hL : 0 ≤ (L : Real) := NNReal.coe_nonneg _
  have hmesh0 : 0 ≤ mesh :=
    le_trans (sixVertexPositiveHalfRootGap_pos_of_open hopen ⟨0, hm⟩).le
      (hmesh ⟨0, hm⟩)
  change _ ≤ (L : Real) * mesh * (2 * Real.pi)
  calc
    |∑ k, sixVertexPositiveHalfRootGap q k * H (-q k) -
        ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩, H y| ≤
        (L : Real) * mesh *
          (q ⟨0, hm⟩ - -q ⟨m - 1, by omega⟩) := hquad
    _ ≤ (L : Real) * mesh * (2 * Real.pi) := by
      have hcoef : 0 ≤ (L : Real) * mesh := mul_nonneg hL hmesh0
      have hlen : q ⟨0, hm⟩ - -q ⟨m - 1, by omega⟩ ≤
          2 * Real.pi := by
        linarith [hfirst.2, hlast.2]
      exact mul_le_mul_of_nonneg_left hlen hcoef

theorem sixVertexBethePositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative
    {N m : Nat} {c : Real} {q : Fin m → Real}
    {j k : Fin m} (hjk : j ≠ k) :
    sixVertexBethePositiveHalfJacobianMatrix N m c q j k =
      sixVertexSymmetricScatteringDerivative c (-q j) (-q k) := by
  let p := sixVertexEvenSymmetricLift m q
  let i := Fin.natAdd m j
  let l := Fin.natAdd m k
  let lr := Fin.castAdd m k.rev
  have hil : i ≠ l := by
    intro h
    apply hjk
    have hv := congrArg Fin.val h
    apply Fin.ext
    simp [i, l, Fin.natAdd] at hv ⊢
    omega
  have hilr : i ≠ lr := by
    intro h
    have hv := congrArg Fin.val h
    simp [i, lr, Fin.natAdd, Fin.castAdd] at hv
    omega
  have hi : p i = q j := sixVertexEvenSymmetricLift_natAdd m q j
  have hl : p l = q k := sixVertexEvenSymmetricLift_natAdd m q k
  have hlr : p lr = -q k := by
    change sixVertexEvenSymmetricLift m q (Fin.castAdd m k.rev) = -q k
    rw [sixVertexEvenSymmetricLift_castAdd]
    simp
  unfold sixVertexBethePositiveHalfJacobianMatrix
  dsimp only
  rw [sixVertexBetheJacobianMatrix, if_neg hil,
    sixVertexBetheJacobianMatrix, if_neg hilr]
  simp only [sixVertexEvenSymmetricLift_natAdd,
    sixVertexEvenSymmetricLift_castAdd, Fin.rev_rev]
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
  simp only [neg_neg]

theorem sixVertexSymmetricScatteringDerivative_odd_right
    (c x y : Real) :
    sixVertexSymmetricScatteringDerivative c x (-y) =
      -sixVertexSymmetricScatteringDerivative c x y := by
  unfold sixVertexSymmetricScatteringDerivative
  have hfactor : sixVertexBetheIntegratingFactor c (-x) =
      sixVertexBetheIntegratingFactor c x := by
    simp [sixVertexBetheIntegratingFactor]
  have hden₁ : sixVertexThetaDerivativeDenominator c x (-y) =
      sixVertexThetaDerivativeDenominator c (-x) y := by
    exact sixVertexThetaDerivativeDenominator_neg_right c x y
  have hden₂ : sixVertexThetaDerivativeDenominator c (-x) (-y) =
      sixVertexThetaDerivativeDenominator c x y := by
    unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
    simp only [Real.cos_neg, Real.sin_neg]
    ring
  rw [hfactor, hden₁, hden₂]
  ring

theorem sixVertexSymmetricScatteringPhase_even_right
    (c x y : Real) :
    sixVertexSymmetricScatteringPhase c x (-y) =
      sixVertexSymmetricScatteringPhase c x y := by
  unfold sixVertexSymmetricScatteringPhase
  have h₁ := sixVertexTheta_neg c (-x) y
  have h₂ := sixVertexTheta_neg c x y
  simp only [neg_neg] at h₁
  rw [h₁, h₂]
  ring

theorem intervalIntegral_sixVertexSymmetricScatteringDerivative_symmetric
    {c : Real} (hc : 2 < c) (x a : Real) :
    ∫ y in -a..a, sixVertexSymmetricScatteringDerivative c x y = 0 := by
  rw [intervalIntegral_sixVertexSymmetricScatteringDerivative hc]
  rw [sixVertexSymmetricScatteringPhase_even_right]
  ring




theorem intervalIntegral_sixVertexSymmetricScatteringDerivative_root_bounds
    {c : Real} (hc : 2 < c) {m : Nat} {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (j k0 kmax : Fin m) (hk0 : q k0 ≤ q kmax) :
    0 ≤ ∫ y in -q kmax..q k0,
          sixVertexSymmetricScatteringDerivative c (-q j) y ∧
      (∫ y in -q kmax..q k0,
          sixVertexSymmetricScatteringDerivative c (-q j) y) ≤
        sixVertexSymmetricScatteringBoundaryBound c := by
  let H := sixVertexSymmetricScatteringDerivative c (-q j)
  have hjIcc := sixVertexEvenSymmetricLift_positive_mem_Icc hopen j
  have hk0Icc := sixVertexEvenSymmetricLift_positive_mem_Icc hopen k0
  have hkmaxIcc := sixVertexEvenSymmetricLift_positive_mem_Icc hopen kmax
  have hx : -q j ∈ Set.Icc (-Real.pi) 0 :=
    ⟨neg_le_neg hjIcc.2, neg_nonpos.mpr hjIcc.1⟩
  have hnonneg (y : Real) (hy : y ∈ Set.Icc (-Real.pi) 0) : 0 ≤ H y :=
    sixVertexTheta_right_difference_nonneg hc hx hy
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume)
    (b := -q k0)
    ((continuous_sixVertexSymmetricScatteringDerivative hc (-q j)).intervalIntegrable
      (-q kmax) (-q k0))
    ((continuous_sixVertexSymmetricScatteringDerivative hc (-q j)).intervalIntegrable
      (-q k0) (q k0))
  have hcentral :=
    intervalIntegral_sixVertexSymmetricScatteringDerivative_symmetric
      hc (-q j) (q k0)
  have hrootEq : (∫ y in -q kmax..q k0, H y) =
      ∫ y in -q kmax..-q k0, H y := by
    rw [← hsplit]
    rw [hcentral, add_zero]
  have horder : -q kmax ≤ -q k0 := neg_le_neg hk0
  have hrootNonneg : 0 ≤ ∫ y in -q kmax..-q k0, H y := by
    apply intervalIntegral.integral_nonneg horder
    intro y hy
    apply hnonneg y
    exact ⟨(neg_le_neg hkmaxIcc.2).trans hy.1,
      hy.2.trans (neg_nonpos.mpr hk0Icc.1)⟩
  have hrootUpper : (∫ y in -q kmax..-q k0, H y) ≤
      ∫ y in -Real.pi..0, H y := by
    apply intervalIntegral.integral_mono_interval
    · linarith [hkmaxIcc.2]
    · exact horder
    · linarith [hk0Icc.1]
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
      change 0 ≤ H y
      exact hnonneg y ⟨hy.1.le, hy.2⟩
    · exact (continuous_sixVertexSymmetricScatteringDerivative hc (-q j)).intervalIntegrable
        (-Real.pi) 0
  have hboundary : (∫ y in -Real.pi..0, H y) =
      sixVertexSymmetricScatteringBoundaryIncrement c (-q j) := by
    rw [intervalIntegral_sixVertexSymmetricScatteringDerivative hc]
    rfl
  have hb := sixVertexSymmetricScatteringBoundaryIncrement_bounds hc hx
  rw [hrootEq]
  constructor
  · exact hrootNonneg
  · rw [hboundary] at hrootUpper
    exact hrootUpper.trans hb.2

theorem abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_of_mesh
    {c : Real} (hc : 2 < c) {N m : Nat} (hm : 0 < m)
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    {mesh : Real}
    (hmesh : ∀ k, sixVertexPositiveHalfRootGap q k ≤ mesh)
    (j : Fin m) :
    |(∑ k ∈ Finset.univ.erase j,
          sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k) -
        ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩,
          sixVertexSymmetricScatteringDerivative c (-q j) y| ≤
      ((2 * Real.pi) *
          (sixVertexSymmetricScatteringLipschitzConstant c : Real) +
        2 * (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1))) * mesh := by
  let H := sixVertexSymmetricScatteringDerivative c (-q j)
  let L := (sixVertexSymmetricScatteringLipschitzConstant c : Real)
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  have hgap (k : Fin m) : 0 ≤ sixVertexPositiveHalfRootGap q k :=
    (sixVertexPositiveHalfRootGap_pos_of_open hopen k).le
  have hquad := abs_positiveHalfScatteringEndpointSum_sub_integral_le
    hc hm hopen hmesh j
  have hterm (k : Fin m) :
      |sixVertexPositiveHalfRootGap q k * H (-q k)| ≤ 2 * R * mesh := by
    rw [abs_mul, abs_of_nonneg (hgap k)]
    have hH := abs_sixVertexSymmetricScatteringDerivative_le hc (-q j) (-q k)
    have hR : 0 ≤ 2 * R := by
      have hd := one_lt_sixVertexAnisotropyMagnitude hc
      exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by linarith))
    calc
      sixVertexPositiveHalfRootGap q k * |H (-q k)| ≤
          sixVertexPositiveHalfRootGap q k * (2 * R) :=
        mul_le_mul_of_nonneg_left hH (hgap k)
      _ ≤ mesh * (2 * R) := mul_le_mul_of_nonneg_right (hmesh k) hR
      _ = 2 * R * mesh := by ring
  have hoffEq :
      (∑ k ∈ Finset.univ.erase j,
          sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k) =
        ∑ k ∈ Finset.univ.erase j,
          sixVertexPositiveHalfRootGap q k * H (-q k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : j ≠ k := Ne.symm (Finset.mem_erase.mp hk).1
    rw [sixVertexBethePositiveHalfScaledJacobianMatrix,
      sixVertexBethePositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative hkj]
    ring
  let I := ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩, H y
  have herase :
      (∑ k ∈ Finset.univ.erase j,
          sixVertexPositiveHalfRootGap q k * H (-q k)) =
        (∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) -
          sixVertexPositiveHalfRootGap q j * H (-q j) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    ring
  rw [hoffEq, herase]
  change |((∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) -
      sixVertexPositiveHalfRootGap q j * H (-q j)) - I| ≤
        ((2 * Real.pi) * L + 2 * R) * mesh
  calc
    |((∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) -
        sixVertexPositiveHalfRootGap q j * H (-q j)) - I| ≤
      |(∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) - I| +
        |sixVertexPositiveHalfRootGap q j * H (-q j)| := by
      rw [show ((∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) -
          sixVertexPositiveHalfRootGap q j * H (-q j)) - I =
        ((∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) - I) -
          sixVertexPositiveHalfRootGap q j * H (-q j) by ring]
      exact abs_sub _ _
    _ ≤ L * mesh * (2 * Real.pi) + 2 * R * mesh :=
      add_le_add hquad (hterm j)
    _ = ((2 * Real.pi) * L + 2 * R) * mesh := by ring

def sixVertexSymmetricTailJacobianOffDiagonalError
    (c : Real) (N : Nat) : Real :=
  ((2 * Real.pi) *
      (sixVertexSymmetricScatteringLipschitzConstant c : Real) +
    2 * (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1))) *
    (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c))


theorem abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N m : Nat} (hm : 0 < m) (hN : 0 < N) (hhalf : N = 2 * (m + m))
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q)) (j : Fin m) :
    |(∑ k ∈ Finset.univ.erase j,
          sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k) -
        ∫ y in -q ⟨m - 1, by
              omega⟩..q ⟨0, hm⟩,
          sixVertexSymmetricScatteringDerivative c (-q j) y| ≤
      sixVertexSymmetricTailJacobianOffDiagonalError c N := by
  let mesh := 1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)
  let H := sixVertexSymmetricScatteringDerivative c (-q j)
  let L := (sixVertexSymmetricScatteringLipschitzConstant c : Real)
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  have hgap (k : Fin m) : 0 ≤ sixVertexPositiveHalfRootGap q k :=
    (sixVertexPositiveHalfRootGap_pos_of_open hopen k).le
  have hmesh (k : Fin m) : sixVertexPositiveHalfRootGap q k ≤ mesh :=
    sixVertexPositiveHalfRootGap_upper_tail hc htail hN hhalf hopen hsol k
  have hquad := abs_positiveHalfScatteringEndpointSum_sub_integral_le
    hc hm hopen hmesh j
  have hterm (k : Fin m) :
      |sixVertexPositiveHalfRootGap q k * H (-q k)| ≤ 2 * R * mesh := by
    rw [abs_mul, abs_of_nonneg (hgap k)]
    have hH := abs_sixVertexSymmetricScatteringDerivative_le hc (-q j) (-q k)
    have hR : 0 ≤ 2 * R := by
      have hd := one_lt_sixVertexAnisotropyMagnitude hc
      exact mul_nonneg (by norm_num) (div_nonneg (by linarith) (by linarith))
    calc
      sixVertexPositiveHalfRootGap q k * |H (-q k)| ≤
          sixVertexPositiveHalfRootGap q k * (2 * R) :=
        mul_le_mul_of_nonneg_left hH (hgap k)
      _ ≤ mesh * (2 * R) := mul_le_mul_of_nonneg_right (hmesh k) hR
      _ = 2 * R * mesh := by ring
  have hoffEq :
      (∑ k ∈ Finset.univ.erase j,
          sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k) =
        ∑ k ∈ Finset.univ.erase j,
          sixVertexPositiveHalfRootGap q k * H (-q k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : j ≠ k := Ne.symm (Finset.mem_erase.mp hk).1
    rw [sixVertexBethePositiveHalfScaledJacobianMatrix,
      sixVertexBethePositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative hkj]
    ring
  let I := ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩, H y
  have herase :
      (∑ k ∈ Finset.univ.erase j,
          sixVertexPositiveHalfRootGap q k * H (-q k)) =
        (∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) -
          sixVertexPositiveHalfRootGap q j * H (-q j) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    ring
  change _ ≤ sixVertexSymmetricTailJacobianOffDiagonalError c N
  rw [hoffEq, herase]
  unfold sixVertexSymmetricTailJacobianOffDiagonalError
  change |((∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) -
      sixVertexPositiveHalfRootGap q j * H (-q j)) - I| ≤
        ((2 * Real.pi) * L + 2 * R) * mesh
  calc
    |((∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) -
        sixVertexPositiveHalfRootGap q j * H (-q j)) - I| ≤
      |(∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) - I| +
        |sixVertexPositiveHalfRootGap q j * H (-q j)| := by
      rw [show ((∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) -
          sixVertexPositiveHalfRootGap q j * H (-q j)) - I =
        ((∑ k, sixVertexPositiveHalfRootGap q k * H (-q k)) - I) -
          sixVertexPositiveHalfRootGap q j * H (-q j) by ring]
      exact abs_sub _ _
    _ ≤ L * mesh * (2 * Real.pi) + 2 * R * mesh :=
      add_le_add hquad (hterm j)
    _ = ((2 * Real.pi) * L + 2 * R) * mesh := by ring

def sixVertexSymmetricTailJacobianTotalError (c : Real) (N : Nat) : Real :=
  sixVertexSymmetricTailJacobianDiagonalError c N +
    sixVertexSymmetricTailJacobianOffDiagonalError c N

def sixVertexSymmetricJacobianOffDiagonalErrorOfLower
    (c : Real) (N : Nat) (lower : Real) : Real :=
  ((2 * Real.pi) *
      (sixVertexSymmetricScatteringLipschitzConstant c : Real) +
    2 * (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1))) *
    (1 / ((N : Real) * lower))

def sixVertexSymmetricJacobianTotalErrorOfLower
    (c : Real) (N : Nat) (lower : Real) : Real :=
  sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower +
    sixVertexSymmetricJacobianOffDiagonalErrorOfLower c N lower

theorem sixVertexEvenSymmetricBetheRootJacobian_injective_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hcount : m + m ≤ N) {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q))
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (m + m)
      (sixVertexEvenSymmetricLift m q) x)
    (hmargin : sixVertexSymmetricScatteringBoundaryBound c +
      2 * sixVertexSymmetricJacobianTotalErrorOfLower c N lower <
        2 * Real.pi) :
    Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
  let mesh := 1 / ((N : Real) * lower)
  let G : Fin m → Real := fun j =>
    ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩,
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
  have heps : 0 ≤ eps := by
    dsimp [eps, sixVertexSymmetricJacobianTotalErrorOfLower]
    exact add_nonneg hD hO
  have hM : 0 ≤ M := sixVertexSymmetricScatteringBoundaryBound_nonneg hc
  have hmesh (k : Fin m) : sixVertexPositiveHalfRootGap q k ≤ mesh :=
    sixVertexPositiveHalfRootGap_upper_of_finiteDensityLower
      hc hN hopen hsol hlower hdensity k
  apply sixVertexEvenSymmetricBetheRootJacobian_injective_of_sourceBounds
    hc q hopen G eps M heps hM hmargin
  · intro j
    have hj :=
      abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower
        hc hN hcount hopen hsol hlower hdensity j
    exact hj.trans (by
      dsimp [eps, sixVertexSymmetricJacobianTotalErrorOfLower, D, O] at ⊢
      linarith)
  · intro j
    have hj :=
      abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_of_mesh
        (N := N) hc hm hopen hmesh j
    exact hj.trans (by
      dsimp [eps, sixVertexSymmetricJacobianTotalErrorOfLower, O,
        sixVertexSymmetricJacobianOffDiagonalErrorOfLower, mesh] at ⊢
      linarith)
  · intro j
    dsimp [G]
    apply intervalIntegral_sixVertexSymmetricScatteringDerivative_root_bounds
      hc hopen j ⟨0, hm⟩ ⟨m - 1, by omega⟩
    exact (sixVertexEvenSymmetricLift_positive_strictMono hopen).monotone (by
      simp only [Fin.le_def]
      omega)

theorem sixVertexEvenSymmetricBetheRootJacobian_injective_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hhalf : N = 2 * (m + m))
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q))
    (hmargin : sixVertexSymmetricScatteringBoundaryBound c +
      2 * sixVertexSymmetricTailJacobianTotalError c N < 2 * Real.pi) :
    Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
  let G : Fin m → Real := fun j =>
    ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩,
      sixVertexSymmetricScatteringDerivative c (-q j) y
  let D := sixVertexSymmetricTailJacobianDiagonalError c N
  let O := sixVertexSymmetricTailJacobianOffDiagonalError c N
  let eps := sixVertexSymmetricTailJacobianTotalError c N
  let M := sixVertexSymmetricScatteringBoundaryBound c
  have hfloor : 0 < sixVertexTailFiniteDensityFloor c :=
    sixVertexTailFiniteDensityFloor_pos hc htail
  have hD : 0 ≤ D := by
    dsimp [D, sixVertexSymmetricTailJacobianDiagonalError]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hO : 0 ≤ O := by
    dsimp [O, sixVertexSymmetricTailJacobianOffDiagonalError]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have heps : 0 ≤ eps := by
    dsimp [eps, sixVertexSymmetricTailJacobianTotalError]
    exact add_nonneg hD hO
  have hM : 0 ≤ M :=
    sixVertexSymmetricScatteringBoundaryBound_nonneg hc
  apply sixVertexEvenSymmetricBetheRootJacobian_injective_of_sourceBounds
    hc q hopen G eps M heps hM hmargin
  · intro j
    have hj :=
      abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_tail
        hc htail hN hhalf hopen hsol j
    exact hj.trans (by
      dsimp [eps, sixVertexSymmetricTailJacobianTotalError, D, O] at ⊢
      linarith)
  · intro j
    have hj :=
      abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_tail
        hc htail hm hN hhalf hopen hsol j
    exact hj.trans (by
      dsimp [eps, sixVertexSymmetricTailJacobianTotalError, D, O] at ⊢
      linarith)
  · intro j
    dsimp [G]
    apply intervalIntegral_sixVertexSymmetricScatteringDerivative_root_bounds
      hc hopen j ⟨0, hm⟩ ⟨m - 1, by omega⟩
    exact (sixVertexEvenSymmetricLift_positive_strictMono hopen).monotone (by
      simp only [Fin.le_def]
      omega)

theorem sixVertexSymmetricTailJacobianTotalError_fourWidth_tendsto_zero
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    Tendsto (fun k : Nat => sixVertexSymmetricTailJacobianTotalError c
      (sixVertexFourWidth 0 k)) atTop (nhds 0) := by
  let d := sixVertexAnisotropyMagnitude c
  let floor := sixVertexTailFiniteDensityFloor c
  let L := (sixVertexFiniteRootDensityLipschitzConstant c : Real)
  let S := (sixVertexSymmetricScatteringLipschitzConstant c : Real)
  let R := d / (d - 1)
  let A := Real.pi * L / floor ^ 2 + R / (2 * floor) +
    ((2 * Real.pi) * S + 2 * R) / (4 * floor)
  have hfloor : 0 < floor := sixVertexTailFiniteDensityFloor_pos hc htail
  have h := (tendsto_const_div_atTop_nhds_zero_nat A).comp
    (tendsto_add_atTop_nat 1)
  apply h.congr'
  filter_upwards [] with k
  unfold sixVertexSymmetricTailJacobianTotalError
    sixVertexSymmetricTailJacobianDiagonalError
    sixVertexSymmetricTailJacobianOffDiagonalError sixVertexFourWidth
  dsimp [A, d, floor, L, S, R]
  have hk : (0 : Real) < k + 1 := by positivity
  field_simp [hfloor.ne', hk.ne']
  push_cast
  ring

theorem eventually_sixVertexSymmetricTailJacobian_margin
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexSymmetricScatteringBoundaryBound c +
        2 * sixVertexSymmetricTailJacobianTotalError c
          (sixVertexFourWidth 0 k) < 2 * Real.pi := by
  let delta := (2 * Real.pi -
    sixVertexSymmetricScatteringBoundaryBound c) / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    have hM :=
      (sixVertexSymmetricScatteringBoundaryBound_lt_two_pi
        (c := c))
    linarith
  have hnhds : Set.Iio delta ∈ nhds (0 : Real) := Iio_mem_nhds hdelta
  have hev :=
    (sixVertexSymmetricTailJacobianTotalError_fourWidth_tendsto_zero
      hc htail).eventually hnhds
  filter_upwards [hev] with k hk
  dsimp [delta] at hk
  linarith

theorem eventually_sixVertexSelectedEvenSymmetricBetheRootJacobian_injective_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    ∀ᶠ k : Nat in atTop, Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian
        (sixVertexFourWidth 0 k) (k + 1) c
        (sixVertexPositiveHalfBetheRoots hc k)) := by
  filter_upwards [eventually_sixVertexSymmetricTailJacobian_margin hc htail]
    with k hmargin
  let p := sixVertexHalfFilledBetheRoots hc k
  let q := sixVertexPositiveHalfBetheRoots hc k
  have hopen : SixVertexOpenRootSimplex p :=
    sixVertexHalfFilledBetheRoots_mem_open hc k
  have hlift : sixVertexEvenSymmetricLift (k + 1) q = p := by
    simpa [q, p, sixVertexPositiveHalfBetheRoots] using
      sixVertexEvenSymmetricLift_projection (k + 1) hopen.2.1
  apply sixVertexEvenSymmetricBetheRootJacobian_injective_tail
    hc htail (by omega) (sixVertexFourWidth_pos 0 k)
    (by unfold sixVertexFourWidth; omega)
  · rw [hlift]
    exact hopen
  · rw [hlift]
    exact sixVertexHalfFilledBetheRoots_is_solution hc k
  · exact hmargin

end

end StatMech.FrontierD
