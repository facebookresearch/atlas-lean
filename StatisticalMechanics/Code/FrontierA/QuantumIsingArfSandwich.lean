/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace StatMech.FrontierA


noncomputable def arfSectorNormMax (sector : Fin 2 -> Fin 2 -> Complex) : Real :=
  max (max ‖sector 1 1‖ ‖sector 0 1‖)
    (max ‖sector 1 0‖ ‖sector 0 0‖)

theorem norm_le_arfSectorNormMax
    (sector : Fin 2 -> Fin 2 -> Complex) (a b : Fin 2) :
    ‖sector a b‖ <= arfSectorNormMax sector := by
  fin_cases a <;> fin_cases b <;>
    simp [arfSectorNormMax]




theorem arfSectorNormMax_le_and_le_two_mul
    (Z : Real) (sector : Fin 2 -> Fin 2 -> Complex)
    (hZ : 0 < Z)
    (hdom : forall a b, ‖sector a b‖ <= Z)
    (harf : (2 * Z : Real) =
      sector 1 1 + sector 0 1 + sector 1 0 - sector 0 0) :
    arfSectorNormMax sector <= Z ∧
      Z <= 2 * arfSectorNormMax sector := by
  let M := arfSectorNormMax sector
  have hMupper : M <= Z := by
    dsimp [M, arfSectorNormMax]
    exact max_le (max_le (hdom 1 1) (hdom 0 1))
      (max_le (hdom 1 0) (hdom 0 0))
  have hterm (a b : Fin 2) : ‖sector a b‖ <= M := by
    exact norm_le_arfSectorNormMax sector a b
  have hsum :
      ‖sector 1 1 + sector 0 1 + sector 1 0 - sector 0 0‖ <= 4 * M := by
    calc
      _ <= ‖sector 1 1 + sector 0 1 + sector 1 0‖ + ‖sector 0 0‖ :=
        norm_sub_le _ _
      _ <= (‖sector 1 1 + sector 0 1‖ + ‖sector 1 0‖) +
          ‖sector 0 0‖ := by
        gcongr
        exact norm_add_le _ _
      _ <= ((‖sector 1 1‖ + ‖sector 0 1‖) + ‖sector 1 0‖) +
          ‖sector 0 0‖ := by
        gcongr
        exact norm_add_le _ _
      _ <= 4 * M := by
        nlinarith [hterm 1 1, hterm 0 1, hterm 1 0, hterm 0 0]
  have harfNorm := congrArg norm harf
  have htwoZ : ‖((2 * Z : Real) : Complex)‖ = 2 * Z := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hZ)]
  have hZlower : Z <= 2 * M := by
    rw [htwoZ] at harfNorm
    nlinarith [harfNorm.trans_le hsum]
  exact ⟨hMupper, hZlower⟩


theorem arfSector_log_sandwich
    (Z : Real) (sector : Fin 2 -> Fin 2 -> Complex)
    (hZ : 0 < Z)
    (hdom : forall a b, ‖sector a b‖ <= Z)
    (harf : (2 * Z : Real) =
      sector 1 1 + sector 0 1 + sector 1 0 - sector 0 0) :
    Real.log (arfSectorNormMax sector) <= Real.log Z ∧
      Real.log Z <= Real.log (arfSectorNormMax sector) + Real.log 2 := by
  obtain ⟨hMZ, hZM⟩ :=
    arfSectorNormMax_le_and_le_two_mul Z sector hZ hdom harf
  let M := arfSectorNormMax sector
  have hM : 0 < M := by
    by_contra h
    have hMnonpos : M <= 0 := le_of_not_gt h
    have hMnonneg : 0 <= M := by
      dsimp [M, arfSectorNormMax]
      positivity
    have : M = 0 := le_antisymm hMnonpos hMnonneg
    dsimp [M] at this hZM
    rw [this] at hZM
    linarith
  constructor
  · exact Real.log_le_log hM hMZ
  · calc
      Real.log Z <= Real.log (2 * M) := Real.log_le_log hZ hZM
      _ = Real.log M + Real.log 2 := by
        rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hM.ne']
        ring
      _ = _ := rfl



theorem arfSector_normalizedLog_gap_tendsto_zero_of_eventually
    (Z : Nat -> Real) (sector : Nat -> Fin 2 -> Fin 2 -> Complex)
    (hZ : ∀ᶠ n in Filter.atTop, 0 < Z n)
    (hdom : ∀ᶠ n in Filter.atTop,
      forall a b, ‖sector n a b‖ <= Z n)
    (harf : ∀ᶠ n in Filter.atTop, (2 * Z n : Real) =
      sector n 1 1 + sector n 0 1 + sector n 1 0 - sector n 0 0) :
    Filter.Tendsto
      (fun n : Nat =>
        (Real.log (Z n) - Real.log (arfSectorNormMax (sector n))) /
          (n + 1 : Real))
      Filter.atTop (nhds 0) := by
  have hupper : Filter.Tendsto
      (fun n : Nat => Real.log 2 / (n + 1 : Real))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => Real.log 2) Filter.atTop (nhds (Real.log 2))).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    simpa [div_eq_mul_inv] using h
  apply squeeze_zero'
    (f := fun n : Nat =>
      (Real.log (Z n) - Real.log (arfSectorNormMax (sector n))) /
        (n + 1 : Real))
    (g := fun n : Nat => Real.log 2 / (n + 1 : Real))
  · filter_upwards [hZ, hdom, harf] with n hZn hdomn harfn
    have hs := arfSector_log_sandwich (Z n) (sector n)
      hZn hdomn harfn
    exact div_nonneg (sub_nonneg.mpr hs.1) (by positivity)
  · filter_upwards [hZ, hdom, harf] with n hZn hdomn harfn
    have hs := arfSector_log_sandwich (Z n) (sector n)
      hZn hdomn harfn
    have hden : 0 < (n + 1 : Real) := by positivity
    exact div_le_div_of_nonneg_right (by linarith [hs.2]) hden.le
  · exact hupper



theorem arfSector_normalizedLog_gap_tendsto_zero
    (Z : Nat -> Real) (sector : Nat -> Fin 2 -> Fin 2 -> Complex)
    (hZ : forall n, 0 < Z n)
    (hdom : forall n a b, ‖sector n a b‖ <= Z n)
    (harf : forall n, (2 * Z n : Real) =
      sector n 1 1 + sector n 0 1 + sector n 1 0 - sector n 0 0) :
    Filter.Tendsto
      (fun n : Nat =>
        (Real.log (Z n) - Real.log (arfSectorNormMax (sector n))) /
          (n + 1 : Real))
      Filter.atTop (nhds 0) := by
  apply arfSector_normalizedLog_gap_tendsto_zero_of_eventually Z sector
  · exact Filter.Eventually.of_forall hZ
  · exact Filter.Eventually.of_forall hdom
  · exact Filter.Eventually.of_forall harf

end StatMech.FrontierA
