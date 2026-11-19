/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Labor.LaborLeisure
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

namespace MathlibExtTest.Economics.Labor.LaborLeisure

open MathlibExt.Economics.LaborLeisure

noncomputable def cdD : ℝ × ℝ →L[ℝ] ℝ :=
  (fun q : ℝ × ℝ => q.2) (1, 2) •
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (-((((fun q : ℝ × ℝ => 2 * q.1) (1, 2)) ^ 2)⁻¹))) ∘SL
        ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ)) +
    (fun q : ℝ × ℝ => (2 * q.1)⁻¹) (1, 2) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem cd_hfull : fullIncome (1 : ℝ) (1 : ℝ) (1 : ℝ) = 2 := by
  show (1 : ℝ) * 1 + 1 = 2
  norm_num

theorem cd_hf : HasFDerivAt (fun q : ℝ × ℝ => q.2)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 2) :=
  hasFDerivAt_snd

theorem cd_hg : HasFDerivAt (fun q : ℝ × ℝ => 2 * q.1)
    ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 2) :=
  HasFDerivAt.const_mul hasFDerivAt_fst (2 : ℝ)

theorem cd_hne : (fun q : ℝ × ℝ => 2 * q.1) (1, 2) ≠ 0 := by
  show (2 : ℝ) * 1 ≠ 0
  norm_num

theorem cd_hinv : HasFDerivAt (fun q : ℝ × ℝ => (2 * q.1)⁻¹)
    ((ContinuousLinearMap.toSpanSingleton ℝ
      (-((((fun q : ℝ × ℝ => 2 * q.1) (1, 2)) ^ 2)⁻¹))) ∘SL
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ)) (1, 2) :=
  HasFDerivAt.comp (1, 2) (hasFDerivAt_inv cd_hne) cd_hg

theorem cd_hmul : HasFDerivAt (fun q : ℝ × ℝ => q.2 * (2 * q.1)⁻¹) cdD (1, 2) :=
  HasFDerivAt.mul cd_hf cd_hinv

theorem cd_hℓ : HasFDerivAt (fun q : ℝ × ℝ => (fun w M : ℝ => M / (2 * w)) q.1 q.2) cdD
    (1, fullIncome (1 : ℝ) (1 : ℝ) (1 : ℝ)) := by
  rw [cd_hfull]
  simp only [div_eq_mul_inv]
  exact cd_hmul

theorem cd_hleis :
    leisureDemand (fun w M : ℝ => M / (2 * w)) (1 : ℝ) (1 : ℝ) (1 : ℝ) = 1 := by
  show ((1 : ℝ) * 1 + 1) / (2 * (1 : ℝ)) = 1
  norm_num

theorem cd_hlab :
    laborSupply (fun w M : ℝ => M / (2 * w)) (1 : ℝ) (1 : ℝ) (1 : ℝ) = 0 := by
  unfold laborSupply
  rw [cd_hleis]
  norm_num

theorem cd_hD10 : cdD (1, 0) = -1 := by
  have e2 : ((fun q : ℝ × ℝ => 2 * q.1) (1, 2) : ℝ) = 2 := by
    show (2 : ℝ) * 1 = 2
    norm_num
  have e4 : ((ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 0) : ℝ) = 1 := rfl
  have e5 : ((ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0) : ℝ) = 0 := rfl
  unfold cdD
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, e2, e4, e5, smul_eq_mul]
  norm_num

theorem cd_hD01 : cdD (0, 1) = 1 / 2 := by
  have e2 : ((fun q : ℝ × ℝ => 2 * q.1) (1, 2) : ℝ) = 2 := by
    show (2 : ℝ) * 1 = 2
    norm_num
  have e4 : ((ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 1) : ℝ) = 0 := rfl
  have e5 : ((ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 1) : ℝ) = 1 := rfl
  unfold cdD
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, e2, e4, e5, smul_eq_mul]
  norm_num

theorem cd_hslutsky : (-1 / 2 : ℝ) = cdD (1, 0) + cdD (0, 1) *
    leisureDemand (fun w M : ℝ => M / (2 * w)) 1 1 1 := by
  rw [cd_hD10, cd_hD01, cd_hleis]
  norm_num

example : HasDerivAt (leisureDemand (fun w M => M / (2 * w)) 1 1) (-1 / 2) 1 := by
  have hmain := leisureDemand_hasDerivAt cd_hℓ cd_hslutsky
  have heq : (-1 / 2 : ℝ) + laborSupply (fun w M : ℝ => M / (2 * w)) 1 1 1 * cdD (0, 1)
      = -1 / 2 := by
    rw [cd_hlab, cd_hD01]
    norm_num
  rw [heq] at hmain
  exact hmain

example : HasDerivAt (laborSupply (fun w M => M / (2 * w)) 1 1) (1 / 2) 1 := by
  have hmain := laborSupply_hasDerivAt cd_hℓ cd_hslutsky
  have heq : -(-1 / 2 : ℝ) - laborSupply (fun w M : ℝ => M / (2 * w)) 1 1 1 * cdD (0, 1)
      = 1 / 2 := by
    rw [cd_hlab, cd_hD01]
    norm_num
  rw [heq] at hmain
  exact hmain

noncomputable def cdD2 : ℝ × ℝ →L[ℝ] ℝ :=
  (fun q : ℝ × ℝ => q.2) (1, 3) •
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (-((((fun q : ℝ × ℝ => 2 * q.1) (1, 3)) ^ 2)⁻¹))) ∘SL
        ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ)) +
    (fun q : ℝ × ℝ => (2 * q.1)⁻¹) (1, 3) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem int_hfull : fullIncome (2 : ℝ) (1 : ℝ) (1 : ℝ) = 3 := by
  show (1 : ℝ) * 2 + 1 = 3
  norm_num

theorem int_hf : HasFDerivAt (fun q : ℝ × ℝ => q.2)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 3) :=
  hasFDerivAt_snd

theorem int_hg : HasFDerivAt (fun q : ℝ × ℝ => 2 * q.1)
    ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 3) :=
  HasFDerivAt.const_mul hasFDerivAt_fst (2 : ℝ)

theorem int_hne : (fun q : ℝ × ℝ => 2 * q.1) (1, 3) ≠ 0 := by
  show (2 : ℝ) * 1 ≠ 0
  norm_num

theorem int_hinv : HasFDerivAt (fun q : ℝ × ℝ => (2 * q.1)⁻¹)
    ((ContinuousLinearMap.toSpanSingleton ℝ
      (-((((fun q : ℝ × ℝ => 2 * q.1) (1, 3)) ^ 2)⁻¹))) ∘SL
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ)) (1, 3) :=
  HasFDerivAt.comp (1, 3) (hasFDerivAt_inv int_hne) int_hg

theorem int_hmul : HasFDerivAt (fun q : ℝ × ℝ => q.2 * (2 * q.1)⁻¹) cdD2 (1, 3) :=
  HasFDerivAt.mul int_hf int_hinv

theorem int_hℓ : HasFDerivAt (fun q : ℝ × ℝ => (fun w M : ℝ => M / (2 * w)) q.1 q.2) cdD2
    (1, fullIncome (2 : ℝ) (1 : ℝ) (1 : ℝ)) := by
  rw [int_hfull]
  simp only [div_eq_mul_inv]
  exact int_hmul

theorem int_hleis :
    leisureDemand (fun w M : ℝ => M / (2 * w)) (2 : ℝ) (1 : ℝ) (1 : ℝ) = 3 / 2 := by
  show ((1 : ℝ) * 2 + 1) / (2 * (1 : ℝ)) = 3 / 2
  norm_num

theorem int_hlab :
    laborSupply (fun w M : ℝ => M / (2 * w)) (2 : ℝ) (1 : ℝ) (1 : ℝ) = 1 / 2 := by
  unfold laborSupply
  rw [int_hleis]
  norm_num

theorem int_hD10 : cdD2 (1, 0) = -3 / 2 := by
  have e2 : ((fun q : ℝ × ℝ => 2 * q.1) (1, 3) : ℝ) = 2 := by
    show (2 : ℝ) * 1 = 2
    norm_num
  have e4 : ((ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 0) : ℝ) = 1 := rfl
  have e5 : ((ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0) : ℝ) = 0 := rfl
  unfold cdD2
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, e2, e4, e5, smul_eq_mul]
  norm_num

theorem int_hD01 : cdD2 (0, 1) = 1 / 2 := by
  have e2 : ((fun q : ℝ × ℝ => 2 * q.1) (1, 3) : ℝ) = 2 := by
    show (2 : ℝ) * 1 = 2
    norm_num
  have e4 : ((ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 1) : ℝ) = 0 := rfl
  have e5 : ((ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 1) : ℝ) = 1 := rfl
  unfold cdD2
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, e2, e4, e5, smul_eq_mul]
  norm_num

theorem int_hslutsky : (-3 / 4 : ℝ) = cdD2 (1, 0) + cdD2 (0, 1) *
    leisureDemand (fun w M : ℝ => M / (2 * w)) 2 1 1 := by
  rw [int_hD10, int_hD01, int_hleis]
  norm_num

example : HasDerivAt (leisureDemand (fun w M => M / (2 * w)) 2 1) (-1 / 2) 1 := by
  have hmain := leisureDemand_hasDerivAt int_hℓ int_hslutsky
  have heq : (-3 / 4 : ℝ) + laborSupply (fun w M : ℝ => M / (2 * w)) 2 1 1 * cdD2 (0, 1)
      = -1 / 2 := by
    rw [int_hlab, int_hD01]
    norm_num
  rw [heq] at hmain
  exact hmain

example : HasDerivAt (laborSupply (fun w M => M / (2 * w)) 2 1) (1 / 2) 1 := by
  have hmain := laborSupply_hasDerivAt int_hℓ int_hslutsky
  have heq : -(-3 / 4 : ℝ) - laborSupply (fun w M : ℝ => M / (2 * w)) 2 1 1 * cdD2 (0, 1)
      = 1 / 2 := by
    rw [int_hlab, int_hD01]
    norm_num
  rw [heq] at hmain
  exact hmain

end MathlibExtTest.Economics.Labor.LaborLeisure