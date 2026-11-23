/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.OperatingPointLinearization
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Electronics.OperatingPointLinearization

namespace PhyslibExtTest.Electronics.OperatingPointLinearization

/-- The quadratic law attains the factor: at deviation `3` the
remainder of linearizing `v ↦ v^2` at `0` is exactly `9`. -/
example : smallSignalRemainder (fun v : Fin 1 → ℝ => (v 0) ^ 2) 0
    (fun _ => 3) = 9 := by
  rw [smallSignal_quadratic_attains_factor]; norm_num

/-- At zero deviation the remainder vanishes for the same law. -/
example : smallSignalRemainder (fun v : Fin 1 → ℝ => (v 0) ^ 2) 0
    (fun _ => 0) = 0 := by
  rw [smallSignal_quadratic_attains_factor]; norm_num

/-- The segment bound applied to the square law at deviation `3`:
the pullback is `s ↦ (3s)^2`, its second derivative is constantly
`18 = 2 * ‖dv‖^2`, and the conclusion is the attained bound. -/
example : |smallSignalRemainder (fun v : Fin 1 → ℝ => (v 0) ^ 2) 0
    (fun _ => 3)| ≤ 2 * ‖(fun _ => 3 : Fin 1 → ℝ)‖ ^ 2 / 2 :=
  smallSignal_remainder_le_of_segment_bound _ _ _ 2
    (by fun_prop)
    (by
      have hcont : ContDiff ℝ 2 (fun s : ℝ => (s * 3) ^ 2) :=
        (contDiff_id.mul contDiff_const).pow 2
      simpa using hcont)
    (by
      intro t _
      have hg : (fun s : ℝ => (fun v : Fin 1 → ℝ => (v 0) ^ 2)
          (0 + s • (fun _ => (3 : ℝ)))) = fun s => (s * 3) ^ 2 := by
        funext s
        simp [Pi.smul_apply, smul_eq_mul]
      rw [hg]
      have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => (u * 3) ^ 2) (18 * s) s := by
        intro s
        have h9 : (fun u : ℝ => (u * 3) ^ 2) = fun u => 9 * u ^ 2 := by
          funext u
          ring
        rw [h9]
        have h := (hasDerivAt_pow 2 s).const_mul (9 : ℝ)
        convert h using 1
        ring
      have hd1 : deriv (fun u : ℝ => (u * 3) ^ 2) = fun s => 18 * s :=
        funext fun s => (hd s).deriv
      have hd2 : deriv (deriv (fun u : ℝ => (u * 3) ^ 2)) t = 18 := by
        rw [hd1]
        simpa using ((hasDerivAt_id' t).const_mul (18 : ℝ)).deriv
      have hnorm : ‖(fun _ => (3 : ℝ) : Fin 1 → ℝ)‖ = 3 := by
        rw [Pi.norm_def]
        simp
      rw [hd2, hnorm]
      norm_num)

/-- The box (Hessian) bound applied to the square law at deviation
`3`, on the box `[-4, 4]` with `M = 2`: the Hessian operator is
`u ↦ (2 * u 0) • proj 0`, of sup-norm at most `2`. -/
example : |smallSignalRemainder (fun v : Fin 1 → ℝ => (v 0) ^ 2) 0
    (fun _ => 3)| ≤ 2 * ‖(fun _ => 3 : Fin 1 → ℝ)‖ ^ 2 / 2 := by
  have hC2 : ContDiff ℝ 2 (fun v : Fin 1 → ℝ => (v 0) ^ 2) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ)
      (0 : Fin 1)).contDiff.pow 2
  have hM : ∀ y ∈ Set.Icc (fun _ => (-4 : ℝ)) (fun _ => (4 : ℝ)),
      ‖fderiv ℝ (fderiv ℝ (fun v : Fin 1 → ℝ => (v 0) ^ 2)) y‖ ≤ 2 := by
    set P : (Fin 1 → ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) (0 : Fin 1)
      with hPdef
    have hf1 : ∀ y : Fin 1 → ℝ, fderiv ℝ (fun v : Fin 1 → ℝ => (v 0) ^ 2) y
        = (2 * y 0) • P := by
      intro y
      have hmul : HasFDerivAt (fun v : Fin 1 → ℝ => (v 0) ^ 2)
          ((y 0) • P + (y 0) • P) y := by
        have hfun : (fun v : Fin 1 → ℝ => (v 0) ^ 2)
            = (fun v : Fin 1 → ℝ => v 0) * (fun v : Fin 1 → ℝ => v 0) := by
          funext v
          simp [pow_two, Pi.mul_apply]
        have hPe : (fun v : Fin 1 → ℝ => v 0) = ⇑P := by
          funext v
          simp [hPdef]
        rw [hfun, hPe]
        exact (ContinuousLinearMap.hasFDerivAt P).mul
          (ContinuousLinearMap.hasFDerivAt P)
      rw [hmul.fderiv, ← add_smul]
      congr 1
      ring
    have hder : ∀ y : Fin 1 → ℝ,
        fderiv ℝ (fderiv ℝ (fun v : Fin 1 → ℝ => (v 0) ^ 2)) y
          = ((2 : ℝ) • P).smulRight P := by
      intro y
      have hmap : HasFDerivAt (fun y' : Fin 1 → ℝ => (2 * y' 0) • P)
          (((2 : ℝ) • P).smulRight P) y := by
        have hfun2 : (fun y' : Fin 1 → ℝ => (2 * y' 0) • P)
            = ⇑(((2 : ℝ) • P).smulRight P) := by
          funext u
          simp [ContinuousLinearMap.smulRight_apply,
            ContinuousLinearMap.smul_apply, Pi.smul_apply, hPdef]
        rw [hfun2]
        exact ContinuousLinearMap.hasFDerivAt _
      have hcong : fderiv ℝ (fderiv ℝ (fun v : Fin 1 → ℝ => (v 0) ^ 2)) y
          = fderiv ℝ (fun y' : Fin 1 → ℝ => (2 * y' 0) • P) y := by
        congr 1
        exact funext hf1
      rw [hcong]
      exact hmap.fderiv
    intro y _
    rw [hder y]
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    have h1 : (((2 : ℝ) • P).smulRight P) u = (2 * u 0) • P := by
      simp [ContinuousLinearMap.smulRight_apply, hPdef]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_mul]
    have hP : ‖P‖ ≤ 1 := by
      rw [hPdef]
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro w
      simpa using norm_le_pi_norm w 0
    have hu : |(2 : ℝ)| * |u 0| ≤ 2 * ‖u‖ := by
      have h1 : |u 0| ≤ ‖u‖ := norm_le_pi_norm u 0
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      linarith
    calc |(2 : ℝ)| * |u 0| * ‖P‖ ≤ (2 * ‖u‖) * 1 :=
          mul_le_mul hu hP (norm_nonneg _)
            (mul_nonneg (by norm_num) (norm_nonneg _))
      _ = 2 * ‖u‖ := by ring
  exact smallSignal_remainder_le_of_hessian_bound _ 2 _ _ _ _ _
    isOpen_univ (Set.subset_univ _) hC2.contDiffOn hM
    (by simp [Set.mem_Icc, Pi.le_def] <;> norm_num)
    (by simp [Set.mem_Icc, Pi.le_def] <;> norm_num)

end PhyslibExtTest.Electronics.OperatingPointLinearization
