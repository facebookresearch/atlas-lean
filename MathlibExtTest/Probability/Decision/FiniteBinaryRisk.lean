/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Decision.FiniteBinaryRisk
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite binary-risk tests

Concrete risks for deterministic and randomized decision rules on a
two-point observation space.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace MathlibExtTest.Probability.Decision

/-- Nonvacuity: always-negative deterministic rule has risk `4/3`.
Concrete instance: `𝒳 = Fin 2`, `P0 = (3/4, 1/4)`, `P1 = (1/4, 3/4)`,
`π = 1/3`, `cFP = 1`, `cFN = 4` (so always-negative pays `π·cFN = 4/3`). -/
theorem finiteBinaryRisk_det_constFalse :
    (avgRisk
      (fun θ y => if θ = y then 0
        else if θ = false then ENNReal.ofReal 1 else ENNReal.ofReal 4)
      (Kernel.boolKernel
        (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
        (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x))
      (Kernel.deterministic (fun _ => false) measurable_const : Kernel (Fin 2) Bool)
      (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true)).toReal = 4/3 := by
  rw [avgRisk_fintype, Fintype.sum_bool]
  have hinner_true :
      (∫⁻ y, (if (true : Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(((Kernel.deterministic (fun _ : Fin 2 => false) measurable_const : Kernel (Fin 2) Bool) ∘ₖ
          Kernel.boolKernel
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x)) true)) = ENNReal.ofReal 4 := by
    have hm : Measurable (fun y : Bool => if (true:Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ)) := by fun_prop
    rw [Kernel.lintegral_comp _ _ _ hm]
    simp only [Kernel.lintegral_deterministic measurable_const]
    rw [Kernel.boolKernel_true]
    simp only [ite_eq_right (show (true:Bool) ≠ false from by decide)]
    rw [lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [Fin.sum_univ_two]
    rw [ite_eq_left (show (0 : Fin 2) = 0 from rfl), ite_eq_right (show (1 : Fin 2) ≠ 0 from by decide)]
    rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1/4 by norm_num),
        ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 3/4 by norm_num)]
    have e1 : (1/4 : ℝ) * 4 = 1 := by norm_num
    have e2 : (3/4 : ℝ) * 4 = 3 := by norm_num
    rw [e1, e2, ← ENNReal.ofReal_add (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 3 by norm_num)]
    congr 1
    norm_num
  have hinner_false :
      (∫⁻ y, (if (false : Bool) = y then (0:ℝ≥0∞) else if (false:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(((Kernel.deterministic (fun _ : Fin 2 => false) measurable_const : Kernel (Fin 2) Bool) ∘ₖ
          Kernel.boolKernel
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x)) false)) = 0 := by
    have hm : Measurable (fun y : Bool => if (false:Bool) = y then (0:ℝ≥0∞) else if (false:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ)) := by fun_prop
    rw [Kernel.lintegral_comp _ _ _ hm]
    simp only [Kernel.lintegral_deterministic measurable_const]
    simp
  have hpi_true : (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true) {true} = ENNReal.ofReal (1/3 : ℝ) := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply]
    have h1 : false ∉ ({true} : Set Bool) := by simp
    have h2 : true ∈ ({true} : Set Bool) := by simp
    rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2]
    simp only [Pi.one_apply, smul_eq_mul, mul_zero, mul_one, zero_add]
  rw [hinner_true, hinner_false, hpi_true]
  simp only [zero_mul, add_zero]
  rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 4 by norm_num)]
  have e : (4:ℝ) * (1/3) = 4/3 := by norm_num
  rw [e, ENNReal.toReal_ofReal (show (0:ℝ) ≤ 4/3 by norm_num)]

/-- Nonvacuity: identity deterministic rule has risk `1/2`. -/
theorem finiteBinaryRisk_det_id :
    (avgRisk
      (fun θ y => if θ = y then 0
        else if θ = false then ENNReal.ofReal 1 else ENNReal.ofReal 4)
      (Kernel.boolKernel
        (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
        (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x))
      (Kernel.deterministic (fun x => decide (x = 1)) (by fun_prop) : Kernel (Fin 2) Bool)
      (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true)).toReal = 1/2 := by
  rw [avgRisk_fintype, Fintype.sum_bool]
  have hinner_false :
      (∫⁻ y, (if (false : Bool) = y then (0:ℝ≥0∞) else if (false:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(((Kernel.deterministic (fun x : Fin 2 => decide (x = 1)) (by fun_prop) : Kernel (Fin 2) Bool) ∘ₖ
          Kernel.boolKernel
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x)) false)) = ENNReal.ofReal (1/4 : ℝ) := by
    have hm : Measurable (fun y : Bool => if (false:Bool) = y then (0:ℝ≥0∞) else if (false:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ)) := by fun_prop
    rw [Kernel.lintegral_comp _ _ _ hm]
    simp only [Kernel.lintegral_deterministic]
    rw [Kernel.boolKernel_false]
    rw [lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [Fin.sum_univ_two]
    simp
  have hinner_true :
      (∫⁻ y, (if (true : Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(((Kernel.deterministic (fun x : Fin 2 => decide (x = 1)) (by fun_prop) : Kernel (Fin 2) Bool) ∘ₖ
          Kernel.boolKernel
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x)) true)) = ENNReal.ofReal 1 := by
    have hm : Measurable (fun y : Bool => if (true:Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ)) := by fun_prop
    rw [Kernel.lintegral_comp _ _ _ hm]
    simp only [Kernel.lintegral_deterministic]
    rw [Kernel.boolKernel_true]
    rw [lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [Fin.sum_univ_two]
    simp
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have hpi_true : (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true) {true} = ENNReal.ofReal (1/3 : ℝ) := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply]
    have h1 : false ∉ ({true} : Set Bool) := by simp
    have h2 : true ∈ ({true} : Set Bool) := by simp
    rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2]
    simp only [Pi.one_apply, smul_eq_mul, mul_zero, mul_one, zero_add]
  have hpi_false : (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true) {false} = ENNReal.ofReal (1 - 1/3 : ℝ) := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply]
    have h1 : false ∈ ({false} : Set Bool) := by simp
    have h2 : true ∉ ({false} : Set Bool) := by simp
    rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
    simp only [Pi.one_apply, smul_eq_mul, mul_one, mul_zero, add_zero]
  rw [hinner_true, hinner_false, hpi_true, hpi_false]
  rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1 by norm_num),
      ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1/4 by norm_num)]
  have t1 : (1:ℝ) * (1/3) = 1/3 := by norm_num
  have t2 : (1/4:ℝ) * (1 - 1/3) = 1/6 := by norm_num
  rw [t1, t2, ← ENNReal.ofReal_add (show (0:ℝ) ≤ 1/3 by norm_num) (show (0:ℝ) ≤ 1/6 by norm_num)]
  have t3 : (1/3:ℝ) + 1/6 = 1/2 := by norm_num
  rw [t3, ENNReal.toReal_ofReal (show (0:ℝ) ≤ 1/2 by norm_num)]

/-- Nonvacuity: swapped deterministic rule has risk `3/2`. -/
theorem finiteBinaryRisk_det_swap :
    (avgRisk
      (fun θ y => if θ = y then 0
        else if θ = false then ENNReal.ofReal 1 else ENNReal.ofReal 4)
      (Kernel.boolKernel
        (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
        (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x))
      (Kernel.deterministic (fun x => decide (x = 0)) (by fun_prop) : Kernel (Fin 2) Bool)
      (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true)).toReal = 3/2 := by
  rw [avgRisk_fintype, Fintype.sum_bool]
  have hinner_false :
      (∫⁻ y, (if (false : Bool) = y then (0:ℝ≥0∞) else if (false:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(((Kernel.deterministic (fun x : Fin 2 => decide (x = 0)) (by fun_prop) : Kernel (Fin 2) Bool) ∘ₖ
          Kernel.boolKernel
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x)) false)) = ENNReal.ofReal (3/4 : ℝ) := by
    have hm : Measurable (fun y : Bool => if (false:Bool) = y then (0:ℝ≥0∞) else if (false:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ)) := by fun_prop
    rw [Kernel.lintegral_comp _ _ _ hm]
    simp only [Kernel.lintegral_deterministic]
    rw [Kernel.boolKernel_false]
    rw [lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [Fin.sum_univ_two]
    simp
  have hinner_true :
      (∫⁻ y, (if (true : Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(((Kernel.deterministic (fun x : Fin 2 => decide (x = 0)) (by fun_prop) : Kernel (Fin 2) Bool) ∘ₖ
          Kernel.boolKernel
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x)) true)) = ENNReal.ofReal 3 := by
    have hm : Measurable (fun y : Bool => if (true:Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ)) := by fun_prop
    rw [Kernel.lintegral_comp _ _ _ hm]
    simp only [Kernel.lintegral_deterministic]
    rw [Kernel.boolKernel_true]
    rw [lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [Fin.sum_univ_two]
    simp
    rw [ENNReal.ofReal_div_of_pos (show (0:ℝ) < 4 by norm_num)]
    simp only [ENNReal.ofReal_ofNat]
    exact ENNReal.div_mul_cancel (by simp) (by simp)
  have hpi_true : (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true) {true} = ENNReal.ofReal (1/3 : ℝ) := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply]
    have h1 : false ∉ ({true} : Set Bool) := by simp
    have h2 : true ∈ ({true} : Set Bool) := by simp
    rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2]
    simp only [Pi.one_apply, smul_eq_mul, mul_zero, mul_one, zero_add]
  have hpi_false : (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true) {false} = ENNReal.ofReal (1 - 1/3 : ℝ) := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply]
    have h1 : false ∈ ({false} : Set Bool) := by simp
    have h2 : true ∉ ({false} : Set Bool) := by simp
    rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
    simp only [Pi.one_apply, smul_eq_mul, mul_one, mul_zero, add_zero]
  rw [hinner_true, hinner_false, hpi_true, hpi_false]
  rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 3 by norm_num),
      ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 3/4 by norm_num)]
  have t1 : (3:ℝ) * (1/3) = 1 := by norm_num
  have t2 : (3/4:ℝ) * (1 - 1/3) = 1/2 := by norm_num
  rw [t1, t2, ← ENNReal.ofReal_add (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)]
  have t3 : (1:ℝ) + 1/2 = 3/2 := by norm_num
  rw [t3, ENNReal.toReal_ofReal (show (0:ℝ) ≤ 3/2 by norm_num)]

/-- Nonvacuity: always-positive deterministic rule has risk `2/3`
(`(1-π)·cFP = 2/3`). -/
theorem finiteBinaryRisk_det_constTrue :
    (avgRisk
      (fun θ y => if θ = y then 0
        else if θ = false then ENNReal.ofReal 1 else ENNReal.ofReal 4)
      (Kernel.boolKernel
        (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
        (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x))
      (Kernel.deterministic (fun _ => true) measurable_const : Kernel (Fin 2) Bool)
      (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true)).toReal = 2/3 := by
  rw [avgRisk_fintype, Fintype.sum_bool]
  have hinner_false :
      (∫⁻ y, (if (false : Bool) = y then (0:ℝ≥0∞) else if (false:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(((Kernel.deterministic (fun _ : Fin 2 => true) measurable_const : Kernel (Fin 2) Bool) ∘ₖ
          Kernel.boolKernel
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x)) false)) = ENNReal.ofReal 1 := by
    have hm : Measurable (fun y : Bool => if (false:Bool) = y then (0:ℝ≥0∞) else if (false:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ)) := by fun_prop
    rw [Kernel.lintegral_comp _ _ _ hm]
    simp only [Kernel.lintegral_deterministic measurable_const]
    rw [Kernel.boolKernel_false]
    simp only [ite_eq_right (show (false:Bool) ≠ true from by decide), ite_true]
    rw [lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [Fin.sum_univ_two]
    rw [ite_eq_left (show (0 : Fin 2) = 0 from rfl), ite_eq_right (show (1 : Fin 2) ≠ 0 from by decide)]
    rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 3/4 by norm_num),
        ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1/4 by norm_num)]
    have e1 : (3/4 : ℝ) * 1 = 3/4 := by norm_num
    have e2 : (1/4 : ℝ) * 1 = 1/4 := by norm_num
    rw [e1, e2, ← ENNReal.ofReal_add (show (0:ℝ) ≤ 3/4 by norm_num) (show (0:ℝ) ≤ 1/4 by norm_num)]
    congr 1
    norm_num
  have hinner_true :
      (∫⁻ y, (if (true : Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(((Kernel.deterministic (fun _ : Fin 2 => true) measurable_const : Kernel (Fin 2) Bool) ∘ₖ
          Kernel.boolKernel
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x)) true)) = 0 := by
    have hm : Measurable (fun y : Bool => if (true:Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ)) := by fun_prop
    rw [Kernel.lintegral_comp _ _ _ hm]
    simp only [Kernel.lintegral_deterministic measurable_const]
    simp
  have hpi_false : (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true) {false} = ENNReal.ofReal (1 - 1/3 : ℝ) := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply]
    have h1 : false ∈ ({false} : Set Bool) := by simp
    have h2 : true ∉ ({false} : Set Bool) := by simp
    rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
    simp only [Pi.one_apply, smul_eq_mul, mul_one, mul_zero, add_zero]
  rw [hinner_false, hinner_true, hpi_false]
  simp only [zero_mul, zero_add]
  rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1 by norm_num)]
  have e : (1:ℝ) * (1 - 1/3) = 2/3 := by norm_num
  rw [e, ENNReal.toReal_ofReal (show (0:ℝ) ≤ 2/3 by norm_num)]

/-- Nonvacuity: the constantly-`1/2` randomized kernel has risk `1`,
strictly between the identity (`1/2`) and swapped (`3/2`) deterministic risks. -/
theorem finiteBinaryRisk_randomized_half :
    (avgRisk
      (fun θ y => if θ = y then 0
        else if θ = false then ENNReal.ofReal 1 else ENNReal.ofReal 4)
      (Kernel.boolKernel
        (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
        (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x))
      (Kernel.ofFunOfCountable (fun _ : Fin 2 =>
        ENNReal.ofReal (1 - 1/2 : ℝ) • Measure.dirac false
          + ENNReal.ofReal (1/2 : ℝ) • Measure.dirac true))
      (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true)).toReal = 1 := by
  rw [avgRisk_fintype, Fintype.sum_bool]
  have hker_false : ∀ x : Fin 2,
      (∫⁻ y, (if (false : Bool) = y then (0:ℝ≥0∞) else if True then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(((Kernel.ofFunOfCountable (fun _ : Fin 2 =>
          ENNReal.ofReal (1 - 1/2 : ℝ) • Measure.dirac false
            + ENNReal.ofReal (1/2 : ℝ) • Measure.dirac true) : Kernel (Fin 2) Bool)) x)) = ENNReal.ofReal (1/2 : ℝ) := by
    intro x
    show (∫⁻ y, (if (false : Bool) = y then (0:ℝ≥0∞) else if True then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(ENNReal.ofReal (1 - 1/2 : ℝ) • Measure.dirac false
            + ENNReal.ofReal (1/2 : ℝ) • Measure.dirac true)) = _
    rw [lintegral_add_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    simp only [ite_true, ite_eq_right (show (false:Bool) ≠ true from by decide), mul_zero, zero_add, ENNReal.ofReal_one, mul_one]
  have hker_true : ∀ x : Fin 2,
      (∫⁻ y, (if (true : Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(((Kernel.ofFunOfCountable (fun _ : Fin 2 =>
          ENNReal.ofReal (1 - 1/2 : ℝ) • Measure.dirac false
            + ENNReal.ofReal (1/2 : ℝ) • Measure.dirac true) : Kernel (Fin 2) Bool)) x)) = ENNReal.ofReal 2 := by
    intro x
    show (∫⁻ y, (if (true : Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(ENNReal.ofReal (1 - 1/2 : ℝ) • Measure.dirac false
            + ENNReal.ofReal (1/2 : ℝ) • Measure.dirac true)) = _
    rw [lintegral_add_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    simp only [ite_eq_right (show (true:Bool) ≠ false from by decide), ite_true, mul_zero, add_zero]
    rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1 - 1/2 by norm_num)]
    congr 1
    norm_num
  have hinner_false :
      (∫⁻ y, (if (false : Bool) = y then (0:ℝ≥0∞) else if (false:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(((Kernel.ofFunOfCountable (fun _ : Fin 2 =>
          ENNReal.ofReal (1 - 1/2 : ℝ) • Measure.dirac false
            + ENNReal.ofReal (1/2 : ℝ) • Measure.dirac true) : Kernel (Fin 2) Bool) ∘ₖ
          Kernel.boolKernel
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x)) false)) = ENNReal.ofReal (1/2 : ℝ) := by
    have hm : Measurable (fun y : Bool => if (false:Bool) = y then (0:ℝ≥0∞) else if (false:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ)) := by fun_prop
    rw [Kernel.lintegral_comp _ _ _ hm]
    simp only [hker_false]
    rw [Kernel.boolKernel_false]
    rw [lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [Fin.sum_univ_two]
    rw [ite_eq_left (show (0 : Fin 2) = 0 from rfl), ite_eq_right (show (1 : Fin 2) ≠ 0 from by decide)]
    rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 3/4 by norm_num),
        ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1/4 by norm_num)]
    have e1 : (3/4 : ℝ) * (1/2) = 3/8 := by norm_num
    have e2 : (1/4 : ℝ) * (1/2) = 1/8 := by norm_num
    rw [e1, e2, ← ENNReal.ofReal_add (show (0:ℝ) ≤ 3/8 by norm_num) (show (0:ℝ) ≤ 1/8 by norm_num)]
    congr 1
    norm_num
  have hinner_true :
      (∫⁻ y, (if (true : Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ))
        ∂(((Kernel.ofFunOfCountable (fun _ : Fin 2 =>
          ENNReal.ofReal (1 - 1/2 : ℝ) • Measure.dirac false
            + ENNReal.ofReal (1/2 : ℝ) • Measure.dirac true) : Kernel (Fin 2) Bool) ∘ₖ
          Kernel.boolKernel
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (3/4 : ℝ) else 1/4) • Measure.dirac x)
            (∑ x : Fin 2, ENNReal.ofReal (if x = 0 then (1/4 : ℝ) else 3/4) • Measure.dirac x)) true)) = ENNReal.ofReal 2 := by
    have hm : Measurable (fun y : Bool => if (true:Bool) = y then (0:ℝ≥0∞) else if (true:Bool) = false then ENNReal.ofReal (1:ℝ) else ENNReal.ofReal (4:ℝ)) := by fun_prop
    rw [Kernel.lintegral_comp _ _ _ hm]
    simp only [hker_true]
    rw [Kernel.boolKernel_true]
    rw [lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [Fin.sum_univ_two]
    rw [ite_eq_left (show (0 : Fin 2) = 0 from rfl), ite_eq_right (show (1 : Fin 2) ≠ 0 from by decide)]
    rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1/4 by norm_num),
        ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 3/4 by norm_num)]
    have e1 : (1/4 : ℝ) * 2 = 1/2 := by norm_num
    have e2 : (3/4 : ℝ) * 2 = 3/2 := by norm_num
    rw [e1, e2, ← ENNReal.ofReal_add (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 3/2 by norm_num)]
    congr 1
    norm_num
  have hpi_true : (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true) {true} = ENNReal.ofReal (1/3 : ℝ) := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply]
    have h1 : false ∉ ({true} : Set Bool) := by simp
    have h2 : true ∈ ({true} : Set Bool) := by simp
    rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2]
    simp only [Pi.one_apply, smul_eq_mul, mul_zero, mul_one, zero_add]
  have hpi_false : (ENNReal.ofReal (1 - 1/3 : ℝ) • Measure.dirac false
        + ENNReal.ofReal (1/3 : ℝ) • Measure.dirac true) {false} = ENNReal.ofReal (1 - 1/3 : ℝ) := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply]
    have h1 : false ∈ ({false} : Set Bool) := by simp
    have h2 : true ∉ ({false} : Set Bool) := by simp
    rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
    simp only [Pi.one_apply, smul_eq_mul, mul_one, mul_zero, add_zero]
  rw [hinner_true, hinner_false, hpi_true, hpi_false]
  rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num),
      ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1/2 by norm_num)]
  have t1 : (2:ℝ) * (1/3) = 2/3 := by norm_num
  have t2 : (1/2:ℝ) * (1 - 1/3) = 1/3 := by norm_num
  rw [t1, t2, ← ENNReal.ofReal_add (show (0:ℝ) ≤ 2/3 by norm_num) (show (0:ℝ) ≤ 1/3 by norm_num)]
  have t3 : (2/3:ℝ) + 1/3 = 1 := by norm_num
  rw [t3, ENNReal.toReal_ofReal (show (0:ℝ) ≤ 1 by norm_num)]

/-- The `1/2`-kernel above is genuinely randomized: at observation `0` it
assigns mass `1/2 ∉ {0, 1}` to `{true}`, so it is not a Dirac (deterministic)
kernel. -/
theorem finiteBinaryRisk_randomized_half_not_deterministic :
    (Kernel.ofFunOfCountable (fun _ : Fin 2 =>
        ENNReal.ofReal (1 - 1/2 : ℝ) • Measure.dirac false
          + ENNReal.ofReal (1/2 : ℝ) • Measure.dirac true) : Kernel (Fin 2) Bool) 0 {true}
      = 1/2
    ∧ (Kernel.ofFunOfCountable (fun _ : Fin 2 =>
        ENNReal.ofReal (1 - 1/2 : ℝ) • Measure.dirac false
          + ENNReal.ofReal (1/2 : ℝ) • Measure.dirac true) : Kernel (Fin 2) Bool) 0 {true} ≠ 0
    ∧ (Kernel.ofFunOfCountable (fun _ : Fin 2 =>
        ENNReal.ofReal (1 - 1/2 : ℝ) • Measure.dirac false
          + ENNReal.ofReal (1/2 : ℝ) • Measure.dirac true) : Kernel (Fin 2) Bool) 0 {true} ≠ 1 := by
  have hval : (Kernel.ofFunOfCountable (fun _ : Fin 2 =>
        ENNReal.ofReal (1 - 1/2 : ℝ) • Measure.dirac false
          + ENNReal.ofReal (1/2 : ℝ) • Measure.dirac true) : Kernel (Fin 2) Bool) 0 {true}
      = ENNReal.ofReal (1/2 : ℝ) := by
    show (ENNReal.ofReal (1 - 1/2 : ℝ) • Measure.dirac false
            + ENNReal.ofReal (1/2 : ℝ) • Measure.dirac true) {true} = _
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply]
    have h1 : false ∉ ({true} : Set Bool) := by simp
    have h2 : true ∈ ({true} : Set Bool) := by simp
    rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2]
    simp only [Pi.one_apply, smul_eq_mul, mul_zero, mul_one, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [hval, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  · rw [hval]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)
  · rw [hval, ne_eq, ENNReal.ofReal_eq_one]
    norm_num

end MathlibExtTest.Probability.Decision
