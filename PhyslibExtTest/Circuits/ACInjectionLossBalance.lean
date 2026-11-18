/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.ACInjectionLossBalance
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Circuits.ACInjectionLossBalance

namespace PhyslibExtTest.Circuits.ACInjectionLossBalance

/-- One node, one branch, resistive admittances: the total supplied
real power is `27`, from branch loss `18` and shunt loss `9`. -/
example :
    (∑ v : Fin 1, (nodeComplexPower 1 1 (Matrix.of fun _ _ => (1 : ℝ)) (fun _ => (3 : ℂ))
      (fun _ => (2 : ℂ)) (fun _ => (1 : ℂ)) v).re) = 27 := by
  rw [total_realPower_eq_branch_add_shunt_losses]
  norm_num [branchDrop, Complex.normSq_apply]

/-- The same fixture through the complex balance. -/
example :
    (∑ v : Fin 1, nodeComplexPower 1 1 (Matrix.of fun _ _ => (1 : ℝ)) (fun _ => (3 : ℂ))
      (fun _ => (2 : ℂ)) (fun _ => (1 : ℂ)) v) = 27 := by
  rw [total_complexPower_eq_branch_add_shunt]
  simp only [branchDrop, Finset.sum_fin_eq_sum_range, Finset.sum_range_one,
    Matrix.of_apply]
  norm_num [Complex.normSq_apply, Complex.ext_iff]

/-- Purely reactive admittances give zero total real power. -/
example :
    (∑ v : Fin 1, (nodeComplexPower 1 1 (Matrix.of fun _ _ => (1 : ℝ)) (fun _ => (3 : ℂ))
      (fun _ => Complex.I) (fun _ => Complex.I) v).re) = 0 :=
  total_realPower_eq_zero_of_purely_reactive 1 1 (Matrix.of fun _ _ => (1 : ℝ))
    (fun _ => (3 : ℂ)) (fun _ => Complex.I) (fun _ => Complex.I)
    (fun _ => by simp) (fun _ => by simp)

/-- Per-unit recovery at a positive real base. -/
example : perUnitComplexPower (27 : ℂ) (9 : ℝ) * ((9 : ℝ) : ℂ) = 27 :=
  perUnitComplexPower_mul_base_eq 27 9 (by norm_num)

/-- The direct-base per-unit power agrees with the existing per-unit power
on a three-phase power base. -/
example (S : ℂ) :
    perUnitComplexPower S (PhyslibExt.Circuits.PerUnitBases.threePhasePowerBase 2 4) =
      PhyslibExt.Circuits.PerUnitBases.powerPerUnit 2 4 S :=
  perUnitComplexPower_threePhasePowerBase S 2 4

end PhyslibExtTest.Circuits.ACInjectionLossBalance
