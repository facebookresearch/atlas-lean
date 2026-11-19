/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Classical.Dioecy
public import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.Classical.Dioecy
open scoped ENNReal

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.Dioecy


/-- All females are `AA`. -/
noncomputable def femalesAA : PMF (Bool × Bool) := PMF.pure (true, true)

/-- All males are `aa`. -/
noncomputable def malesaa : PMF (Bool × Bool) := PMF.pure (false, false)

theorem gamete_femalesAA_true : MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete femalesAA true = 1 := by
  rw [MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete_apply]
  simp [femalesAA, PMF.pure_apply, ENNReal.inv_two_add_inv_two]

theorem gamete_malesaa_true : MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete malesaa true = 0 := by
  rw [MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete_apply]
  simp [malesaa, PMF.pure_apply]

/-- Every offspring of `AA` females and `aa` males is the ordered heterozygote
`(A, a)`. -/
example : offspring femalesAA malesaa (true, false) = 1 := by
  rw [offspring_apply, gamete_femalesAA_true]
  have hfalse : MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete malesaa false = 1 := by
    rw [MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete_apply]
    simp [malesaa, PMF.pure_apply, ENNReal.inv_two_add_inv_two]
  rw [hfalse, mul_one]

/-- Their offspring have allele frequency `1/2` for `A`. -/
example : MathlibExt.Biology.PopulationGenetics.HardyWeinberg.gamete (offspring femalesAA malesaa) true = 2⁻¹ := by
  rw [gamete_offspring, gamete_femalesAA_true, gamete_malesaa_true]
  simp

/-- Equal parental laws give the ordinary Hardy–Weinberg offspring law. -/
example (G : PMF (Bool × Bool)) : offspring G G = MathlibExt.Biology.PopulationGenetics.HardyWeinberg.offspring G :=
  offspring_self G

/-- Scalar boundary checks: `p_f = 1/2`, `p_m = 1/4` gives excess `1/32`, and
equal sex frequencies give no excess. -/
example :
    (1 / 2 : ℝ) * (1 - 1 / 4) + (1 / 4) * (1 - 1 / 2) -
        2 * ((1 / 2 + 1 / 4) / 2) * (1 - (1 / 2 + 1 / 4) / 2) = 1 / 32 ∧
      ¬0 < (2 / 5 : ℝ) * (1 - 2 / 5) + (2 / 5) * (1 - 2 / 5) -
        2 * ((2 / 5 + 2 / 5) / 2) * (1 - (2 / 5 + 2 / 5) / 2) := by
  constructor
  · rw [heterozygote_excess_eq]
    norm_num
  · rw [heterozygote_excess_pos_iff]
    norm_num

end MathlibExtTest.Biology.PopulationGenetics.Classical.Dioecy
