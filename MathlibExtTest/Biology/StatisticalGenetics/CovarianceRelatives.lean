/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.CovarianceRelatives

import Mathlib.Tactic.NormNum

@[expose] public section

open Finset MathlibExt.Biology.StatisticalGenetics.CovarianceRelatives

namespace MathlibExtTest.Biology.StatisticalGenetics.CovarianceRelatives

/-! ### Two alleles at frequency `1/2` -/

/-- Non-vacuity: an additive locus (genotypic value = number of `true` alleles). -/
noncomputable def additive : LocusModel Bool where
  p _ := 1 / 2
  p_nonneg _ := by norm_num
  sum_p := by norm_num
  g a b := (if a then 1 else 0) + (if b then 1 else 0)
  g_symm a b := add_comm _ _

/-- Complete dominance: value `1` if at least one `true` allele. -/
noncomputable def dominant : LocusModel Bool where
  p _ := 1 / 2
  p_nonneg _ := by norm_num
  sum_p := by norm_num
  g a b := if a || b then 1 else 0
  g_symm a b := by rw [Bool.or_comm]

/-- The additive locus has mean `1` and additive variance `1/2`. -/
example : additive.mean = 1 ∧ additive.varA = 1 / 2 := by
  constructor <;> norm_num [LocusModel.mean, LocusModel.varA, LocusModel.alpha, additive]

/-- The additive locus has no dominance variance. -/
example : additive.varD = 0 := by
  norm_num [LocusModel.varD, LocusModel.delta, LocusModel.alpha, LocusModel.mean, additive]

/-- Complete dominance: `V_A = 1/8`, `V_D = 1/16`, and `V_G = 3/16 = V_A + V_D`. -/
example : dominant.varA = 1 / 8 ∧ dominant.varD = 1 / 16 ∧ dominant.varG = 3 / 16 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [LocusModel.varA, LocusModel.varD, LocusModel.varG, LocusModel.delta,
      LocusModel.alpha, LocusModel.mean, dominant]

/-- Fisher's decomposition on the dominant locus. -/
example : dominant.varG = dominant.varA + dominant.varD := dominant.varG_eq

/-- Full sibs (`k = (1/4, 1/2, 1/4)`) at the dominant locus: `Cov = V_A/2 + V_D/4 = 1/16 + 1/64`.
-/
example : dominant.relProd (1 / 4) (1 / 2) (1 / 4) - dominant.mean ^ 2 =
    (1 / 2 / 2 + 1 / 4) * dominant.varA + 1 / 4 * dominant.varD :=
  dominant.relCov_eq (by norm_num)

/-- Parent–offspring (`k₁ = 1`): `Cov = V_A / 2`. -/
example : dominant.relProd 0 1 0 - dominant.mean ^ 2 = (1 / 2 + 0) * dominant.varA +
    0 * dominant.varD :=
  dominant.relCov_eq (by norm_num)

/-- One-locus phantom heritability: Falconer's estimator exceeds `V_A` by `(3/2) V_D`. -/
example (C : ℝ) : 2 * ((dominant.relProd 0 0 1 - dominant.mean ^ 2 + C) -
    (dominant.relProd (1 / 4) (1 / 2) (1 / 4) - dominant.mean ^ 2 + C)) =
    dominant.varA + 3 / 2 * dominant.varD :=
  dominant.falconer_eq_of_locus C

/-! ### Cockerham components with additive-by-additive epistasis -/

/-- Non-vacuity: `V_A = 1`, `V_AA = 1`, nothing else (order `2`). -/
def epistatic : CockerhamComponents where
  n := 2
  V i j := if (i, j) = (1, 0) ∨ (i, j) = (2, 0) then 1 else 0
  V_nonneg i j := by split_ifs <;> norm_num
  V_zero_zero := by simp
  V_supported i j h := by
    rcases h with hi | hj <;> split_ifs with h1 <;>
      (first
        | (rcases h1 with h1 | h1 <;>
            (obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1; omega))
        | rfl)

/-- `V_A = 1` while Falconer's estimator is `1 + 2 (1 - 1/4) = 5/2`. -/
example (C : ℝ) : epistatic.varA = 1 ∧ epistatic.falconer C = 5 / 2 := by
  constructor
  · simp [CockerhamComponents.varA, epistatic]
  · simp [CockerhamComponents.falconer, CockerhamComponents.cov, epistatic,
      Finset.sum_range_succ]
    norm_num

/-- The inequality is strict here: the estimator is not `V_A`. -/
example (C : ℝ) : epistatic.falconer C ≠ epistatic.varA := by
  rw [Ne, epistatic.falconer_eq_varA_iff]
  intro h
  have := h 2 (by simp [epistatic]) 0 (by simp [epistatic]) (by simp)
  simp [epistatic] at this

/-- The phantom inequality on the correlation scale with `V_P = 4`. -/
example (C : ℝ) : epistatic.varA / 4 ≤
    2 * ((epistatic.cov 1 1 + C) / 4 - (epistatic.cov (1 / 2) (1 / 4) + C) / 4) :=
  epistatic.narrow_le_falconerHeritability C (by norm_num)

end MathlibExtTest.Biology.StatisticalGenetics.CovarianceRelatives
