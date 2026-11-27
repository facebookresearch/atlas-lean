/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.PowerSeries.Expand
import MathlibExt.Combinatorics.Enumerative.Partition.OddDesignatedSummands

open MetaMathlibExt PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt.oddDesignatedSummandsCount_odd_args_mod_four

-- Only f₁ contributes to the linear term of the Euler quotient.
private lemma linear_coeff_zero {k : ℕ} (hk : 1 < k) : coeff 1 (qEulerProduct k) = 0 := by
  have hk' : k ≠ 0 := by omega
  have hc : Continuous (expand k hk' : ℤ⟦X⟧ → ℤ⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro f
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    by_cases hd : k ∣ n
    · simpa [coeff_expand, hd] using (WithPiTopology.continuous_coeff ℤ (n / k)).tendsto f
    · simp [coeff_expand, hd]
  have h := (WithPiTopology.hasProd_one_sub_X_pow ℤ).map (expand k hk') hc
  have he : qEulerProduct k = expand k hk' (pentagonalSeries ℤ) := by
    simpa [qEulerProduct, Function.comp_def, pow_mul] using h.tprod_eq
  rw [he, coeff_expand_of_not_dvd _ _ _ (by simpa using hk.ne')]

-- The two initial counts are one, including the first odd index outside the progressions.
example : oddDesignatedSummandsCount 0 = 1 ∧ oddDesignatedSummandsCount 1 = 1 := by
  refine ⟨oddDesignatedSummandsCount_zero, ?_⟩
  have h1 : coeff 1 (qEulerProduct 1) = -1 := by
    rw [qEulerProduct_one, show 1 = pentagonal 1 by norm_num [pentagonal_def],
      coeff_pentagonalSeries_pentagonal]
    simp
  have h := congrArg (coeff 1) oddDesignatedSummandsCount_generatingFunction
  simp (disch := decide) [coeff_one_mul, coeff_one_pow, constantCoeff_qEulerProduct,
    linear_coeff_zero, h1, constantCoeff_mk, oddDesignatedSummandsCount_zero] at h
  omega

-- Each of these three indices lies on just one of the progressions.
example : (4 : ℤ) ∣ oddDesignatedSummandsCount 7 ∧ (4 : ℤ) ∣ oddDesignatedSummandsCount 9 ∧
    (4 : ℤ) ∣ oddDesignatedSummandsCount 5 :=
  ⟨Int.modEq_zero_iff_dvd.mp (oddDesignatedSummandsCount_odd_args_mod_four 1).1,
    Int.modEq_zero_iff_dvd.mp (oddDesignatedSummandsCount_odd_args_mod_four 1).2.1,
    Int.modEq_zero_iff_dvd.mp (oddDesignatedSummandsCount_odd_args_mod_four 0).2.2⟩

end MetaMathlibExt.oddDesignatedSummandsCount_odd_args_mod_four
