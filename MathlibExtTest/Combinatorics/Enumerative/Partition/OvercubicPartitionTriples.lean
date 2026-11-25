/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.OvercubicPartitionTriples
import Mathlib.RingTheory.PowerSeries.Expand

open PowerSeries MetaMathlibExt
open scoped PowerSeries.WithPiTopology

-- At size one there are three choices of component and two choices of overlining.
example : overcubicTripleCount 1 = 6 := by
  have h₁ : coeff 1 (qEulerProduct 1) = -1 := by
    have hp : 1 = pentagonal 1 := by norm_num [pentagonal_def]
    rw [qEulerProduct_one, hp, coeff_pentagonalSeries_pentagonal]
    rfl
  have h (k : ℕ) (hk : 1 < k) : coeff 1 (qEulerProduct k) = 0 := by
    have hk₀ : k ≠ 0 := by omega
    have hc : Continuous (expand k hk₀ : ℤ⟦X⟧ → ℤ⟦X⟧) := by
      rw [continuous_iff_continuousAt]
      intro f
      rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
      intro n
      by_cases hd : k ∣ n
      · simpa [coeff_expand, hd] using (WithPiTopology.continuous_coeff ℤ (n / k)).tendsto f
      · simp [coeff_expand, hd]
    have hp := (WithPiTopology.hasProd_one_sub_X_pow ℤ).map (expand k hk₀) hc
    have he : qEulerProduct k = expand k hk₀ (pentagonalSeries ℤ) := by
      simpa [qEulerProduct, Function.comp_def, pow_mul] using hp.tprod_eq
    rw [he, coeff_expand_of_not_dvd _ _ _ (by simpa using hk.ne')]
  have hg := congrArg (coeff 1) overcubicTripleCount_generatingFunction
  simp only [coeff_one_mul, coeff_one_pow, map_mul, map_pow, h₁, h 2 (by decide),
    h 4 (by decide), constantCoeff_qEulerProduct (by decide : 1 ≤ 1),
    constantCoeff_qEulerProduct (by decide : 1 ≤ 2),
    constantCoeff_qEulerProduct (by decide : 1 ≤ 4), constantCoeff_mk, coeff_mk, overcubicTripleCount_zero] at hg
  norm_num at hg
  omega

-- The comparison at the lower endpoint relates two positive indices.
example : overcubicTripleCount 32 ≡ overcubicTripleCount 16 [ZMOD 4] := by
  simpa using (overcubicTripleCount_congruences_sixteen_mul_args 0 0).2.2.2.2.1

-- Doubling the spacing of the last progression keeps its offset fixed.
example : (4 : ℤ) ∣ overcubicTripleCount 704 := by
  exact Int.modEq_zero_iff_dvd.mp (overcubicTripleCount_congruences_sixteen_mul_args 1 1).2.2.2.2.2
