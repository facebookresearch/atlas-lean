/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

@[expose] public section

open Filter
open scoped ENNReal

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Powers of an element with spectral radius below 1 are summable,
via the Gelfand formula. -/
theorem summable_of_spectralRadius_lt_one {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (a : A)
    (h : spectralRadius ℂ a < 1) :
    Summable (fun k => a ^ k) := by
  have hfin : spectralRadius ℂ a ≠ ∞ := ne_top_of_lt (lt_trans h ENNReal.one_lt_top)
  have hcoe : ENNReal.ofReal (spectralRadius ℂ a).toReal = spectralRadius ℂ a :=
    ENNReal.ofReal_toReal hfin
  have hs1 : (spectralRadius ℂ a).toReal < 1 := by
    have h' : ENNReal.ofReal (spectralRadius ℂ a).toReal < 1 := by
      rw [hcoe]
      exact h
    rw [← ENNReal.ofReal_one] at h'
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mp h'
  obtain ⟨r, hsr, hr1⟩ := exists_between hs1
  have hrpos : 0 < r := lt_of_le_of_lt ENNReal.toReal_nonneg hsr
  have hr0nn : 0 ≤ r := le_of_lt hrpos
  have hρr : spectralRadius ℂ a < ENNReal.ofReal r := by
    rw [← hcoe]
    exact (ENNReal.ofReal_lt_ofReal_iff hrpos).mpr hsr
  have hev :=
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a).eventually_lt_const hρr
  have hev2 := hev.and (Filter.eventually_ge_atTop 1)
  refine Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one hr0nn hr1) ?_
  filter_upwards [hev2] with k ⟨hk, hk1⟩
  change ‖a ^ k‖ ≤ r ^ k
  have h2 : ‖a ^ k‖ ^ (1 / (k : ℝ)) < r :=
    (ENNReal.ofReal_lt_ofReal_iff hrpos).mp hk
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk1
  have h3 := Real.rpow_lt_rpow (Real.rpow_nonneg (norm_nonneg _) (1 / (k : ℝ))) h2
    (Nat.cast_pos.mpr hk0)
  have hLHS : (‖a ^ k‖ ^ (1 / (k : ℝ))) ^ ((k : ℕ) : ℝ) = ‖a ^ k‖ := by
    rw [← Real.rpow_mul (norm_nonneg _),
      one_div_mul_cancel (Nat.cast_ne_zero.mpr (ne_of_gt hk0)), Real.rpow_one]
  rw [hLHS, Real.rpow_natCast] at h3
  exact le_of_lt h3

end
end
public section
