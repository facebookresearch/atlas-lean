/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OperatorTheory.MulByIdentityBoundedOnL2UnitInterval
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Tests for `MathlibExt.Analysis.OperatorTheory.MulByIdentityBoundedOnL2UnitInterval` -/

namespace MathlibExtTest.MulByIdentityBoundedOnL2UnitInterval

open MeasureTheory
open MathlibExt.Analysis.OperatorTheory.MulByIdentityBoundedOnL2UnitIntervalWanted

-- Test section: the conclusion determines the operator. Two continuous linear maps on
-- `L²([0, 1])` that both multiply by `t` almost everywhere are equal.
example (T S : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hT : ∀ f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
      (T f : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] fun t => t * f t)
    (hS : ∀ f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
      (S f : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] fun t => t * f t) :
    T = S := by
  ext1 f
  exact Lp.ext ((hT f).trans (hS f).symm)

-- Test section: the operator has norm at most `1`, since `|t| ≤ 1` for `t ∈ [0, 1]`.
example : ∃ T : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
    (∀ f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
      (T f : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] fun t => t * f t) ∧ ‖T‖ ≤ 1 := by
  obtain ⟨T, hT⟩ := exists_continuousLinearMap_mul_id_L2_Icc
  refine ⟨T, hT, T.opNorm_le_bound zero_le_one fun f => ?_⟩
  rw [one_mul]
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [hT f, ae_restrict_mem measurableSet_Icc] with t ht hmem
  rw [ht, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hmem.1], hmem.2⟩

-- Test section: the operator is symmetric for the inner product `⟪f, g⟫ = ∫ f g` of `L²([0, 1])`.
example (T : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hT : ∀ f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
      (T f : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] fun t => t * f t)
    (f g : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    inner ℝ (T f) g = inner ℝ f (T g) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hT f, hT g] with t hf hg
  simp only [hf, hg, RCLike.inner_apply, conj_trivial]
  ring

-- Test section: the operator is not zero. It sends the constant function `1` to the class of
-- `t ↦ t`, which does not vanish almost everywhere on `[0, 1]`.
example (T : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hT : ∀ f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
      (T f : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] fun t => t * f t) :
    T ≠ 0 := by
  intro h0
  -- `T 1 = 0` would make `t = 0` for almost every `t ∈ [0, 1]`.
  have hzero : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), t = 0 := by
    filter_upwards [hT (Lp.const 2 _ 1), Lp.coeFn_const (p := 2)
        (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (c := (1 : ℝ)),
      Lp.coeFn_zero ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))] with t hTt hct h0t
    rw [h0, zero_apply, h0t, hct] at hTt
    simpa using hTt.symm
  -- But `t ≠ 0` on `(0, 1]`, a subset of `[0, 1]` of measure `1`.
  rw [ae_iff, Measure.restrict_apply' measurableSet_Icc] at hzero
  have hsub : Set.Ioc (0 : ℝ) 1 ⊆ {t : ℝ | ¬t = 0} ∩ Set.Icc 0 1 :=
    fun t ht => ⟨ht.1.ne', Set.Ioc_subset_Icc_self ht⟩
  have := measure_mono (μ := volume) hsub
  rw [hzero, Real.volume_Ioc] at this
  norm_num at this

end MathlibExtTest.MulByIdentityBoundedOnL2UnitInterval
