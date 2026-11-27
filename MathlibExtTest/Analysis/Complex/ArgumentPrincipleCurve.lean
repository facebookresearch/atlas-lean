/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Meromorphic.NormalForm
import MathlibExt.Analysis.Complex.ArgumentPrincipleCurve
import MathlibExtTest.Analysis.Complex.ResidueTheorem

set_option autoImplicit false

open Complex Filter Metric Set Topology
open scoped Real

/-! The unit circle `circlePath 0 1` satisfies every hypothesis on the curve; the four facts
(`range_circlePath_zero_one`, `inside_range_circlePath_zero_one`, `injOn_circlePath_zero_one`,
`windingNumber_circlePath_zero_one`) are proved in the residue theorem tests. -/

/-! The argument principle for `f z = z² (z - 3) / (z - 1/2)` on the unit circle. Inside the
circle `f` has a double zero at `0` and a simple pole at `1/2`; its simple zero at `3` lies outside.
So `N - P = 2 - 1 = 1`. -/

theorem meromorphicOrderAt_sub_const' (a w : ℂ) :
    meromorphicOrderAt (fun z : ℂ => z - a) w = if w = a then 1 else 0 := by
  split_ifs with h
  · subst h
    exact meromorphicOrderAt_id_sub_const
  · exact (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (AnalyticAt.meromorphicNFAt
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - a) w))).2 (sub_ne_zero.2 h)

theorem meromorphicOrderAt_rational (w : ℂ) :
    meromorphicOrderAt (fun z : ℂ => z ^ 2 * (z - 3) * (z - 1 / 2)⁻¹) w =
      (((if w = 0 then 2 else 0) + (if w = 3 then 1 else 0) - (if w = 1 / 2 then 1 else 0) :
        ℤ) : WithTop ℤ) := by
  have h0 : meromorphicOrderAt (fun z : ℂ => z) w = if w = 0 then 1 else 0 := by
    simpa using meromorphicOrderAt_sub_const' 0 w
  rw [fun_meromorphicOrderAt_mul (by fun_prop) (by fun_prop),
    fun_meromorphicOrderAt_mul (by fun_prop) (by fun_prop),
    fun_meromorphicOrderAt_pow (f := fun z : ℂ => z) (by fun_prop),
    fun_meromorphicOrderAt_inv, h0, meromorphicOrderAt_sub_const' 3 w,
    meromorphicOrderAt_sub_const' (1 / 2) w]
  split_ifs <;> simp_all

theorem divisor_rational (w : ℂ) :
    MeromorphicOn.divisor (fun z : ℂ => z ^ 2 * (z - 3) * (z - 1 / 2)⁻¹) univ w =
      (if w = 0 then 2 else 0) + (if w = 3 then 1 else 0) - (if w = 1 / 2 then 1 else 0) := by
  rw [MeromorphicOn.divisor_apply (fun z _ => by fun_prop) (mem_univ w),
    meromorphicOrderAt_rational, WithTop.untop₀_coe]

example : (2 * π * I)⁻¹ * ∫ᶜ z in circlePath 0 1,
    logDeriv (fun z : ℂ => z ^ 2 * (z - 3) * (z - 1 / 2)⁻¹) z • ContinuousLinearMap.id ℂ ℂ =
      1 := by
  have hγf : ∀ z ∈ range (circlePath 0 1),
      meromorphicOrderAt (fun z : ℂ => z ^ 2 * (z - 3) * (z - 1 / 2)⁻¹) z = 0 := by
    intro z hz
    rw [range_circlePath_zero_one, mem_sphere_zero_iff_norm] at hz
    have h0 : z ≠ 0 := by rintro rfl; norm_num at hz
    have h3 : z ≠ 3 := by rintro rfl; norm_num at hz
    have h12 : z ≠ 2⁻¹ := by rintro rfl; norm_num at hz
    rw [meromorphicOrderAt_rational]
    simp [h0, h3, h12]
  obtain ⟨-, h⟩ := MeromorphicOn.argument_principle isOpen_univ (fun z _ => by fun_prop)
    (isPiecewiseC1_circlePath 0 1) injOn_circlePath_zero_one windingNumber_circlePath_zero_one
    (subset_univ _) (subset_univ _) hγf
  rw [h, inside_range_circlePath_zero_one]
  -- Inside the unit circle the zero divisor is `2 • [0]` and the pole divisor is `[1/2]`.
  have hpos : ∑ᶠ z ∈ ball (0 : ℂ) 1,
      (MeromorphicOn.divisor (fun z : ℂ => z ^ 2 * (z - 3) * (z - 1 / 2)⁻¹) univ)⁺ z = 2 := by
    rw [finsum_mem_inter_support_eq _ _ {0} ?_, finsum_mem_singleton]
    · norm_num [divisor_rational]
    · ext z
      simp only [mem_inter_iff, Function.mem_support, mem_singleton_iff, mem_ball_zero_iff,
        Function.locallyFinsuppWithin.posPart_apply, divisor_rational]
      refine ⟨fun ⟨hz, hd⟩ => ⟨by_contra fun h0 => hd ?_, hd⟩, fun ⟨h0, hd⟩ => ⟨by simp [h0], hd⟩⟩
      have h3 : z ≠ 3 := by rintro rfl; norm_num at hz
      split_ifs <;> simp_all
  have hneg : ∑ᶠ z ∈ ball (0 : ℂ) 1,
      (MeromorphicOn.divisor (fun z : ℂ => z ^ 2 * (z - 3) * (z - 1 / 2)⁻¹) univ)⁻ z = 1 := by
    rw [finsum_mem_inter_support_eq _ _ {1 / 2} ?_, finsum_mem_singleton]
    · norm_num [divisor_rational]
    · ext z
      simp only [mem_inter_iff, Function.mem_support, mem_singleton_iff, mem_ball_zero_iff,
        Function.locallyFinsuppWithin.negPart_apply, divisor_rational]
      refine ⟨fun ⟨hz, hd⟩ => ⟨by_contra fun h12 => hd ?_, hd⟩,
        fun ⟨h12, hd⟩ => ⟨by norm_num [h12], hd⟩⟩
      have h3 : z ≠ 3 := by rintro rfl; norm_num at hz
      split_ifs <;> simp_all
  rw [hpos, hneg]
  norm_num

#print axioms MeromorphicOn.argument_principle
