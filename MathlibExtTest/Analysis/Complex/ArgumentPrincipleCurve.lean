/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Meromorphic.NormalForm
import MathlibExt.Analysis.Complex.ArgumentPrincipleCurve

set_option autoImplicit false

open Complex Filter Metric Set Topology
open scoped Real

/-! The counterclockwise unit circle `circlePath 0 1` satisfies every hypothesis on the curve. -/

theorem range_circlePath_zero_one : range (circlePath 0 1) = sphere (0 : ℂ) 1 := by
  refine subset_antisymm (by simpa using range_circlePath_subset (0 : ℂ) 1) fun w hw => ?_
  rw [← abs_one, ← image_circleMap_Ioc] at hw
  obtain ⟨θ, hθ, rfl⟩ := hw
  have h2π : (0 : ℝ) < 2 * π := Real.two_pi_pos
  refine ⟨⟨θ / (2 * π), div_nonneg hθ.1.le h2π.le, (div_le_one h2π).2 hθ.2⟩, ?_⟩
  change circleMap 0 1 (2 * π * (θ / (2 * π))) = circleMap 0 1 θ
  rw [mul_div_cancel₀ θ h2π.ne']

-- The inside of the unit circle is the open unit disc (as in the residue theorem tests).
theorem inside_range_circlePath_zero_one :
    (range (circlePath 0 1)).inside = ball (0 : ℂ) 1 := by
  rw [range_circlePath_zero_one]
  ext z
  refine ⟨fun ⟨hzs, hzb⟩ => ?_, fun hz => ?_⟩
  · rw [mem_ball_zero_iff]
    by_contra! hz
    have hz1 : 1 < ‖z‖ := lt_of_le_of_ne hz fun h => hzs (mem_sphere_zero_iff_norm.2 h.symm)
    have hsub : (fun t : ℝ => (t : ℂ) * z) '' Ici 1 ⊆ (sphere 0 1)ᶜ := by
      rintro _ ⟨t, ht, rfl⟩ h
      rw [mem_sphere_zero_iff_norm, norm_mul, norm_real,
        Real.norm_of_nonneg (zero_le_one.trans ht)] at h
      nlinarith [mem_Ici.1 ht]
    have hray : IsPreconnected ((fun t : ℝ => (t : ℂ) * z) '' Ici 1) :=
      isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * z).continuousOn
    obtain ⟨C, hC⟩ := (hzb.subset (hray.subset_connectedComponentIn
      ⟨1, mem_Ici.2 le_rfl, by simp⟩ hsub)).exists_norm_le
    have h := hC _ ⟨max C 1, mem_Ici.2 (le_max_right C 1), rfl⟩
    rw [norm_mul, norm_real, Real.norm_of_nonneg (zero_le_one.trans (le_max_right C 1))] at h
    nlinarith [le_max_left C 1, le_max_right C 1]
  · have hzs : z ∉ sphere (0 : ℂ) 1 := fun h => by
      rw [mem_sphere_zero_iff_norm] at h
      rw [mem_ball_zero_iff, h] at hz
      exact lt_irrefl 1 hz
    refine mem_inside.2 ⟨hzs, (isBounded_ball (x := (0 : ℂ)) (r := 1)).subset ?_⟩
    have hsub : (sphere (0 : ℂ) 1)ᶜ ⊆ ball 0 1 ∪ (closedBall 0 1)ᶜ := by
      intro w hw
      rw [mem_compl_iff, mem_sphere_zero_iff_norm] at hw
      rcases lt_or_gt_of_ne hw with h | h
      · exact Or.inl (mem_ball_zero_iff.2 h)
      · exact Or.inr fun h' => (mem_closedBall_zero_iff.1 h').not_gt h
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union isOpen_ball
      isClosed_closedBall.isOpen_compl (disjoint_compl_right_iff_subset.2 ball_subset_closedBall)
      ((connectedComponentIn_subset _ _).trans hsub) ⟨z, mem_connectedComponentIn hzs, hz⟩

theorem injOn_circlePath_zero_one : InjOn (circlePath 0 1) (Iio 1) := by
  have h2π : (0 : ℝ) < 2 * π := Real.two_pi_pos
  have hmem : ∀ u : unitInterval, u ∈ Iio 1 → 2 * π * (u : ℝ) ∈ Ico 0 (2 * π) := fun u hu =>
    ⟨mul_nonneg h2π.le u.2.1, by
      have : (u : ℝ) < 1 := hu
      nlinarith⟩
  intro s hs t ht hst
  exact Subtype.ext (mul_left_cancel₀ h2π.ne' (injOn_circleMap_of_abs_sub_le' one_ne_zero
    (by rw [sub_zero]) (hmem s hs) (hmem t ht) hst))

theorem windingNumber_circlePath_zero_one :
    ∀ z ∈ (range (circlePath 0 1)).inside, windingNumber (circlePath 0 1) z = 1 := fun _ hz =>
  windingNumber_circlePath_of_mem_ball (inside_range_circlePath_zero_one ▸ hz)

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
