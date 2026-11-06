/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.CauchyIntegral
import MathlibExt.Analysis.Complex.ResidueTheorem

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

-- The inside of the unit circle is the open unit disc: a point outside the closed disc lies on a
-- ray that avoids the circle and is unbounded, and the component of a point of the open disc
-- stays in the disc.
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

-- Positive orientation: the unit circle winds once around every point inside it.
theorem windingNumber_circlePath_zero_one :
    ∀ z ∈ (range (circlePath 0 1)).inside, windingNumber (circlePath 0 1) z = 1 := fun _ hz =>
  windingNumber_circlePath_of_mem_ball (inside_range_circlePath_zero_one ▸ hz)

/-! The residue theorem for `f z = z⁻¹ + (z - 2)⁻¹` on the unit circle: of its two simple poles
only `0` lies inside, with residue `1`. -/

theorem residue_inv_add_inv_sub_two :
    residue (fun z : ℂ => z⁻¹ + (z - 2)⁻¹) 0 = 1 := by
  have h2 : DifferentiableOn ℂ (fun z : ℂ => (z - 2)⁻¹) {2}ᶜ :=
    (differentiableOn_id.sub_const 2).fun_inv fun z hz => sub_ne_zero.2 hz
  have hdisc : closedBall (0 : ℂ) 1 ⊆ {2}ᶜ := by
    rintro z hz rfl
    norm_num [mem_closedBall_zero_iff] at hz
  have hf : DifferentiableOn ℂ (fun z : ℂ => z⁻¹ + (z - 2)⁻¹) (closedBall 0 1 \ {0}) :=
    fun z hz => ((differentiableAt_inv hz.2).add (h2.differentiableAt
      (isOpen_compl_singleton.mem_nhds (hdisc hz.1)))).differentiableWithinAt
  have hi1 : CircleIntegrable (fun z : ℂ => z⁻¹) 0 1 :=
    (continuousOn_inv₀.mono fun z hz h0 => by
      rw [mem_singleton_iff.1 h0] at hz
      simp at hz).circleIntegrable'
  have hi2 : CircleIntegrable (fun z : ℂ => (z - 2)⁻¹) 0 1 :=
    (h2.continuousOn.mono ((sphere_subset_closedBall.trans (by simp)).trans hdisc)
      ).circleIntegrable'
  have hinv : ∮ z in C(0, 1), z⁻¹ = 2 * π * I := by
    simpa using circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self (one_pos (α := ℝ)))
      (c := (0 : ℂ))
  rw [residue_eq_circleIntegral hf one_pos subset_rfl, circleIntegral.integral_add hi1 hi2, hinv,
    (h2.diffContOnCl_ball hdisc).circleIntegral_eq_zero zero_le_one, add_zero, smul_eq_mul,
    inv_mul_cancel₀ two_pi_I_ne_zero]

example : (2 * π * I)⁻¹ *
    ∫ᶜ z in circlePath 0 1, (z⁻¹ + (z - 2)⁻¹) • ContinuousLinearMap.id ℂ ℂ = 1 := by
  have hS : ∀ z ∈ (univ : Set ℂ), ∀ᶠ w in 𝓝[≠] z, w ∉ ({0, 2} : Set ℂ) := fun z _ => by
    have h : (({0, 2} : Set ℂ) \ {z})ᶜ ∈ 𝓝 z :=
      ((toFinite _).subset sdiff_subset).isClosed.compl_mem_nhds fun h => h.2 rfl
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with w hw hwz hwS
    exact hw ⟨hwS, hwz⟩
  have hf : DifferentiableOn ℂ (fun z : ℂ => z⁻¹ + (z - 2)⁻¹) (univ \ {0, 2}) := by
    rintro z ⟨-, hz⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
    have hd : DifferentiableAt ℂ (fun w : ℂ => w - 2) z := by fun_prop
    exact ((differentiableAt_inv hz.1).add (hd.inv (sub_ne_zero.2 hz.2))).differentiableWithinAt
  have hSγ : ∀ a ∈ ({0, 2} : Set ℂ), a ∉ range (circlePath 0 1) := by
    rw [range_circlePath_zero_one]
    rintro a (rfl | rfl) <;> norm_num [mem_sphere_zero_iff_norm]
  have hins : ({0, 2} : Set ℂ) ∩ (range (circlePath 0 1)).inside = {0} := by
    rw [inside_range_circlePath_zero_one]
    ext z
    constructor
    · rintro ⟨rfl | rfl, hz⟩
      · rfl
      · norm_num [mem_ball_zero_iff] at hz
    · rintro rfl
      exact ⟨Or.inl rfl, mem_ball_self one_pos⟩
  obtain ⟨-, h⟩ := two_pi_I_inv_mul_curveIntegral_eq_finsum_residue isOpen_univ isConnected_univ
    (subset_univ _) hS hf (isPiecewiseC1_circlePath 0 1) injOn_circlePath_zero_one
    windingNumber_circlePath_zero_one (subset_univ _) (subset_univ _) hSγ
  rw [h, hins, finsum_mem_singleton, residue_inv_add_inv_sub_two]

/-! Cauchy's theorem for the cycle `C(0, 3) - C(0, 1/4) - C(1, 1/4)`, homologous to zero in
`ℂ \ {0, 1}`. -/

example (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f {0, 1}ᶜ) :
    ∫ᶜ z in circlePath 0 3, f z • ContinuousLinearMap.id ℂ ℂ =
      (∮ z in C(0, 1 / 4), f z) + ∮ z in C(1, 1 / 4), f z := by
  have h01 : (0 : ℂ) ≠ 1 := zero_ne_one
  have hΩ : IsOpen ({0, 1}ᶜ : Set ℂ) := (toFinite _).isClosed.isOpen_compl
  have hγΩ : range (circlePath 0 3) ⊆ {0, 1}ᶜ := fun z hz => by
    have h := range_circlePath_subset 0 3 hz
    rw [mem_sphere_zero_iff_norm] at h
    rintro (rfl | rfl) <;> norm_num at h
  have hF : ∀ a ∈ ({0, 1} : Finset ℂ), sphere a |(fun _ => (1 / 4 : ℝ)) a| ⊆ {0, 1}ᶜ := by
    intro a ha z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [mem_sphere, dist_eq_norm] at hz
    rcases ha with rfl | rfl <;> rintro (rfl | rfl) <;> norm_num at hz
  have hhom : ∀ z ∉ ({0, 1}ᶜ : Set ℂ), windingNumber (circlePath 0 3) z =
      ∑ a ∈ ({0, 1} : Finset ℂ), windingNumber (circlePath a ((fun _ => (1 / 4 : ℝ)) a)) z := by
    intro z hz
    rw [notMem_compl_iff] at hz
    rw [Finset.sum_pair h01]
    rcases hz with rfl | rfl
    · rw [windingNumber_circlePath_of_mem_ball (by norm_num [mem_ball_zero_iff]),
        windingNumber_circlePath_of_mem_ball (by norm_num [mem_ball_zero_iff]),
        windingNumber_circlePath_of_notMem_closedBall (by norm_num)
          (by norm_num [mem_closedBall, dist_eq_norm]), add_zero]
    · rw [windingNumber_circlePath_of_mem_ball (by norm_num [mem_ball_zero_iff]),
        windingNumber_circlePath_of_notMem_closedBall (by norm_num)
          (by norm_num [mem_closedBall_zero_iff]),
        windingNumber_circlePath_of_mem_ball (by norm_num [mem_ball]), zero_add]
  have key := curveIntegral_eq_sum_circleIntegral hΩ (isPiecewiseC1_circlePath 0 3) hγΩ hF hhom hf
  rwa [Finset.sum_pair h01] at key

#print axioms Complex.curveIntegral_eq_sum_circleIntegral
#print axioms Complex.two_pi_I_inv_mul_curveIntegral_eq_finsum_residue_of_windingNumber_eq_one
#print axioms Complex.two_pi_I_inv_mul_curveIntegral_eq_finsum_residue
