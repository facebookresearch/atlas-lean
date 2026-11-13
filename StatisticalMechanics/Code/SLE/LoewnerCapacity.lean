/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Code.SLE.LoewnerProps
import Code.SLE.CapacityProps

open Complex Set Filter Topology
open scoped NNReal

namespace StatMech.SLE












theorem tendsto_self_div_of_tendsto_const (F : ℂ → ℂ) (c : ℂ)
    (hF : Tendsto (fun z => F z - z) (cocompact ℂ) (𝓝 c)) :
    Tendsto (fun z => z / F z) (cocompact ℂ) (𝓝 1) := by
  
  have hFc : Tendsto F (cocompact ℂ) (cocompact ℂ) := by
    rw [tendsto_cocompact_iff_norm]
    have hzn : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    have hb : Tendsto (fun z => -‖F z - z‖) (cocompact ℂ) (𝓝 (-‖c‖)) := hF.norm.neg
    apply tendsto_atTop_mono (f := fun z => ‖z‖ - ‖F z - z‖)
    · intro z
      have : ‖z‖ ≤ ‖F z‖ + ‖F z - z‖ := by
        calc ‖z‖ = ‖F z - (F z - z)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖F z‖ + ‖F z - z‖ := norm_sub_le _ _
      linarith
    · have : Tendsto (fun z => ‖z‖ + - ‖F z - z‖) (cocompact ℂ) atTop := hzn.atTop_add hb
      simpa [sub_eq_add_neg] using this
  
  have hquot : Tendsto (fun z => F z / z) (cocompact ℂ) (𝓝 1) := by
    have hprod : Tendsto (fun z => (F z - z) * z⁻¹) (cocompact ℂ) (𝓝 (c * 0)) :=
      hF.mul tendsto_inv_cocompact
    rw [mul_zero] at hprod
    have h1 : Tendsto (fun z => 1 + (F z - z) * z⁻¹) (cocompact ℂ) (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℂ)) (f := cocompact ℂ)).add hprod
      simpa using this
    apply h1.congr'
    filter_upwards [eventually_ne_zero_cocompact] with z hz0
    field_simp; ring
  
  have hinv : Tendsto (fun z => (F z / z)⁻¹) (cocompact ℂ) (𝓝 (1 : ℂ)⁻¹) :=
    hquot.inv₀ (by norm_num)
  rw [inv_one] at hinv
  apply hinv.congr'
  filter_upwards [eventually_ne_zero_cocompact,
    hFc.eventually eventually_ne_zero_cocompact] with z hz hFz
  rw [inv_div]
















theorem tendsto_mul_loewnerField (W : ℝ → ℝ) (t : ℝ) (G : ℂ → ℂ)
    (hG : Tendsto (fun z => G z - z) (cocompact ℂ) (𝓝 0)) :
    Tendsto (fun z => z * loewnerField W t (G z)) (cocompact ℂ) (𝓝 (2 : ℂ)) := by
  
  have hF : Tendsto (fun z => (G z - (W t : ℂ)) - z) (cocompact ℂ) (𝓝 (-(W t : ℂ))) := by
    have heq : (fun z => (G z - (W t : ℂ)) - z) = (fun z => (G z - z) + (- (W t : ℂ))) := by
      funext z; ring
    rw [heq]
    have := hG.add_const (- (W t : ℂ))
    simpa using this
  have hratio : Tendsto (fun z => z / (G z - (W t : ℂ))) (cocompact ℂ) (𝓝 1) :=
    tendsto_self_div_of_tendsto_const (fun z => G z - (W t : ℂ)) (-(W t : ℂ)) hF
  
  have hGWc : Tendsto (fun z => G z - (W t : ℂ)) (cocompact ℂ) (cocompact ℂ) := by
    rw [tendsto_cocompact_iff_norm]
    have hzn : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    have hb : Tendsto (fun z => -‖(G z - (W t : ℂ)) - z‖) (cocompact ℂ) (𝓝 (-‖-(W t : ℂ)‖)) :=
      hF.norm.neg
    apply tendsto_atTop_mono (f := fun z => ‖z‖ - ‖(G z - (W t : ℂ)) - z‖)
    · intro z
      have : ‖z‖ ≤ ‖G z - (W t : ℂ)‖ + ‖(G z - (W t : ℂ)) - z‖ := by
        calc ‖z‖ = ‖(G z - (W t : ℂ)) - ((G z - (W t : ℂ)) - z)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖G z - (W t : ℂ)‖ + ‖(G z - (W t : ℂ)) - z‖ := norm_sub_le _ _
      linarith
    · have : Tendsto (fun z => ‖z‖ + - ‖(G z - (W t : ℂ)) - z‖) (cocompact ℂ) atTop :=
        hzn.atTop_add hb
      simpa [sub_eq_add_neg] using this
  
  have hh : Tendsto (fun z => 2 * (z / (G z - (W t : ℂ)))) (cocompact ℂ) (𝓝 ((2 : ℂ) * 1)) :=
    hratio.const_mul 2
  rw [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ne_zero_cocompact,
    hGWc.eventually eventually_ne_zero_cocompact] with z hz hGz
  simp only [loewnerField_apply]
  field_simp












theorem coeff_ode_solution {a₁ : ℝ → ℝ}
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t)
    (h0 : a₁ 0 = 0) :
    ∀ t ∈ Ici (0 : ℝ), a₁ t = 2 * t := by
  intro t ht
  have htnn : (0 : ℝ) ≤ t := ht
  rcases eq_or_lt_of_le htnn with htz | htpos
  · simp [← htz, h0]
  
  set b : ℝ → ℝ := fun u => a₁ u - 2 * u with hbdef
  have hIcc_sub : Icc (0 : ℝ) t ⊆ Ici (0 : ℝ) := fun x hx => hx.1
  have hbderiv : ∀ x ∈ Icc (0 : ℝ) t, HasDerivWithinAt b 0 (Icc (0 : ℝ) t) x := by
    intro x hx
    have hax : HasDerivWithinAt a₁ 2 (Icc (0 : ℝ) t) x := (hd x hx.1).mono hIcc_sub
    have hlin : HasDerivWithinAt (fun u : ℝ => 2 * u) 2 (Icc (0 : ℝ) t) x := by
      simpa using (hasDerivWithinAt_id x (Icc (0 : ℝ) t)).const_mul (2 : ℝ)
    have : HasDerivWithinAt (fun u => a₁ u - 2 * u) (2 - 2) (Icc (0 : ℝ) t) x := hax.sub hlin
    simpa [hbdef] using this
  have hdiff : DifferentiableOn ℝ b (Icc (0 : ℝ) t) :=
    fun x hx => (hbderiv x hx).differentiableWithinAt
  have hud : UniqueDiffOn ℝ (Icc (0 : ℝ) t) := uniqueDiffOn_Icc htpos
  have hderivW : ∀ x ∈ Ico (0 : ℝ) t, derivWithin b (Icc (0 : ℝ) t) x = 0 := fun x hx =>
    (hbderiv x (Ico_subset_Icc_self hx)).derivWithin (hud x (Ico_subset_Icc_self hx))
  have hconst := constant_of_derivWithin_zero hdiff hderivW t (right_mem_Icc.mpr htnn)
  simp only [hbdef, h0] at hconst
  linarith [hconst]







theorem hasHalfPlaneCapacity_zero_of_eq_id {g : ℝ → ℂ → ℂ} (h0 : ∀ z, g 0 z = z) :
    HasHalfPlaneCapacity (g 0) 0 := by
  have hfun : g 0 = id := funext (fun z => h0 z)
  rw [hfun]; exact hasHalfPlaneCapacity_id
























theorem loewner_halfplane_capacity_eq {g : ℝ → ℂ → ℂ} {a₁ : ℝ → ℝ}
    (hcap : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a₁ t))
    (h0 : a₁ 0 = 0)
    (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t) :
    ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (2 * t) := by
  intro t ht
  have heq : a₁ t = 2 * t := coeff_ode_solution hrate h0 t ht
  rw [← heq]; exact hcap t ht






theorem loewner_capacity_coeff_eq {a₁ : ℝ → ℝ}
    (h0 : a₁ 0 = 0)
    (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t) :
    ∀ t ∈ Ici (0 : ℝ), a₁ t = 2 * t :=
  coeff_ode_solution hrate h0





theorem loewner_capacity_unique {g : ℝ → ℂ → ℂ} {a₁ : ℝ → ℝ}
    (hcap : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a₁ t))
    (h0 : a₁ 0 = 0)
    (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) {b : ℝ} (hb : HasHalfPlaneCapacity (g t) b) :
    b = 2 * t :=
  hb.unique (loewner_halfplane_capacity_eq hcap h0 hrate t ht)

















theorem loewner_capacity_eq_of_loewnerChain (c : LoewnerChain) {a₁ : ℝ → ℝ}
    (hcap : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (c.maps t) (a₁ t))
    (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t) :
    ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (c.maps t) (2 * t) := by
  
  have hid : HasHalfPlaneCapacity (c.maps 0) 0 :=
    hasHalfPlaneCapacity_zero_of_eq_id (fun z => c.maps_zero z)
  have h0 : a₁ 0 = 0 :=
    ((hcap 0 Set.self_mem_Ici).unique hid)
  exact loewner_halfplane_capacity_eq hcap h0 hrate

end StatMech.SLE
