/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Complex.Loewner.LoewnerProps
public import MathlibExt.Analysis.Complex.Loewner.CapacityProps

/-!
# Half-plane capacity of a Loewner chain: `hcap(g_t) = 2t` from the rate equation

For the chordal Loewner flow `∂_t g_t(z) = 2 / (g_t(z) - W_t)` one expects `g_t(z) = z + 2t/z +
o(1/z)`, i.e. `hcap(K_t) = 2t`. The heuristic is that the coefficient `a₁(t)` of `1/z` satisfies
`a₁'(t) = lim z · 2/(g_t(z) - W_t) = 2` (`tendsto_mul_loewnerField`). This file proves the
calculus part: if `g_t` has half-plane capacity `a₁(t)` for every `t ≥ 0`, `a₁(0) = 0` and
`a₁' = 2` on `[0, ∞)`, then `a₁(t) = 2t` (`coeff_ode_solution`), hence `hcap(g_t) = 2t`
(`loewner_halfplane_capacity_eq`, the form `HasCapacityRate g 2` of `LoewnerProps`).

The two hypotheses that carry the analytic content, existence of the expansion
(`HasHalfPlaneCapacity (g t) (a₁ t)`) and the rate `a₁' = 2`, are **assumed**. Deriving them from
the Loewner equation (exchanging `∂_t` with the expansion at infinity) is not done here.

## Main results

* `tendsto_self_div_of_tendsto_const`: if `F z - z → c` at infinity then `z / F z → 1`.
* `tendsto_mul_loewnerField`: if `G z - z → 0` then `z · 2/(G z - W_t) → 2`.
* `coeff_ode_solution`: `a₁(0) = 0`, `a₁' = 2` on `[0, ∞)` imply `a₁(t) = 2t`.
* `loewner_halfplane_capacity_eq`, `loewner_capacity_eq_of_loewnerChain`: `hcap(g_t) = 2t`
  under the capacity and rate hypotheses.

## References

* G. F. Lawler, *Conformally Invariant Processes in the Plane*, Mathematical Surveys and Monographs
  114, Amer. Math. Soc., 2005, Chapter 4.
-/

@[expose] public section

open Complex Set Filter Topology
open scoped NNReal

namespace StatMech.SLE

/-- If `F z - z → c` at infinity then `z / F z → 1`. Generalizes `tendsto_self_div_cocompact`
(the case `c = 0`). -/
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

/-- If `G z - z → 0` at infinity, then `z · loewnerField W t (G z) = 2z/(G z - W_t) → 2`: the
heuristic rate `d/dt hcap = 2` of the Loewner flow. -/
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

/-- A function with derivative `2` on `[0, ∞)` and value `0` at `0` is `t ↦ 2t`. -/
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

/-- If `g 0` is the identity then it has half-plane capacity `0`. -/
theorem hasHalfPlaneCapacity_zero_of_eq_id {g : ℝ → ℂ → ℂ} (h0 : ∀ z, g 0 z = z) :
    HasHalfPlaneCapacity (g 0) 0 := by
  have hfun : g 0 = id := funext (fun z => h0 z)
  rw [hfun]; exact hasHalfPlaneCapacity_id

/-- `hcap(g_t) = 2t` (i.e. `HasCapacityRate g 2`), **assuming** `g_t` has half-plane capacity
`a₁(t)` for `t ≥ 0`, `a₁(0) = 0` and `a₁' = 2`. -/
theorem loewner_halfplane_capacity_eq {g : ℝ → ℂ → ℂ} {a₁ : ℝ → ℝ}
    (hcap : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a₁ t))
    (h0 : a₁ 0 = 0)
    (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t) :
    ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (2 * t) := by
  intro t ht
  have heq : a₁ t = 2 * t := coeff_ode_solution hrate h0 t ht
  rw [← heq]; exact hcap t ht

/-- Under the hypotheses of `loewner_halfplane_capacity_eq`, any half-plane capacity of `g_t` is
`2t`. -/
theorem loewner_capacity_unique {g : ℝ → ℂ → ℂ} {a₁ : ℝ → ℝ}
    (hcap : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a₁ t))
    (h0 : a₁ 0 = 0)
    (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) {b : ℝ} (hb : HasHalfPlaneCapacity (g t) b) :
    b = 2 * t :=
  hb.unique (loewner_halfplane_capacity_eq hcap h0 hrate t ht)

/-- For a Loewner chain, `hcap(g_t) = 2t`, **assuming** `g_t` has half-plane capacity `a₁(t)` with
`a₁' = 2`; `a₁(0) = 0` follows from `g_0 = id`. -/
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
