/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Gronwall's inequality in integral form

Mathlib's `Mathlib.Analysis.ODE.Gronwall` bounds functions through their (Dini) derivatives. This
file gives the integral form for real functions that are only integrable, not continuous.

## Main results

* `le_mul_exp_of_le_add_integral`: if a nonnegative integrable `u` satisfies
  `u t ≤ a + K ∫₀ᵗ u` on `[0, T]` with `K ≥ 0`, then `u t ≤ a e^{K t}` there.
-/

@[expose] public section

open MeasureTheory Real Set Filter
open scoped Topology

namespace MathlibExt.Analysis.ODE

/-- **Gronwall's inequality in integral form.** If a nonnegative integrable `u` satisfies
`u(t) ≤ a + K ∫₀ᵗ u` on `[0, T]` with `K ≥ 0`, then `u(t) ≤ a e^{K t}` there. No continuity of
`u` is needed: the primitive `v = ∫₀ᵗ u` is continuous with right upper Dini derivative at most
`a + K v`, and Mathlib's Dini-derivative Gronwall bound applies to `v`. -/
theorem le_mul_exp_of_le_add_integral {u : ℝ → ℝ} {a K T : ℝ} (hK : 0 ≤ K)
    (hu : IntegrableOn u (Icc 0 T)) (hu0 : ∀ t ∈ Icc 0 T, 0 ≤ u t)
    (h : ∀ t ∈ Icc 0 T, u t ≤ a + K * ∫ s in (0 : ℝ)..t, u s) :
    ∀ t ∈ Icc 0 T, u t ≤ a * exp (K * t) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  set v : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, u s with hv
  have hii : ∀ x ∈ Icc 0 T, ∀ z ∈ Icc 0 T, IntervalIntegrable u volume x z := fun x hx z hz =>
    (hu.mono_set (uIcc_subset_Icc hx hz)).intervalIntegrable
  have hvc : ContinuousOn v (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
      (f := u) (by rwa [uIcc_of_le hT])
    rwa [uIcc_of_le hT] at this
  have hvmono : ∀ x ∈ Icc 0 T, ∀ z ∈ Icc 0 T, x ≤ z → v x ≤ v z := by
    intro x hx z hz hxz
    have hsplit : v z - v x = ∫ s in x..z, u s :=
      intervalIntegral.integral_interval_sub_left (hii 0 ⟨le_rfl, hT⟩ z hz)
        (hii 0 ⟨le_rfl, hT⟩ x hx)
    have : 0 ≤ ∫ s in x..z, u s :=
      intervalIntegral.integral_nonneg hxz fun s hs => hu0 s ⟨hx.1.trans hs.1, hs.2.trans hz.2⟩
    linarith
  have hvle : ∀ x ∈ Icc 0 T, v x ≤ gronwallBound 0 K a (x - 0) := by
    refine le_gronwallBound_of_liminf_deriv_right_le (f' := fun x => K * v x + a) hvc ?_
      (by simp [hv]) (fun x _ => le_rfl)
    intro x hx r hr
    have hxT : x < T := hx.2
    have hsub : Ioo x T ⊆ Icc 0 T := fun z hz => ⟨hx.1.trans hz.1.le, hz.2.le⟩
    have htend : Tendsto v (𝓝[>] x) (𝓝 (v x)) := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT hxT]
      exact (hvc x ⟨hx.1, hxT.le⟩).mono hsub
    have hlim : Tendsto (fun z => K * v z + a) (𝓝[>] x) (𝓝 (K * v x + a)) :=
      (htend.const_mul K).add_const a
    refine Eventually.frequently ?_
    filter_upwards [hlim.eventually (gt_mem_nhds hr), Ioo_mem_nhdsGT hxT] with z hz hzI
    have hxz : x < z := hzI.1
    have hzI' : z ∈ Icc 0 T := hsub hzI
    have hxI : x ∈ Icc 0 T := ⟨hx.1, hxT.le⟩
    have hint : v z - v x ≤ (z - x) * (K * v z + a) := by
      have hsplit : v z - v x = ∫ s in x..z, u s :=
        intervalIntegral.integral_interval_sub_left (hii 0 ⟨le_rfl, hT⟩ z hzI')
          (hii 0 ⟨le_rfl, hT⟩ x hxI)
      rw [hsplit]
      have := intervalIntegral.integral_mono_on hxz.le (hii x hxI z hzI')
        (intervalIntegrable_const (c := K * v z + a)) fun s hs => by
          have hsI : s ∈ Icc 0 T := ⟨hx.1.trans hs.1, hs.2.trans hzI'.2⟩
          have := h s hsI
          have := hvmono s hsI z hzI' hs.2
          nlinarith
      rwa [intervalIntegral.integral_const, smul_eq_mul] at this
    have hpos : 0 < z - x := sub_pos.2 hxz
    calc (z - x)⁻¹ * (v z - v x) ≤ (z - x)⁻¹ * ((z - x) * (K * v z + a)) :=
          mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hpos.le)
      _ = K * v z + a := by field_simp
      _ < r := hz
  have hut := h t ht
  have hvt := hvle t ht
  rw [sub_zero] at hvt
  rcases hK.eq_or_lt with hK0 | hKpos
  · subst hK0
    simpa using hut
  · rw [gronwallBound_of_K_ne_0 hKpos.ne'] at hvt
    have : K * v t ≤ a * (exp (K * t) - 1) := by
      have := mul_le_mul_of_nonneg_left hvt hK
      simp only [zero_mul, zero_add] at this
      calc K * v t ≤ K * (a / K * (exp (K * t) - 1)) := this
        _ = a * (exp (K * t) - 1) := by field_simp
    change u t ≤ a * exp (K * t)
    have : u t ≤ a + K * v t := hut
    nlinarith

end MathlibExt.Analysis.ODE
