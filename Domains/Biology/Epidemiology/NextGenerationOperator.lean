/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Next-generation operator with a separable kernel

On a measure space, let `a`, `b`, and `S` be measurable nonnegative real functions, with `b`
essentially bounded and `S a` integrable. If the bounded real operator `K` on `L¹` acts almost
everywhere by `K φ = S a ∫ b φ` for every `φ`, its Gelfand radius is `∫ b S a`.

## References

* O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, *On the definition and the computation of
  the basic reproduction ratio R₀ in models for infectious diseases in heterogeneous populations*,
  Journal of Mathematical Biology 28 (1990), 365–382, Eq. (2.2) and Section 3.1, Eqs. (3.1)–(3.3).
* Thomas Browning, Mathlib's `Mathlib.Analysis.Normed.Algebra.GelfandRadius`, for the Gelfand radius
  API used in the proof.
-/

@[expose] public section

namespace WantedExt.Biology.Epidemiology.NextGenerationOperatorWanted

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The basic reproduction ratio `R₀`.** The per-generation growth factor of a bounded real
operator `K`, an alias for Mathlib's Gelfand radius `gelfandRadius K`: the limit of
`‖K^m‖^(1/m)` (`tendsto_gelfandRadius`), which is also `inf_{m ≥ 1} ‖K^m‖^(1/m)` and equals the
spectral radius of the complexification of `K`. It is the basic reproduction ratio `R₀ = r(K)` of
Diekmann, Heesterbeek and Metz (1990, Eq. (2.2)). -/
noncomputable abbrev generationGrowth (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) : ℝ :=
  gelfandRadius K

/-- **`R₀` for a separable kernel** (Diekmann, Heesterbeek and Metz 1990, Section 3.1,
Eqs. (3.1)–(3.3)). Let `a, b, S ≥ 0` be measurable with `b` essentially bounded and `S a`
integrable, and let `K φ = S a ∫ b φ`, the next-generation operator of the kernel
`k(ξ, η) = a(ξ) b(η)`. Then `R₀ = ∫ b S a`.

Source: Diekmann, Heesterbeek and Metz (1990), Eq. (3.3). -/
theorem generationGrowth_eq_integral_of_separable (a b S : Ω → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hS : Measurable S)
    (ha0 : ∀ ξ, 0 ≤ a ξ) (hb0 : ∀ ξ, 0 ≤ b ξ) (hS0 : ∀ ξ, 0 ≤ S ξ)
    (hbinf : MemLp b ⊤ μ) (hSa : Integrable (fun ξ => S ξ * a ξ) μ)
    (K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ)
    (hK : ∀ φ : Lp ℝ 1 μ,
      ((K φ : Lp ℝ 1 μ) : Ω → ℝ) =ᵐ[μ] fun ξ => S ξ * a ξ * ∫ η, b η * φ η ∂μ) :
    generationGrowth K = ∫ ξ, b ξ * S ξ * a ξ ∂μ := by
  let c : ℝ := ∫ ξ, b ξ * S ξ * a ξ ∂μ
  have hIntegrable : Integrable (fun ξ => b ξ * S ξ * a ξ) μ :=
    ⟨((hb.mul hS).mul ha).aestronglyMeasurable, by
      convert (hSa.mul_of_top_right hbinf).hasFiniteIntegral using 1
      funext ξ
      rw [Pi.mul_apply, mul_assoc]⟩
  have hc : 0 ≤ c := by
    rw [← integral_zero' (μ := μ) (G := ℝ)]
    exact integral_mono (integrable_zero Ω ℝ μ) hIntegrable fun ξ =>
      mul_nonneg (mul_nonneg (hb0 ξ) (hS0 ξ)) (ha0 ξ)
  have huLp : MemLp (fun ξ => S ξ * a ξ) 1 μ := memLp_one_iff_integrable.mpr hSa
  let u := huLp.toLp (fun ξ => S ξ * a ξ)
  have hu : (u : Ω → ℝ) =ᵐ[μ] fun ξ => S ξ * a ξ := huLp.coeFn_toLp
  have hK' (φ : Lp ℝ 1 μ) : K φ = (∫ ξ, b ξ * φ ξ ∂μ) • u := by
    apply Lp.ext
    filter_upwards [hK φ, Lp.coeFn_smul (∫ ξ, b ξ * φ ξ ∂μ) u, hu] with ξ hφ hsmul hξ
    rw [hφ, hsmul, Pi.smul_apply, smul_eq_mul, hξ, mul_comm]
  have hcu : ∫ ξ, b ξ * u ξ ∂μ = c := by
    apply integral_congr_ae
    filter_upwards [hu] with ξ hξ
    rw [hξ, mul_assoc]
  have heigen : K u = c • u := by rw [hK', hcu]
  have hsq : K ^ 2 = c • K := by
    rw [pow_two]
    ext1 φ
    rw [mul_apply_eq_comp, hK' φ, map_smul, heigen, smul_apply,
      hK' φ, smul_smul, smul_smul, mul_comm]
  have hr : gelfandRadius K ^ 2 = c * gelfandRadius K := by
    rw [← gelfandRadius_pow_of_ne_zero K (by decide : (2 : ℕ) ≠ 0), hsq,
      gelfandRadius_smul, Real.norm_of_nonneg hc]
  change gelfandRadius K = c
  by_cases hc0 : c = 0
  · rw [hc0, zero_mul] at hr
    rw [hc0]
    exact sq_eq_zero_iff.mp hr
  have hu0 : u ≠ 0 := by
    intro h
    apply hc0
    refine hcu.symm.trans (integral_eq_zero_of_ae ?_)
    have huz : (u : Ω → ℝ) =ᵐ[μ] 0 := h ▸ Lp.coeFn_zero ℝ 1 μ
    filter_upwards [huz] with ξ hξ
    simp [hξ]
  have hpow (n : ℕ) : (K ^ n) u = c ^ n • u := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, map_smul, heigen, smul_smul, pow_succ]
  have hlower : gelfandRadius c ≤ gelfandRadius K := by
    refine gelfandRadius_le_of_norm_pow_le 1 fun n => ?_
    have h := (K ^ n).le_opNorm u
    rw [hpow, norm_smul] at h
    rw [one_mul]
    exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hu0)
  have hc_radius : gelfandRadius c = c := by
    simpa only [smul_eq_mul, mul_one, gelfandRadius_one, Real.norm_of_nonneg hc] using
      gelfandRadius_smul c (1 : ℝ)
  rw [hc_radius] at hlower
  exact mul_right_cancel₀ ((lt_of_le_of_ne hc (Ne.symm hc0)).trans_le hlower).ne' (by
    simpa only [pow_two] using hr)

end WantedExt.Biology.Epidemiology.NextGenerationOperatorWanted
