/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Complex L¹ factorization by two L² functions

On any measure space, each complex `L¹` class factors as `f=g conj(h)` for two classes `g,h∈L²`.
The product is the pointwise product interpreted in the canonical `Lp ℂ 1 μ` carrier.

No finiteness, sigma-finiteness or nonzero-measure hypothesis is required.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal ComplexConjugate MeasureTheory

namespace MathlibExt.MeasureTheory.Function

noncomputable section

universe u

variable {X : Type u} [MeasurableSpace X] {mu : Measure X}

/-- **Factorization of a complex L¹ class by two L² classes.** Let `X` be a measurable space
and `μ` any measure. For every `f∈Lp ℂ 1 μ`, there exist `g,h∈Lp ℂ 2 μ` with `g*conj(h)=f`
as L¹ classes, the product being the pointwise `Lp` multiplication. No assumption on the
measure is required. -/
theorem exists_l2_mul_star_eq (f : Lp ℂ 1 mu) :
    ∃ g h : Lp ℂ 2 mu, (g • star h : Lp ℂ 1 mu) = f := by
  let r : X → ℝ := fun x ↦ Real.sqrt ‖f x‖
  let g₀ : X → ℂ := fun x ↦ f x / (r x : ℂ)
  let h₀ : X → ℂ := fun x ↦ (r x : ℂ)
  have hg₀meas : AEStronglyMeasurable g₀ mu := by
    dsimp only [g₀, r]
    have hfmeas : AEMeasurable (fun x ↦ f x) mu := (Lp.aestronglyMeasurable f).aemeasurable
    have hrmeas : AEMeasurable (fun x ↦ (Real.sqrt ‖f x‖ : ℂ)) mu :=
      hfmeas.norm.sqrt.complex_ofReal
    exact (hfmeas.div hrmeas).aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hh₀meas : AEStronglyMeasurable h₀ mu := by
    dsimp only [h₀, r]
    fun_prop
  have hg₀norm (x : X) : ‖g₀ x‖ ^ 2 = ‖f x‖ := by
    dsimp only [g₀, r]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.div_sqrt,
      Real.sq_sqrt (norm_nonneg _)]
  have hh₀norm (x : X) : ‖h₀ x‖ ^ 2 = ‖f x‖ := by
    dsimp only [h₀, r]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (norm_nonneg _)]
  have hfint : Integrable (fun x ↦ ‖f x‖) mu :=
    (memLp_one_iff_integrable.mp (Lp.memLp f)).norm
  have hg₀mem : MemLp g₀ 2 mu := by
    rw [memLp_two_iff_integrable_sq_norm hg₀meas]
    simpa only [hg₀norm] using hfint
  have hh₀mem : MemLp h₀ 2 mu := by
    rw [memLp_two_iff_integrable_sq_norm hh₀meas]
    simpa only [hh₀norm] using hfint
  let g : Lp ℂ 2 mu := hg₀mem.toLp g₀
  let h : Lp ℂ 2 mu := hh₀mem.toLp h₀
  refine ⟨g, h, ?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := 1) g (star h), Lp.coeFn_star h,
    hg₀mem.coeFn_toLp, hh₀mem.coeFn_toLp] with x hmul hstar hg hh
  have hg' : g x = g₀ x := by simpa only [g] using hg
  have hh' : h x = h₀ x := by simpa only [h] using hh
  rw [hmul, Pi.smul_apply', hstar, Pi.star_apply, hg', hh']
  change g₀ x * star (h₀ x) = f x
  by_cases hfx : f x = 0
  · simp [g₀, h₀, r, hfx]
  · have hr : r x ≠ 0 := by
      dsimp only [r]
      exact (Real.sqrt_pos.2 (norm_pos_iff.mpr hfx)).ne'
    dsimp only [g₀, h₀]
    rw [Complex.star_def, Complex.conj_ofReal, div_mul_cancel₀]
    exact_mod_cast hr

end

end MathlibExt.MeasureTheory.Function
