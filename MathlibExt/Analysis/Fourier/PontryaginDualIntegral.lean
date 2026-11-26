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

public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Fourier integral with the inverse continuous character

For a monoid `G` with topology and measurable structure and a measure `μ`, define `F_μ(f)(χ)=∫
conj(χ(g)) f(g) dμ(g)`. The integral is totalized for arbitrary functions and has bound
`|F_μ(f)(χ)|≤∫ |f| dμ`.

Almost-everywhere equality and complex scalar multiplication preserve this integral. With Borel
measurable structure, the kernel is integrable exactly when `f` is integrable, and addition is
preserved for integrable functions. No group, countability or Haar condition is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace PontryaginDual

noncomputable section

universe uG

variable {G : Type uG} [Monoid G] [TopologicalSpace G] [MeasurableSpace G]

/-- **Fourier integral at an inverse continuous character.** Let `G` be a monoid with a
topology and measurable structure, `μ` any measure and `χ : PontryaginDual G` a continuous
circle-valued character. `fourierIntegral μ f χ=∫ χ(g)⁻¹ • f(g) dμ(g)` for any function `f
: G → ℂ`, with the circle action embedded in complex scalars. -/
def fourierIntegral (μ : Measure G) (f : G → ℂ) (χ : PontryaginDual G) : ℂ :=
  ∫ g, (χ g)⁻¹ • f g ∂μ

/-- **Conjugate-character scalar formula of the Fourier integral.** Let `G` be a monoid with a
topology and measurable structure, `μ` any measure and `χ : PontryaginDual G` a continuous
circle-valued character. for `f : G → ℂ`, `fourierIntegral μ f χ=∫ conj(χ(g)) f(g) dμ(g)`. -/
theorem fourierIntegral_apply (μ : Measure G) (f : G → ℂ) (χ : PontryaginDual G) :
    fourierIntegral μ f χ = ∫ g, (starRingEnd ℂ) ((χ g : Circle) : ℂ) * f g ∂μ := by
  simp only [fourierIntegral, Circle.smul_def, Circle.coe_inv_eq_conj, smul_eq_mul]

/-- **Almost-everywhere equality preserves the Fourier integral.** Let `G` be a monoid with a
topology and measurable structure, `μ` any measure and `χ : PontryaginDual G` a continuous
circle-valued character. if `f,h : G → ℂ` agree `μ`-almost everywhere, `fourierIntegral μ
f=fourierIntegral μ h` as functions on the character group. -/
theorem fourierIntegral_congr_ae (μ : Measure G) {f h : G → ℂ} (hfh : f =ᵐ[μ] h) :
    fourierIntegral μ f = fourierIntegral μ h := by
  funext χ
  apply integral_congr_ae
  filter_upwards [hfh] with g hg
  rw [hg]

/-- **Complex scalar homogeneity of the totalized Fourier integral.** Let `G` be a monoid with
a topology and measurable structure, `μ` any measure and `χ : PontryaginDual G` a
continuous circle-valued character. for `z∈ℂ` and any `f : G → ℂ`, `fourierIntegral μ (z •
f)=z • fourierIntegral μ f`. -/
theorem fourierIntegral_const_smul (μ : Measure G) (f : G → ℂ) (r : ℂ) :
    fourierIntegral μ (r • f) = r • fourierIntegral μ f := by
  funext χ
  simp only [Pi.smul_apply, fourierIntegral, smul_comm _ r, integral_smul]

/-- **L¹ integral upper bound of a character Fourier value.** Let `G` be a monoid with a
topology and measurable structure, `μ` any measure and `χ : PontryaginDual G` a continuous
circle-valued character. for any `f : G → ℂ`, `|fourierIntegral μ f χ|≤∫ |f(g)| dμ(g)`. -/
theorem norm_fourierIntegral_le_integral_norm (μ : Measure G) (f : G → ℂ)
    (χ : PontryaginDual G) : ‖fourierIntegral μ f χ‖ ≤ ∫ g, ‖f g‖ ∂μ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

variable [BorelSpace G]

/-- **Integrable domain unchanged by the inverse-character kernel.** Let `G` be a monoid with
a topology and measurable structure, `μ` any measure and `χ : PontryaginDual G` a
continuous circle-valued character. assume the measurable structure of `G` is Borel. Then
`g ↦ χ(g)⁻¹ • f(g)` is integrable exactly when `f` is integrable. -/
theorem fourierIntegral_convergent_iff (μ : Measure G) {f : G → ℂ} (χ : PontryaginDual G) :
    Integrable (fun g => (χ g)⁻¹ • f g) μ ↔ Integrable f μ := by
  have aux {h : G → ℂ} (hh : Integrable h μ) (ψ : PontryaginDual G) :
      Integrable (fun g => (ψ g)⁻¹ • h g) μ := by
    have hc : Continuous (fun g => (ψ g)⁻¹) := ψ.continuous.inv
    rw [← integrable_norm_iff (hc.aestronglyMeasurable.fun_smul hh.1)]
    simpa only [Circle.norm_smul] using hh.norm
  refine ⟨fun hf => ?_, fun hf => aux hf χ⟩
  have hh := aux hf χ⁻¹
  change Integrable (fun g => ((χ g)⁻¹)⁻¹ • ((χ g)⁻¹ • f g)) μ at hh
  simpa only [inv_inv, smul_smul, mul_inv_cancel, one_smul] using hh

/-- **Additivity of character Fourier integrals on the integrable domain.** Let `G` be a
monoid with a topology and measurable structure, `μ` any measure and `χ : PontryaginDual
G` a continuous circle-valued character. assume `G` has Borel measurable structure and
`f,h` are integrable against `μ`. Then `fourierIntegral μ (f+h)=fourierIntegral μ
f+fourierIntegral μ h`. -/
theorem fourierIntegral_add (μ : Measure G) {f h : G → ℂ} (hf : Integrable f μ)
    (hh : Integrable h μ) :
    fourierIntegral μ (f + h) = fourierIntegral μ f + fourierIntegral μ h := by
  funext χ
  simp only [Pi.add_apply, fourierIntegral, smul_add]
  rw [integral_add]
  · exact (fourierIntegral_convergent_iff μ χ).2 hf
  · exact (fourierIntegral_convergent_iff μ χ).2 hh

end

end PontryaginDual
