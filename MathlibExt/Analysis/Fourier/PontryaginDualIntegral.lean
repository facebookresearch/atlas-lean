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
# The actual continuous-character Fourier integral

The scalar kernel is the original negative character, χ(g)⁻¹ = conj(χ(g)).
This primitive uses the actual continuous-character group and original measure.
Its convergence and scalar/additive laws have no countability, sigma-finiteness,
Fourier-unitary or normalized-dual-Haar input. On integrable source functions
it is the literal source Fourier integral. No Plancherel conclusion is asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace PontryaginDual

noncomputable section

universe uG

variable {G : Type uG} [Monoid G] [TopologicalSpace G] [MeasurableSpace G]

/-- The Fourier integral uses the actual inverse-character scalar kernel. -/
def fourierIntegral (μ : Measure G) (f : G → ℂ) (χ : PontryaginDual G) : ℂ :=
  ∫ g, (χ g)⁻¹ • f g ∂μ

/-- The source Fourier kernel is literally the conjugate original character. -/
theorem fourierIntegral_apply (μ : Measure G) (f : G → ℂ) (χ : PontryaginDual G) :
    fourierIntegral μ f χ = ∫ g, (starRingEnd ℂ) ((χ g : Circle) : ℂ) * f g ∂μ := by
  simp only [fourierIntegral, Circle.smul_def, Circle.coe_inv_eq_conj, smul_eq_mul]

/-- Almost-everywhere equal source functions have the same actual Fourier integral. -/
theorem fourierIntegral_congr_ae (μ : Measure G) {f h : G → ℂ} (hfh : f =ᵐ[μ] h) :
    fourierIntegral μ f = fourierIntegral μ h := by
  funext χ
  apply integral_congr_ae
  filter_upwards [hfh] with g hg
  rw [hg]

/-- Complex scalar multiplication commutes with the literal original integral. -/
theorem fourierIntegral_const_smul (μ : Measure G) (f : G → ℂ) (r : ℂ) :
    fourierIntegral μ (r • f) = r • fourierIntegral μ f := by
  funext χ
  simp only [Pi.smul_apply, fourierIntegral, smul_comm _ r, integral_smul]

/-- The literal Fourier integral is bounded pointwise by the original L1 integral. -/
theorem norm_fourierIntegral_le_integral_norm (μ : Measure G) (f : G → ℂ)
    (χ : PontryaginDual G) : ‖fourierIntegral μ f χ‖ ≤ ∫ g, ‖f g‖ ∂μ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

variable [BorelSpace G]

/-- Multiplication by the actual inverse character preserves exactly the integrable domain. -/
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

/-- Addition is preserved on the original integrable source domain. -/
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
