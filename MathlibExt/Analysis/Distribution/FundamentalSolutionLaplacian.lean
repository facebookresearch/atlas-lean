/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# A fundamental solution of the three-dimensional Laplacian

The inverse Fourier transform of the density $-1/((2π)^2 ‖ξ‖^2)$ gives a tempered distribution
whose Laplacian is the Dirac delta at the origin.
-/

open FourierTransform Laplacian MeasureTheory
open scoped SchwartzMap NNReal

namespace MathlibExt.Analysis.Distribution.NewtonPotentialWanted

private theorem hasTemperateGrowth_invNormSq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (hdim : Module.finrank ℝ E = 3) :
    (volume.withDensity fun x : E ↦ ((‖x‖₊ ^ 2)⁻¹ : ℝ≥0)).HasTemperateGrowth := by
  refine ⟨2, ?_⟩
  rw [integrable_withDensity_iff_integrable_coe_smul (by fun_prop)]
  simp only [NNReal.coe_inv, NNReal.coe_pow, coe_nnNorm, smul_eq_mul]
  -- In radial coordinates the Jacobian cancels the inverse square exactly.
  apply (integrable_fun_norm_addHaar volume
    (f := fun r : ℝ ↦ (r ^ 2)⁻¹ * (1 + r) ^ (-(2 : ℝ)))).2
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  apply h.integrableOn.congr_fun _ measurableSet_Ioi
  intro r (hr : 0 < r)
  simp [hdim, Real.norm_of_nonneg hr.le, smul_eq_mul, hr.ne']

/--
**Fundamental solution of the Laplacian in dimension three.** Let $E$ be a real inner product
space of dimension $3$. Then there is a complex-valued tempered distribution $N$ on $E$ such that
$\Delta N = \delta_0$, where $\Delta$ is the Laplacian in the sense of distributions and
$\delta_0$ is the Dirac delta at the origin.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Applications" / entry "fundamental solution of the Laplacian";
L. Evans, *Partial Differential Equations*, §2.2.
-/
public theorem exists_fundamental_solution_laplacian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) :
    ∃ N : 𝓢'(E, ℂ), Δ N = TemperedDistribution.delta (0 : E) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  let d (x : E) : ℝ≥0 := (‖x‖₊ ^ 2)⁻¹
  let μ : Measure E := volume.withDensity fun x ↦ d x
  have : μ.HasTemperateGrowth := hasTemperateGrowth_invNormSq hdim
  have hcancel : TemperedDistribution.smulLeftCLM ℂ (fun x : E ↦ (↑(‖x‖ ^ 2) : ℂ))
      μ.toTemperedDistribution = volume.toTemperedDistribution := by
    ext1 u
    have hg : (fun x : E ↦ (↑(‖x‖ ^ 2) : ℂ)).HasTemperateGrowth := by fun_prop
    simp only [TemperedDistribution.smulLeftCLM_apply_apply, Measure.toTemperedDistribution_apply,
      SchwartzMap.smulLeftCLM_apply_apply hg]
    rw [integral_withDensity_eq_integral_smul (μ := volume) (f := d) (by dsimp [d]; fun_prop)]
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne volume (0 : E)] with x hx
    simp [d, NNReal.smul_def, Complex.real_smul, smul_eq_mul, norm_ne_zero_iff.mpr hx]
  let c := Complex.ofReal (-(2 * Real.pi) ^ 2)
  have hc : c ≠ 0 := by simp [c, Real.pi_ne_zero]
  refine ⟨c⁻¹ • 𝓕⁻ μ.toTemperedDistribution, ?_⟩
  rw [TemperedDistribution.laplacian_eq_fourierMultiplierCLM, map_smul,
    TemperedDistribution.fourierMultiplierCLM_apply, fourier_fourierInv_eq, hcancel,
    ← TemperedDistribution.fourier_delta_zero, fourierInv_fourier_eq,
    ← Complex.coe_smul (-(2 * Real.pi) ^ 2)]
  change c • c⁻¹ • _ = _
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

end MathlibExt.Analysis.Distribution.NewtonPotentialWanted
