/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Approximate identities and Fejér means on `ℝ` in `L¹`

Two results from Section 1 (Fourier Integrals on `L²(ℝ)`) of the FourierAnalysis notes:

* `tendsto_eLpNorm_convolution_rescale_sub` (Theorem 4): for `K ∈ L¹(ℝ)` with `∫ K = 1` and
  `K_ε(x) = ε⁻¹ K(x / ε)`, `‖K_ε * f - f‖₁ → 0` as `ε → 0⁺` for every `f ∈ L¹(ℝ)`.
* `tendsto_eLpNorm_sub_fejerMean` (Theorem 3): for `f ∈ L¹(ℝ)`, the Fejér means
  `σ_N(x) = (1/2π) ∫_{-N}^{N} (1 - |ξ/N|)⁺ f̂(ξ) e^{ixξ} dξ`, with the notes' transform
  `f̂(ξ) = ∫ f(y) e^{-iyξ} dy` (Mathlib's `𝓕 f (ξ / 2π)`), converge to `f` in `L¹`.

Mathlib has convolution and the `L¹` Fourier transform but neither statement.

The statements are written from the textbook text recorded for targets 13 and 15 in
`v1/Atlas/FourierAnalysis/targets.yaml` at commit `6191bf1ba03d204784385ef5be2472be88035b93`.
The archived formalizations (`CesaroSummation.cesaro_L1_convergence` and
`ApproxIdentityR.approxIdentity_tendsto_L1_norm`) rest on the sorried
`approxIdentity_tendsto_Lp_norm`, so they are recorded here as wanted. The archived formalization
and its original license/provenance remain in `v1/` (the original license text is
`v1/LICENSE`).
-/

@[expose] public section

namespace MathlibExt.Analysis.Fourier.ApproximateIdentityRealWanted

open MeasureTheory Filter Topology Real
open scoped Convolution

/-- **Approximate identity in `L¹(ℝ)`** (FourierAnalysis notes, Section 1, Theorem 4). If
`K ∈ L¹(ℝ)` has `∫ K = 1` and `K_ε(x) = ε⁻¹ K(x / ε)`, then `‖K_ε * f - f‖₁ → 0` as `ε → 0⁺` for
every `f ∈ L¹(ℝ)`. -/
public theorem_wanted tendsto_eLpNorm_convolution_rescale_sub {K : ℝ → ℝ} (hK : Integrable K)
    (hK_int : ∫ x, K x = 1) {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun ε : ℝ => eLpNorm
        (fun x => ((fun y => ε⁻¹ * K (y / ε)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x)
        1 volume) (𝓝[>] 0) (𝓝 0)

/-- **Fejér means of the Fourier integral in `L¹(ℝ)`** (FourierAnalysis notes, Section 1,
Theorem 3). For `f ∈ L¹(ℝ)` with `f̂(ξ) = ∫ f(y) e^{-iyξ} dy`, the means
`σ_N(x) = (1/2π) ∫_{-N}^{N} (1 - |ξ/N|)⁺ f̂(ξ) e^{ixξ} dξ` converge to `f` in `L¹` as `N → ∞`. -/
public theorem_wanted tendsto_eLpNorm_sub_fejerMean {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun N : ℝ => eLpNorm (fun x : ℝ => f x - (1 / (2 * π) : ℂ) *
        ∫ ξ in -N..N, ((max (1 - |ξ / N|) 0 : ℝ) : ℂ) *
          (∫ y : ℝ, Complex.exp (-(y * ξ * Complex.I)) * f y) * Complex.exp (x * ξ * Complex.I))
        1 volume) atTop (𝓝 0)

end MathlibExt.Analysis.Fourier.ApproximateIdentityRealWanted
