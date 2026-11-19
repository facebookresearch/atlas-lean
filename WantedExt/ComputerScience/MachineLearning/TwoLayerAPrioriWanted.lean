/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.GeneralizationBounds.TwoLayerReLURademacher
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A priori estimate of the population risk for two-layer networks

W. E, C. Ma and L. Wu, *A priori estimates of the population risk for two-layer neural
networks*, Commun. Math. Sci. 17 (2019), arXiv:1810.06397, Theorem 4.1 (noiseless case). Data
`x ∼ ρ_x` lie in `X = [-1, 1]^d`, the target `f*` takes values in `[0, 1]` on `X` and has a
representation `f*(x) = ∫ a(w) σ(⟨w, x⟩) dπ(w)` with `π` a probability measure on the `ℓ¹` unit
sphere `{‖w‖₁ = 1}` (their equation (3.3), with `σ` the ReLU); `γ₂(f*)` is the infimum of
`(∫ |a|² dπ)^{1/2}` over such representations (equation (3.4)). Networks
`f(x; θ) = ∑ₖ aₖ σ(⟨wₖ, x⟩)` of width `m` are truncated to `[0, 1]`, and the estimator `θ̂`
minimizes the path-norm regularized empirical risk
`J_λ(θ) = (1/n) ∑ᵢ ½ (f(xᵢ; θ) - f*(xᵢ))² + λ (‖θ‖_P + 1)` (Definition 3.1). If
`log (2d) ≥ 1` and `λ ≥ λ_n = 4 √(2 log (2d) / n)`, then for every `δ > 0`, with probability at
least `1 - δ` over the sample,

`𝔼_x |f(x; θ̂) - f*(x)|² ≲ γ₂(f*)² / m + λ γ̂₂(f*) + n^{-1/2} (γ̂₂(f*) + √(log (n / δ)))`

with `γ̂₂ = max(1, γ₂)` and an absolute constant. The estimate is a priori: it depends on the
target only through its Barron norm, and its estimation part does not depend on the width `m`.

The statement below quantifies over every representation `(a, π)` with `∫ |a|² dπ ≤ γ²` instead
of naming `γ₂(f*)`; since the right-hand side is nondecreasing and continuous in `γ`, this is
equivalent to the stated form. The source's proof combines the direct approximation theorem
(Theorem 3.1) with the Rademacher bound for path-norm balls (bound (5.1)) and the Rademacher
risk bound (Theorem 5.1), through the a posteriori bound of Theorem 5.2. Measurability of `f*`
is assumed (on `X` the representation already makes `f*` continuous); every minimizer `θ̂` is
covered. As for the repository's Rademacher risk bound, the probability is that of a possibly
non-measurable event, measured by the outer measure of the product measure.
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.MachineLearning.GeneralizationBounds

open MeasureTheory

/-- **A priori estimate of the population risk for two-layer ReLU networks** (W. E, C. Ma and
L. Wu, *A priori estimates of the population risk for two-layer neural networks*, Commun. Math.
Sci. 17 (2019), Theorem 4.1, noiseless case). There is an absolute constant `C` such that the
following holds. Let `log (2d) ≥ 1`, `n ≥ 1`, `m ≥ 1`, let `ρ_x` be a probability measure
carried by `[-1, 1]^d`, and let `f*` be measurable with values in `[0, 1]` on `[-1, 1]^d` and
`f*(x) = ∫ a(w) max(⟨w, x⟩, 0) dπ(w)` there, for a probability measure `π` carried by the `ℓ¹`
unit sphere and `∫ |a|² dπ ≤ γ²`, `γ ≥ 0`. Let `λ ≥ 4 √(2 log (2d) / n)` and `δ > 0`. Then with
probability at least `1 - δ` over an i.i.d. sample `x₁, …, xₙ ∼ ρ_x`, every minimizer `θ̂` over
width-`m` networks of `J_λ(θ) = (1/n) ∑ᵢ ½ (T f(xᵢ; θ) - f*(xᵢ))² + λ (‖θ‖_P + 1)`, where
`T t = max (min t 1) 0` truncates to `[0, 1]`, satisfies
`𝔼_x |T f(x; θ̂) - f*(x)|² ≤ C (γ² / m + λ max(1, γ) + (max(1, γ) + √(log (n / δ))) / √n)`. -/
theorem_wanted twoLayer_a_priori_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ (d n m : ℕ), 1 ≤ Real.log (2 * d) → 0 < n → 0 < m →
      ∀ (ρx : Measure (Fin d → ℝ)), IsProbabilityMeasure ρx →
      ρx (Set.univ.pi fun _ => Set.Icc (-1 : ℝ) 1)ᶜ = 0 →
      ∀ (fstar : (Fin d → ℝ) → ℝ), Measurable fstar →
      (∀ x ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1), fstar x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (ν : Measure (Fin d → ℝ)), IsProbabilityMeasure ν → (∀ᵐ w ∂ν, ∑ j, |w j| = 1) →
      ∀ (a : (Fin d → ℝ) → ℝ),
      (∀ x ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1),
        Integrable (fun w => a w * max (∑ j, w j * x j) 0) ν ∧
          fstar x = ∫ w, a w * max (∑ j, w j * x j) 0 ∂ν) →
      ∀ γ : ℝ, 0 ≤ γ → ∫⁻ w, ‖a w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (γ ^ 2) →
      ∀ (lam δ : ℝ), 4 * √(2 * Real.log (2 * d) / n) ≤ lam → 0 < δ →
      1 - ENNReal.ofReal δ ≤ (Measure.pi fun _ : Fin n => ρx)
        {S | ∀ (â : Fin m → ℝ) (ŵ : Fin m → Fin d → ℝ),
          (∀ (a' : Fin m → ℝ) (w' : Fin m → Fin d → ℝ),
            (n : ℝ)⁻¹ * ∑ i, (max (min (twoLayerReLU â ŵ (S i)) 1) 0 - fstar (S i)) ^ 2 / 2 +
                lam * (pathNorm â ŵ + 1) ≤
              (n : ℝ)⁻¹ * ∑ i, (max (min (twoLayerReLU a' w' (S i)) 1) 0 - fstar (S i)) ^ 2 / 2 +
                lam * (pathNorm a' w' + 1)) →
          ∫⁻ x, ENNReal.ofReal ((max (min (twoLayerReLU â ŵ x) 1) 0 - fstar x) ^ 2) ∂ρx ≤
            ENNReal.ofReal (C * (γ ^ 2 / m + lam * max 1 γ +
              (max 1 γ + √(Real.log (n / δ))) / √(n : ℝ)))}

end CSLibExt.MachineLearning.GeneralizationBounds
