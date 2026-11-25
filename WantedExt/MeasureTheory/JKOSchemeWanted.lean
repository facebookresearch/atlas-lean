/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Diffusion.JKOStep
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Algebra.Order.Floor.Defs

/-!
# The JKO scheme: wanted results

Convergence of the Jordan–Kinderlehrer–Otto scheme to the Fokker–Planck equation (Theorem 5.1)
of R. Jordan, D. Kinderlehrer and F. Otto, *The variational formulation of the Fokker–Planck
equation*, SIAM J. Math. Anal. 29 (1998), 1–17, for the definitions of
`MathlibExt.Probability.Diffusion.JKOScheme`.

The standing assumptions of their Section 4 on the potential are: `Ψ` is `C^∞`, `Ψ ≥ 0`, and
`|∇Ψ(x)| ≤ C (Ψ(x) + 1)` for some constant `C`. They work on `ℝⁿ`; here `E` is any
finite-dimensional real inner product space with its Lebesgue measure.
-/

@[expose] public section

open MeasureTheory Filter Topology InnerProductSpace Laplacian
open scoped ENNReal ContDiff

open MathlibExt.Probability.Diffusion.JKOScheme

namespace MathlibExt.Probability.Diffusion.JKOSchemeWanted

/-- **Convergence of the JKO scheme to the Fokker–Planck equation.** Under the assumptions of
Section 4 on `Ψ`, let `β > 0` and let `ρ₀` be admissible with finite free energy. Then there is a
function `ρ : ℝ → E → ℝ`, `C^∞` on `(0, ∞) × E`, solving
`∂ₜρ = div(ρ ∇Ψ) + β⁻¹ Δρ` (written as `⟪∇ρ, ∇Ψ⟫ + ρ ΔΨ + β⁻¹ Δρ`) on `(0, ∞) × E`, with
`ρ(t) → dρ₀/dx` in `L¹` as `t ↓ 0`, with second moment and potential energy in `L^∞(0, T)`
for every `T`, and such that for every family of JKO sequences `ρ_h` started at `ρ₀`, the
piecewise-constant interpolation `ρ_h(t) = ρ_h(⌊t/h⌋)` converges to `ρ(t)` weakly in `L¹`
for every `t > 0`: `∫ g dρ_h(t) → ∫ g ρ(t) dx` as `h ↓ 0` for every bounded measurable `g`
(R. Jordan, D. Kinderlehrer and F. Otto, *The variational formulation of the Fokker–Planck
equation*, SIAM J. Math. Anal. 29 (1998), Theorem 5.1 with (31), (32) and (33)). JKO also assert
that `ρ` is the unique smooth solution with these properties; that uniqueness clause is not part
of this statement. -/
theorem_wanted tendsto_jko_fokkerPlanck {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ψ : E → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hΨ0 : ∀ x, 0 ≤ Ψ x)
    (hΨgrad : ∃ C : ℝ, ∀ x, ‖fderiv ℝ Ψ x‖ ≤ C * (Ψ x + 1))
    {β : ℝ} (hβ : 0 < β) (ρ₀ : ProbabilityMeasure E) (hρ₀ : IsAdmissible ρ₀)
    (hF : freeEnergy Ψ β (ρ₀ : Measure E) ≠ ⊤) :
    ∃ ρ : ℝ → E → ℝ,
      ContDiffOn ℝ ∞ (Function.uncurry ρ) (Set.Ioi 0 ×ˢ Set.univ) ∧
      (∀ t > 0, ∀ x, deriv (fun s => ρ s x) t =
        inner ℝ (gradient (ρ t) x) (gradient Ψ x) + ρ t x * Δ Ψ x + β⁻¹ * Δ (ρ t) x) ∧
      Tendsto (fun t => ∫⁻ x, ‖ρ t x - ((ρ₀ : Measure E).rnDeriv volume x).toReal‖ₑ)
        (𝓝[>] 0) (𝓝 0) ∧
      (∀ T > 0, ∃ M : ℝ≥0∞, M ≠ (∞ : ℝ≥0∞) ∧ ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) T)),
        ∫⁻ x, ‖x‖ₑ ^ 2 * ENNReal.ofReal (ρ t x) ≤ M ∧
          ∫⁻ x, ENNReal.ofReal (Ψ x) * ENNReal.ofReal (ρ t x) ≤ M) ∧
      ∀ (ρh : ℝ → ℕ → ProbabilityMeasure E), (∀ h > 0, ρh h 0 = ρ₀) →
        (∀ h > 0, IsJKOSequence Ψ β h (ρh h)) →
        ∀ t > 0, ∀ g : E → ℝ, Measurable g → (∃ C, ∀ x, |g x| ≤ C) →
          Tendsto (fun h => ∫ x, g x ∂(ρh h ⌊t / h⌋₊ : Measure E)) (𝓝[>] 0)
            (𝓝 (∫ x, g x * ρ t x))

end MathlibExt.Probability.Diffusion.JKOSchemeWanted
