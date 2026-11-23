/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The JKO scheme for the Fokker–Planck equation

R. Jordan, D. Kinderlehrer and F. Otto (*The variational formulation of the Fokker–Planck
equation*, SIAM J. Math. Anal. 29 (1998), 1–17) write the Fokker–Planck equation

`∂ₜρ = div(ρ ∇Ψ) + β⁻¹ Δρ`

as the gradient flow of the free energy `F(ρ) = ∫ Ψ ρ dx + β⁻¹ ∫ ρ log ρ dx` for the quadratic
Wasserstein distance, through the implicit scheme (their (13)): `ρ⁽ᵏ⁾` minimizes
`½ W₂(ρ⁽ᵏ⁻¹⁾, ρ)² + h F(ρ)` over the set `K` of probability densities with finite second moment.

This file defines the ingredients on a finite-dimensional real inner product space `E` (for instance
`EuclideanSpace ℝ (Fin n)`, so that `W₂` is taken for the Euclidean distance) with its
Lebesgue measure, and proves the comparison inequality that starts the a priori
estimates. Existence and uniqueness of the step (JKO Proposition 4.1) and convergence of the
scheme to the Fokker–Planck equation (JKO Theorem 5.1) are wanted results in
`WantedExt/MeasureTheory/JKOSchemeWanted.lean`; the metric-space part of the estimates is proved
in `MathlibExt/Analysis/Variational/MinimizingMovement.lean`.

Probability densities are represented by probability measures absolutely continuous with respect
to Lebesgue measure; the density is the Radon–Nikodym derivative. Energies take values in
`EReal`: `∫ Ψ ρ` may be `+∞`, and `∫ ρ log ρ` is the difference of the integrals of its positive
and negative parts (JKO show, their (14), that the negative part is finite on `K`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (wasserstein wasserstein_self)

namespace MathlibExt.Probability.Diffusion.JKOScheme

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Admissible densities of the JKO scheme.** A probability measure `ρ` on `E` (`ℝⁿ` in
JKO) belongs to the JKO admissible set `K` if it is absolutely continuous with respect to
Lebesgue measure and has finite second moment `M(ρ) = ∫ |x|² dρ < ∞` (R. Jordan,
D. Kinderlehrer and F. Otto, SIAM J. Math. Anal. 29 (1998), the set `K` of Section 4). -/
def IsAdmissible (ρ : ProbabilityMeasure E) : Prop :=
  (ρ : Measure E) ≪ volume ∧ ∫⁻ x, ‖x‖ₑ ^ 2 ∂(ρ : Measure E) < ∞

/-- **Negative Boltzmann entropy.** For a measure `ρ` on `E` with density `f = dρ/dx`,
`S(ρ) = ∫ f log f dx ∈ [-∞, +∞]`, computed as the integral of the positive part minus the
integral of the negative part of `f log f` (R. Jordan, D. Kinderlehrer and F. Otto, SIAM J. Math.
Anal. 29 (1998), the functional `S` of Section 2, the negative of the Gibbs–Boltzmann entropy). -/
noncomputable def negEntropy (ρ : Measure E) : EReal :=
  ((∫⁻ x, ENNReal.ofReal ((ρ.rnDeriv volume x).toReal * Real.log (ρ.rnDeriv volume x).toReal)
      : ℝ≥0∞) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (-((ρ.rnDeriv volume x).toReal *
      Real.log (ρ.rnDeriv volume x).toReal)) : ℝ≥0∞) : EReal)

/-- **Potential energy.** For a potential `Ψ ≥ 0` and a measure `ρ`, `E(ρ) = ∫ Ψ dρ ∈ [0, ∞]`
(R. Jordan, D. Kinderlehrer and F. Otto, SIAM J. Math. Anal. 29 (1998), the functional `E` of
Section 2; negative values of `Ψ` are truncated to `0`, which is harmless under JKO's assumption
`Ψ ≥ 0`). -/
noncomputable def potentialEnergy (Ψ : E → ℝ) (ρ : Measure E) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Ψ x) ∂ρ

/-- **Free energy of the Fokker–Planck equation.** `F(ρ) = E(ρ) + β⁻¹ S(ρ)`, potential energy
plus `β⁻¹` times the negative entropy, with values in `EReal` (R. Jordan, D. Kinderlehrer and
F. Otto, SIAM J. Math. Anal. 29 (1998), equation (5)). -/
noncomputable def freeEnergy (Ψ : E → ℝ) (β : ℝ) (ρ : Measure E) : EReal :=
  (potentialEnergy Ψ ρ : EReal) + ((β⁻¹ : ℝ) : EReal) * negEntropy ρ

/-- **JKO objective.** `½ W₂(ρ₀, ρ)² + h F(ρ)`, the functional minimized at each step of the
scheme (13) of R. Jordan, D. Kinderlehrer and F. Otto, SIAM J. Math. Anal. 29 (1998). -/
noncomputable def jkoObjective (Ψ : E → ℝ) (β h : ℝ) (ρ₀ ρ : ProbabilityMeasure E) :
    EReal :=
  ((wasserstein 2 ρ₀ ρ ^ (2 : ℝ) / 2 : ℝ≥0∞) : EReal) + (h : EReal) * freeEnergy Ψ β ρ

/-- **JKO step.** `ρ` is a step of the JKO scheme from `ρ₀` if it is admissible and minimizes
`½ W₂(ρ₀, ·)² + h F` over the admissible set `K` (R. Jordan, D. Kinderlehrer and F. Otto, SIAM
J. Math. Anal. 29 (1998), scheme (13)). -/
def IsJKOStep (Ψ : E → ℝ) (β h : ℝ) (ρ₀ ρ : ProbabilityMeasure E) : Prop :=
  IsAdmissible ρ ∧ ∀ ν, IsAdmissible ν → jkoObjective Ψ β h ρ₀ ρ ≤ jkoObjective Ψ β h ρ₀ ν

/-- **JKO sequence.** `ρ : ℕ → ProbabilityMeasure E` solves the JKO scheme with time step `h` if
each `ρ (k + 1)` is a JKO step from `ρ k` (R. Jordan, D. Kinderlehrer and F. Otto, SIAM J. Math.
Anal. 29 (1998), scheme (13) with `ρ⁽⁰⁾ = ρ 0`). -/
def IsJKOSequence (Ψ : E → ℝ) (β h : ℝ) (ρ : ℕ → ProbabilityMeasure E) : Prop :=
  ∀ k, IsJKOStep Ψ β h (ρ k) (ρ (k + 1))

/-- **The JKO objective at the previous state.** Since `W₂(ρ₀, ρ₀) = 0`, the objective of the
competitor `ρ = ρ₀` is `h F(ρ₀)`. -/
theorem jkoObjective_self (Ψ : E → ℝ) (β h : ℝ) (ρ₀ : ProbabilityMeasure E) :
    jkoObjective Ψ β h ρ₀ ρ₀ = (h : EReal) * freeEnergy Ψ β ρ₀ := by
  rw [jkoObjective, wasserstein_self (by norm_num : (0 : ℝ) < 2)]
  simp

/-- **One-step comparison inequality of the JKO scheme.** If `ρ₀` is admissible and `ρ` is a
JKO step from `ρ₀`, then `½ W₂(ρ₀, ρ)² + h F(ρ) ≤ h F(ρ₀)`: compare the minimizer with the
admissible competitor `ρ₀` (R. Jordan, D. Kinderlehrer and F. Otto, *The variational formulation
of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), proof of Theorem 5.1, the
inequality preceding (46)). -/
theorem IsJKOStep.jkoObjective_le {Ψ : E → ℝ} {β h : ℝ} {ρ₀ ρ : ProbabilityMeasure E}
    (hρ : IsJKOStep Ψ β h ρ₀ ρ) (hρ₀ : IsAdmissible ρ₀) :
    jkoObjective Ψ β h ρ₀ ρ ≤ (h : EReal) * freeEnergy Ψ β ρ₀ :=
  (hρ.2 ρ₀ hρ₀).trans_eq (jkoObjective_self Ψ β h ρ₀)

end MathlibExt.Probability.Diffusion.JKOScheme
