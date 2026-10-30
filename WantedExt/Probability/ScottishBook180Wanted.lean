/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

namespace MathlibExt.Probability.ScottishBook180Wanted

/-- Stationarity in the sense of Slutsky and Khinchin, as stated:
mean zero, constant mean square, and `E[v(t) v(t+h)]` depending only
on `h`. The constant mean square and the covariance function are
existentially quantified. Integrability of the products is left
implicit in the Bochner-integral notation; see gaps. -/
def IsStationary (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (v : ℝ → Ω → ℝ) : Prop :=
  ∃ (c : ℝ) (R : ℝ → ℝ),
    (∀ t : ℝ, ∫ ω, v t ω ∂μ = 0) ∧
    (∀ t : ℝ, ∫ ω, (v t ω) ^ 2 ∂μ = c) ∧
    ∀ t h : ℝ, ∫ ω, v t ω * v (t + h) ω ∂μ = R h

/-- Scottish Book Problem 180: given a stationary random function `v`
(in the Slutsky-Khinchin sense), does there exist a random variable `A`,
uniformly distributed on `[0,1]` with `Prob(A < α) = α`, and a map
`φ` linking the uniform variable to the event, i.e. `A(φ α) = α` for
`α ∈ [0,1]` (condition (1), `E = φ(α)` as printed), such that for every
`t₁ ≠ t₂` the functions `v(t₁, φ(α))` and `v(t₂, φ(α))` are independent
in the sense of Steinhaus (condition (2))? Independence is read as
`ProbabilityTheory.IndepFun` of the two `α`-variables under the uniform
law on `[0,1]`. `A` stays on the original space `Ω` (it is not moved to
a newly constructed space). It is assumed that `Ω` already carries some
uniform variable `U`; this is the weakest hypothesis excluding
purely space-pathology refutations, and it does not trivialize the
conclusion, since `U` need not admit a section `φ` with the required
independence property. -/
def ScottishBookProblem180Claim : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω),
    MeasureTheory.IsProbabilityMeasure μ →
    (∃ U : Ω → ℝ, Measurable U ∧
      MeasureTheory.Measure.map U μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
    ∀ v : ℝ → Ω → ℝ, (∀ t, Measurable (v t)) → IsStationary Ω μ v →
    ∃ (A : Ω → ℝ) (φ : ℝ → Ω), Measurable A ∧
      MeasureTheory.Measure.map A μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1) ∧
      (∀ α : ℝ, α ∈ Set.Icc (0 : ℝ) 1 → A (φ α) = α) ∧
      ∀ t₁ t₂ : ℝ, t₁ ≠ t₂ →
        ProbabilityTheory.IndepFun (fun α => v t₁ (φ α))
          (fun α => v t₂ (φ α))
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))

/--
Scottish Book Problem 180 is false as stated. Counterexample: take
`Ω = ℝ` (Borel), `μ = volume.restrict (Set.Icc 0 1)`, and the
constant-in-time process `v t ω = ω - 1 / 2` for all `t`. It is
stationary with `c = 1 / 12`, `R ≡ 1 / 12`, by genuine finite
integrals (`∫₀¹ (ω - 1/2) dω = 0`, `∫₀¹ (ω - 1/2)² dω = 1 / 12`), and
the uniform-variable hypothesis holds with `U = id`. The process is
bounded, hence integrable with finite moments, so the totalization
loophole for Bochner integrals plays no role here. If witnesses
`A, φ` existed, then `A (φ α) = α` for `α ∈ [0,1]` would make `φ`
injective on `[0,1]`. But for `t₁ ≠ t₂` both `α`-functions are the
same function `f α = φ α - 1 / 2`, so the conclusion demands
`IndepFun f f` under Lebesgue measure on `[0,1]`; Mathlib's
characterisation (`indepFun_iff_measure_inter_preimage_eq_mul`, no
measurability hypothesis) then gives, for every Borel `S`,
`μ (f ⁻¹' S) ∈ {0, 1}`, and a dyadic-interval argument gives a `c`
with `f` a.e. constant, contradicting injectivity of `φ`, hence of
`f`. No non-degeneracy hypothesis is added: the source asks for none,
and such a hypothesis would be a new problem, not a transcription fix.
Source: J. Kampe de Feriet, Problem 180 of the Scottish Book,
typescript PDF pp. 82-83, printed pp. 79-80; see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted scottishBook180_refuted : ¬ ScottishBookProblem180Claim

end MathlibExt.Probability.ScottishBook180Wanted
