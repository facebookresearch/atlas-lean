/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rosenbaum's sensitivity bounds for the matched-pair sign test

In a matched-pair observational study, Rosenbaum's model of hidden bias lets the odds that the
first unit of pair `i` receives treatment be `exp(γ (u_{i1} - u_{i2}))` for unobserved covariates
`u ∈ [0, 1]` and a sensitivity parameter `Γ = exp γ ≥ 1`. The probability `π_i` that the first
unit is treated then lies in `[1 / (1 + Γ), Γ / (1 + Γ)]`, so the within-pair treatment odds lie
in `[1 / Γ, Γ]`; `Γ = 1` is a randomized experiment.

Under the sharp null hypothesis of no treatment effect, the sign statistic, the number of
untied pairs in which the treated unit has the larger response, is a sum of independent
Bernoulli variables with success probabilities `π_i` (one of `π_i`, `1 - π_i` per pair, both in
the same interval). Its upper tail is increasing in each `π_i`, so it lies between the tails of
the binomial laws `Bin(n, 1 / (1 + Γ))` and `Bin(n, Γ / (1 + Γ))`. These two tails bound the
p-value of the sign test for every `Γ ≥ 1`.

Sources: P. R. Rosenbaum, "Sensitivity analysis for certain permutation inferences in matched
observational studies", Biometrika 74 (1987) 13–26; P. R. Rosenbaum, *Observational Studies*,
2nd ed., Springer (2002), §4.3.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Finset.Powerset

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.RosenbaumSensitivityWanted

/-- The probability `P(∑ᵢ Bᵢ ≥ k)` for independent Bernoulli variables `Bᵢ` with success
probabilities `π_i`, `i < n` (a Poisson-binomial upper tail), as a sum over the sets of
successes. -/
noncomputable def bernoulliSumUpperTail {n : ℕ} (π : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => k ≤ S.card),
    (∏ i ∈ S, π i) * ∏ i ∈ Sᶜ, (1 - π i)

/-- **Treatment probabilities under bounded hidden bias** (Rosenbaum 1987). For `γ ≥ 0` and
unobserved covariates `u₁, u₂ ∈ [0, 1]`, the probability `exp(γ u₁) / (exp(γ u₁) + exp(γ u₂))`
that the first unit of a pair is treated lies in `[1 / (1 + Γ), Γ / (1 + Γ)]` with
`Γ = exp γ`.

Sources: Rosenbaum (1987); Rosenbaum (2002), §4.2. -/
public theorem_wanted treatmentProb_mem {γ u₁ u₂ : ℝ} (hγ : 0 ≤ γ) (hu₁ : 0 ≤ u₁) (hu₁' : u₁ ≤ 1)
    (hu₂ : 0 ≤ u₂) (hu₂' : u₂ ≤ 1) :
    1 / (1 + Real.exp γ) ≤ Real.exp (γ * u₁) / (Real.exp (γ * u₁) + Real.exp (γ * u₂)) ∧
      Real.exp (γ * u₁) / (Real.exp (γ * u₁) + Real.exp (γ * u₂)) ≤
        Real.exp γ / (1 + Real.exp γ)

/-- **Binomial bounds on the sign-test tail** (Rosenbaum 1987). Let `Γ ≥ 1`, and let the success
probabilities `π_i`, `i < n`, of independent Bernoulli variables satisfy
`1 / (1 + Γ) ≤ π_i ≤ Γ / (1 + Γ)` for every `i`. Then for every `k`,
`P(Bin(n, 1 / (1 + Γ)) ≥ k) ≤ P(∑ᵢ Bᵢ ≥ k) ≤ P(Bin(n, Γ / (1 + Γ)) ≥ k)`, the binomial tails
being the Poisson-binomial tails with constant success probabilities.

Sources: Rosenbaum (1987); Rosenbaum (2002), §4.3. -/
public theorem_wanted upperTail_bounds {n : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) (π : Fin n → ℝ)
    (hlo : ∀ i, 1 / (1 + Γ) ≤ π i) (hhi : ∀ i, π i ≤ Γ / (1 + Γ)) (k : ℕ) :
    bernoulliSumUpperTail (fun _ : Fin n => 1 / (1 + Γ)) k ≤ bernoulliSumUpperTail π k ∧
      bernoulliSumUpperTail π k ≤ bernoulliSumUpperTail (fun _ : Fin n => Γ / (1 + Γ)) k

end WantedExt.Biology.StatisticalGenetics.RosenbaumSensitivityWanted
