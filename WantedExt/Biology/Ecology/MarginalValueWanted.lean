/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Charnov's marginal value theorem

A forager meets patch types `i` with probabilities `pᵢ > 0`, spends time `tᵢ ≥ 0` in a patch of
type `i`, gaining `gᵢ(tᵢ)`, and travels on average `τ > 0` between patches. Its long-run intake
rate is `E(t) = ∑ᵢ pᵢ gᵢ(tᵢ) / (τ + ∑ᵢ pᵢ tᵢ)`. With gains `gᵢ` on `[0, ∞)` that vanish at `0`,
are nondecreasing, concave and differentiable on `(0, ∞)`, Charnov (1976) showed that at an
optimal allocation with every `tᵢ* > 0` the marginal gain in every patch equals the optimal
rate: `gᵢ'(tᵢ*) = E(t*)`. Concavity makes this condition sufficient for global optimality, and
strict concavity makes the optimum unique.

Recorded here: necessity, sufficiency and uniqueness of the marginal value condition for
interior allocations. The primary was not read; the statement follows the restatement of
Wajnberg, Bernhard, Hamelin and Boivin (2006). Sufficiency and uniqueness are derived.

Sources: E. L. Charnov, "Optimal foraging, the marginal value theorem", Theor. Popul. Biol. 9
(1976) 129–136, doi:10.1016/0040-5809(76)90040-X; É. Wajnberg, P. Bernhard, F. Hamelin and
G. Boivin, "Optimal patch time allocation for time-limited foragers", Behav. Ecol. Sociobiol. 60
(2006) 1–10, doi:10.1007/s00265-005-0131-7.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace WantedExt.Biology.Ecology.MarginalValueWanted

/-- **Long-run intake rate.** The long-run intake rate `E(t) = ∑ᵢ pᵢ gᵢ(tᵢ) / (τ + ∑ᵢ pᵢ tᵢ)`. -/
noncomputable def intakeRate {ι : Type*} [Fintype ι] (p : ι → ℝ) (g : ι → ℝ → ℝ) (τ : ℝ)
    (t : ι → ℝ) : ℝ :=
  (∑ i, p i * g i (t i)) / (τ + ∑ i, p i * t i)

/-- **Gain functions.** The standing hypotheses on the gain functions: every `gᵢ` vanishes at `0`,
is nondecreasing and concave on `[0, ∞)`, and is differentiable on `(0, ∞)`. -/
def IsGainFamily {ι : Type*} (g : ι → ℝ → ℝ) : Prop :=
  ∀ i, g i 0 = 0 ∧ MonotoneOn (g i) (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) (g i) ∧
    DifferentiableOn ℝ (g i) (Set.Ioi 0)

/-- **The marginal value theorem, necessity.** Let `pᵢ > 0` with `∑ pᵢ = 1`, `τ > 0`, and let the
gains `gᵢ` vanish at `0`, be nondecreasing and concave on `[0, ∞)` and differentiable on `(0, ∞)`.
If `t*` with every `tᵢ* > 0` maximizes the intake rate `E` over all allocations with every `tᵢ ≥ 0`,
then `gᵢ'(tᵢ*) = E(t*)` for every patch type `i`.

Sources: Charnov (1976); Wajnberg et al. (2006). -/
public theorem_wanted deriv_eq_intakeRate_of_isMaxOn {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∑ i, p i = 1) (g : ι → ℝ → ℝ) (hg : IsGainFamily g) (τ : ℝ)
    (hτ : 0 < τ) (ts : ι → ℝ) (hts : ∀ i, 0 < ts i)
    (hmax : ∀ t : ι → ℝ, (∀ i, 0 ≤ t i) → intakeRate p g τ t ≤ intakeRate p g τ ts) (i : ι) :
    deriv (g i) (ts i) = intakeRate p g τ ts

/-- **The marginal value theorem, sufficiency.** A derived converse: under the hypotheses of the
necessity statement (`pᵢ > 0`, `∑ pᵢ = 1`, `τ > 0`, gains vanishing at `0`, nondecreasing and
concave on `[0, ∞)`, differentiable on `(0, ∞)`), if `t*` with every `tᵢ* > 0` satisfies
`gᵢ'(tᵢ*) = E(t*)` for every `i`, then `E(t) ≤ E(t*)` for every allocation with every `tᵢ ≥ 0`.

Sources: Charnov (1976); Wajnberg et al. (2006). -/
public theorem_wanted isMaxOn_of_deriv_eq {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∑ i, p i = 1) (g : ι → ℝ → ℝ) (hg : IsGainFamily g) (τ : ℝ)
    (hτ : 0 < τ) (ts : ι → ℝ) (hts : ∀ i, 0 < ts i)
    (hmv : ∀ i, deriv (g i) (ts i) = intakeRate p g τ ts) :
    ∀ t : ι → ℝ, (∀ i, 0 ≤ t i) → intakeRate p g τ t ≤ intakeRate p g τ ts

/-- **Uniqueness under strict concavity.** A derived complement: under the hypotheses of the
sufficiency statement, and if moreover every `gᵢ` is strictly concave on `[0, ∞)`, an interior
allocation `t*` satisfying `gᵢ'(tᵢ*) = E(t*)` for every `i` is the unique maximizer: every
allocation `t` with every `tᵢ ≥ 0` and `E(t) = E(t*)` equals `t*`.

Sources: Charnov (1976); Wajnberg et al. (2006). -/
public theorem_wanted eq_of_intakeRate_eq {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∑ i, p i = 1) (g : ι → ℝ → ℝ) (hg : IsGainFamily g)
    (hstrict : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (g i)) (τ : ℝ) (hτ : 0 < τ) (ts : ι → ℝ)
    (hts : ∀ i, 0 < ts i) (hmv : ∀ i, deriv (g i) (ts i) = intakeRate p g τ ts)
    (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (heq : intakeRate p g τ t = intakeRate p g τ ts) :
    t = ts

end WantedExt.Biology.Ecology.MarginalValueWanted
