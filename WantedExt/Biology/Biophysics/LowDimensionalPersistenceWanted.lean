/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Persistence and global attractivity for low-dimensional mass-action systems

Pantea (2012): for mass-action systems `ẋ = ∑_r k_r x^{src r} (prod r - src r)` on the positive
orthant,

* weakly reversible systems whose stoichiometric subspace has dimension two are persistent: every
  bounded trajectory starting in the positive orthant stays away from the boundary,
  `liminf_{t → ∞} x_s(t) > 0` for every species `s` (a consequence of Theorem 5.1, which covers
  lower-endotactic `κ`-variable systems);
* the global attractor conjecture holds when the stoichiometric subspace has dimension three
  (Theorem 6.3): for a complex-balanced system, the unique positive equilibrium of each positive
  stoichiometric compatibility class attracts every trajectory starting in that class.

The network, its stoichiometric subspace, the mass-action field and weak reversibility are the
shared ones of `MathlibExt.Dynamics.PolynomialNetworks.Deficiency`. A trajectory is a function
`x : ℝ → (S → ℝ)` with `x(0)` positive that has derivative `massActionField k (x t)` at every
`t ≥ 0`. A system is complex balanced when it has a positive equilibrium `c` at which, for every
complex `y`, the total rate of reactions out of `y` equals the total rate of reactions into `y`;
this is `ReactionNetwork.IsComplexBalanced` of `Domains.Biology.Dynamics.ComplexBalanced`, where
the Horn–Jackson theorems are proved, together with positivity of `c`.
Positive rate constants are fixed in time here; Theorem 5.1 itself, for time-dependent rates and
lower-endotactic networks, is not recorded.

Sources: C. Pantea, "On the persistence and global stability of mass-action systems", SIAM Journal
on Mathematical Analysis 44 (2012) 1636–1673, arXiv:1103.0603,
Theorems 5.1 and 6.3.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.Dynamics.ComplexBalanced
public import MathlibExt.Dynamics.PolynomialNetworks.Deficiency
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

namespace WantedExt.Biology.Biophysics.LowDimensionalPersistenceWanted

open MathlibExt.Biology.Dynamics.ComplexBalanced Filter Topology

variable {S ρ : Type*} [Fintype S] [Fintype ρ]

/-- `x` is a **forward trajectory** of the mass-action system of `N` with rate constants `k`
starting in the positive orthant: every coordinate of `x 0` is positive and `x` has derivative
`massActionField k (x t)` at every `t ≥ 0`. -/
def IsPositiveTrajectory (N : ReactionNetwork S ρ) (k : ρ → ℝ) (x : ℝ → S → ℝ) : Prop :=
  (∀ s, 0 < x 0 s) ∧ ∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t

/-- **Persistence in dimension two** (Pantea 2012, consequence of Theorem 5.1): for a weakly
reversible network on finitely many species and reactions whose stoichiometric subspace has
dimension `2`, positive rate constants `k`, and a forward trajectory `x` starting in the positive
orthant that is bounded on `[0, ∞)`, every species stays eventually above a positive level: for
each `s` there is `δ > 0` with `δ ≤ x(t)_s` for all large `t`.

Source: Pantea (2012), Theorem 5.1. -/
public theorem_wanted persistent_of_finrank_two (N : ReactionNetwork S ρ)
    (hwr : N.IsWeaklyReversible) (hdim : Module.finrank ℝ N.stoichiometricSubspace = 2)
    (k : ρ → ℝ) (hk : ∀ r, 0 < k r) (x : ℝ → S → ℝ) (hx : IsPositiveTrajectory N k x)
    (hbdd : ∃ C, ∀ t, 0 ≤ t → ∀ s, |x t s| ≤ C) :
    ∀ s, ∃ δ > 0, ∀ᶠ t in atTop, δ ≤ x t s

/-- **The global attractor conjecture in dimension three** (Pantea 2012, Theorem 6.3): for a network
on finitely many species and reactions whose stoichiometric subspace has dimension `3`, positive
rate constants `k` for which the system is complex balanced at some positive `c₀`
(`N.IsComplexBalanced k c₀`), a forward
trajectory `x` starting in the positive orthant, and a positive equilibrium `c`
(`massActionField k c = 0`, `c` positive) in the same stoichiometric compatibility class
(`c - x 0` in the stoichiometric subspace), `x(t) → c` as `t → ∞`.

Source: Pantea (2012), Theorem 6.3. -/
public theorem_wanted tendsto_equilibrium_of_finrank_three (N : ReactionNetwork S ρ)
    (hdim : Module.finrank ℝ N.stoichiometricSubspace = 3) (k : ρ → ℝ) (hk : ∀ r, 0 < k r)
    (hcb : ∃ c₀, (∀ s, 0 < c₀ s) ∧ N.IsComplexBalanced k c₀) (x : ℝ → S → ℝ)
    (hx : IsPositiveTrajectory N k x)
    (c : S → ℝ) (hc : ∀ s, 0 < c s) (heq : N.massActionField k c = 0)
    (hclass : c - x 0 ∈ N.stoichiometricSubspace) :
    Tendsto x atTop (𝓝 c)

end WantedExt.Biology.Biophysics.LowDimensionalPersistenceWanted
