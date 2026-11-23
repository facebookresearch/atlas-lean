/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.PolynomialNetworks.Deficiency
public import Mathlib.Basic.Real.Basic

/-!
# Stochastic mass-action propensity and firing

This module defines the stochastic mass-action propensity of a reaction in a
reaction network, together with the one-step firing maps `fire` and `unfire`.
It is the shared foundation for the Domains systems-biology development and
for the SSA direct method in `CSLibExt`: downstream developments use these
definitions rather than private copies.

The propensity is the falling-factorial rate of Anderson, Craciun and Kurtz
(2010), §2; `fire` and `unfire` step molecule counts by one reaction firing,
as in Gillespie's stochastic simulation algorithm (Gillespie 1977).

## Main declarations

* `ReactionNetwork.propensity`: the stochastic mass-action propensity
  `k r * ∏ s, ((x s).descFactorial (N.src r s) : ℝ)`.
* `ReactionNetwork.fire`: the state reached from `x` by one firing of reaction `r`.
* `ReactionNetwork.unfire`: the state from which one firing of reaction `r` leads to `x`.
-/

@[expose] public section

namespace MathlibExt.Biology.Dynamics.ComplexBalanced

namespace ReactionNetwork

/-- The stochastic mass-action propensity of reaction `r` of network `N` in state `x`
(molecule counts): `k r * ∏_s x_s (x_s - 1) ⋯ (x_s - src_s + 1)`, the falling factorial
`Nat.descFactorial x_s src_s` (it vanishes when `x_s < src_s`). Anderson, Craciun & Kurtz
(2010), §2. -/
noncomputable def propensity {S ρ : Type*} [Fintype S] (N : ReactionNetwork S ρ) (k : ρ → ℝ) (r : ρ) (x : S → ℕ) : ℝ := k r * ∏ s, ((x s).descFactorial (N.src r s) : ℝ)

/-- The state reached from `x` by one firing of reaction `r` of network `N`,
`x - src r + prod r` (meaningful when `src r ≤ x`, the only case in which the propensity
is nonzero). -/
def fire {S ρ : Type*} (N : ReactionNetwork S ρ) (r : ρ) (x : S → ℕ) : S → ℕ := fun s => x s - N.src r s + N.prod r s

/-- The state from which one firing of reaction `r` of network `N` leads to `x`,
`x - prod r + src r` (meaningful when `prod r ≤ x`). -/
def unfire {S ρ : Type*} (N : ReactionNetwork S ρ) (r : ρ) (x : S → ℕ) : S → ℕ := fun s => x s - N.prod r s + N.src r s

end ReactionNetwork

end MathlibExt.Biology.Dynamics.ComplexBalanced
