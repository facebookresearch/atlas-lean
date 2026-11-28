/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.PolynomialNetworks.Deficiency
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

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
* `ReactionNetwork.propensity_nonneg`: nonnegativity of the propensity under
  nonnegative rate constants.
* `ReactionNetwork.propensity_eq_zero_of_not_le`: vanishing of the propensity
  when the source complex does not fit into the state.
-/

@[expose] public section

namespace MathlibExt.Biology.Dynamics.ComplexBalanced

namespace ReactionNetwork

/-- The stochastic mass-action propensity of reaction `r` of network `N` in state `x`
(molecule counts): `k r * ∏_s x_s (x_s - 1) ⋯ (x_s - src_s + 1)`, the falling factorial
`Nat.descFactorial x_s src_s` (it vanishes when `x_s < src_s`). Anderson, Craciun & Kurtz
(2010), §2. -/
noncomputable def propensity {S ρ : Type*} [Fintype S] (N : ReactionNetwork S ρ)
    (k : ρ → ℝ) (r : ρ) (x : S → ℕ) : ℝ :=
  k r * ∏ s, ((x s).descFactorial (N.src r s) : ℝ)

/-- The state reached from `x` by one firing of reaction `r` of network `N`,
`x - src r + prod r` (meaningful when `src r ≤ x`, the only case in which the propensity
is nonzero). -/
def fire {S ρ : Type*} (N : ReactionNetwork S ρ) (r : ρ) (x : S → ℕ) : S → ℕ :=
  fun s => x s - N.src r s + N.prod r s

/-- The state from which one firing of reaction `r` of network `N` leads to `x`,
`x - prod r + src r` (meaningful when `prod r ≤ x`). -/
def unfire {S ρ : Type*} (N : ReactionNetwork S ρ) (r : ρ) (x : S → ℕ) : S → ℕ :=
  fun s => x s - N.prod r s + N.src r s

/-- The propensity is nonnegative when all rate constants are nonnegative. -/
theorem propensity_nonneg {S ρ : Type*} [Fintype S] (N : ReactionNetwork S ρ) {k : ρ → ℝ}
    (hk : ∀ r, 0 ≤ k r) (r : ρ) (x : S → ℕ) : 0 ≤ N.propensity k r x := by
  unfold ReactionNetwork.propensity
  exact mul_nonneg (hk r)
    (Finset.prod_nonneg (fun s _ => Nat.cast_nonneg _))

/-- The propensity vanishes when the source complex does not fit into the state:
some species has fewer molecules than the reaction consumes, so its falling
factorial is zero. -/
theorem propensity_eq_zero_of_not_le {S ρ : Type*} [Fintype S] (N : ReactionNetwork S ρ)
    {k : ρ → ℝ} {r : ρ} {x : S → ℕ} (h : ¬ N.src r ≤ x) : N.propensity k r x = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, x s < N.src r s := by
    by_contra h'
    exact h fun s => not_lt.mp fun hs => h' ⟨s, hs⟩
  unfold ReactionNetwork.propensity
  have hfactor : ((x s).descFactorial (N.src r s) : ℝ) = 0 := by
    rw [Nat.descFactorial_eq_zero_iff_lt.2 hs, Nat.cast_zero]
  rw [Finset.prod_eq_zero (Finset.mem_univ s) hfactor, mul_zero]

end ReactionNetwork

end MathlibExt.Biology.Dynamics.ComplexBalanced
