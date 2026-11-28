/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Stochastic absolute concentration robustness: non-terminal complexes are turned off

A chemical reaction network on a finite set `S` of species has reactions `r : y_r → y'_r` with
complexes in `ℕ^S`. Its deficiency is `δ = n - ℓ - s` (complexes, linkage classes, dimension of
the stoichiometric subspace). A complex is terminal if every complex reachable from it by a
directed path of reactions reaches it back, that is, its strong linkage class is terminal;
otherwise it is non-terminal. The network is conservative if some `w` with all entries positive
has `w · (y' - y) = 0` for every reaction. Complex `y` is turned off at a state `x ∈ ℕ^S` if
`x_i < y_i` for some `i`. Complex `y` is dominated by `y'`, written `y ≪ y'`, if `y'_i ≤ y_i` for
every `i`. Rate functions are stoichiometrically admissible if `λ_r(x) > 0` exactly when
`x ≥ y_r` componentwise.

**Theorem 2** (Anderson–Enciso–Johnston 2014). Consider a reaction network which is
conservative, has deficiency one, and for which the deterministic mass-action system admits a
positive equilibrium for some choice of rate constants. Suppose there are two non-terminal
complexes `y_1 ≪ y_2`. Then, for any choice of stoichiometrically admissible kinetics, all
non-terminal complexes are turned off at each positive recurrent state of the stochastically
modelled system.

Positive recurrence. With admissible kinetics, the chain jumps from `x` to `x - y_r + y'_r`
exactly for the reactions with `y_r ≤ x`, so its communication structure does not depend on the
kinetics. For a conservative network the states reachable from `x` lie in the finite set
`{z ∈ ℕ^S : w · z = w · x}`, so a state is positive recurrent if and only if it is recurrent, if
and only if every state reachable from it reaches it back. That combinatorial form is used here.
The deficiency, complexes and linkage classes are those of
`MathlibExt.Dynamics.PolynomialNetworks.Deficiency`.

Sources: D. F. Anderson, G. A. Enciso, M. D. Johnston, "Stochastic analysis of biochemical
reaction networks with absolute concentration robustness", J. R. Soc. Interface 11 (2014)
20130943, Section 2 and Theorem 2 (arXiv:1310.3761).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Dynamics.PolynomialNetworks.Deficiency
public import Mathlib.Logic.Relation

@[expose] public section

namespace WantedExt.Biology.Biophysics.StochasticAbsoluteConcentrationRobustnessWanted

open MathlibExt.Biology.Dynamics.ComplexBalanced

variable {S ρ : Type*} (N : ReactionNetwork S ρ)

/-- The complex `y` is terminal: every complex reachable from `y` by a directed path of reactions
reaches `y` back. -/
def IsTerminal (y : S → ℕ) : Prop :=
  ∀ y', Relation.ReflTransGen N.Reacts y y' → Relation.ReflTransGen N.Reacts y' y

/-- The complex `y` is non-terminal: it is a complex of the network and is not terminal. -/
def IsNonTerminal (y : S → ℕ) : Prop :=
  y ∈ N.complexes ∧ ¬ IsTerminal N y

/-- The network is conservative: some `w` with all entries positive is orthogonal to every
reaction vector. -/
def IsConservative [Fintype S] : Prop :=
  ∃ w : S → ℝ, (∀ s, 0 < w s) ∧ ∀ r, ∑ s, w s * ((N.prod r s : ℝ) - N.src r s) = 0

/-- The complex `y` is turned off at the state `x`: `x s < y s` for some species `s`. -/
def IsTurnedOff (y x : S → ℕ) : Prop :=
  ∃ s, x s < y s

/-- One step of the stochastic chain under stoichiometrically admissible kinetics: some reaction
`r` with `src r ≤ x` fires and moves `x` to `x - src r + prod r`. -/
def Step (x x' : S → ℕ) : Prop :=
  ∃ r, N.src r ≤ x ∧ x' = x - N.src r + N.prod r

/-- `x` is recurrent: every state reachable from `x` reaches `x` back. For a conservative network
this is positive recurrence under any stoichiometrically admissible kinetics. -/
def IsRecurrent (x : S → ℕ) : Prop :=
  ∀ x', Relation.ReflTransGen (Step N) x x' → Relation.ReflTransGen (Step N) x' x

/-- **Non-terminal complexes are turned off at positive recurrent states** (Anderson–Enciso–
Johnston 2014, Theorem 2). Let `N` have finitely many species and reactions, be conservative
(some `w` with positive entries is orthogonal to every reaction vector), have deficiency one,
and have a positive equilibrium of the deterministic mass-action system for some positive rate
constants `k` (some `c` with all entries positive has `massActionField k c = 0`). Suppose there
are two distinct non-terminal complexes `y₁` and `y₂` with `y₁ ≪ y₂`, that is `y₂ ≤ y₁`
componentwise. Then every non-terminal complex is turned off at every positive recurrent state
`x` of the stochastic model with stoichiometrically admissible kinetics.

Source: D. F. Anderson, G. A. Enciso, M. D. Johnston, J. R. Soc. Interface 11 (2014) 20130943,
Theorem 2. -/
theorem_wanted isTurnedOff_of_isRecurrent [Fintype S] [Fintype ρ] (hcons : IsConservative N)
    (hδ : N.deficiency = 1)
    (heq : ∃ k : ρ → ℝ, (∀ r, 0 < k r) ∧ ∃ c : S → ℝ, (∀ s, 0 < c s) ∧ N.massActionField k c = 0)
    {y₁ y₂ : S → ℕ} (hy₁ : IsNonTerminal N y₁) (hy₂ : IsNonTerminal N y₂) (hne : y₁ ≠ y₂)
    (hdom : y₂ ≤ y₁) {x : S → ℕ} (hx : IsRecurrent N x) {y : S → ℕ} (hy : IsNonTerminal N y) :
    IsTurnedOff y x

end WantedExt.Biology.Biophysics.StochasticAbsoluteConcentrationRobustnessWanted
