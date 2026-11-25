/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Positive steady states of weakly reversible mass-action systems

A reaction network with real stoichiometric coefficients on a finite set `S` of species is a
finite family of reactions `r`, each turning a source complex `src r : S → ℝ` into a product
complex `prod r : S → ℝ`. Negative coefficients are allowed, so the state space is the open
positive orthant. With positive rate constants `k`, mass-action kinetics gives the vector field
`x ↦ ∑_r k r x^{src r} (prod r - src r)` on positive states, where `x^y = ∏_s x_s ^ y_s`
(real powers). The stoichiometric subspace is the span of the reaction vectors
`prod r - src r`; a positive stoichiometric class is `(x₀ + span) ∩ ℝ_{>0}^S` for a positive
`x₀`. The network is weakly reversible if every reaction `y → y'` lies on a directed cycle of
reactions, that is, there is a directed path of reactions from `y'` back to `y`.

**Theorem** (Boros 2019, Theorem 1). For every weakly reversible mass-action system, any
positive rate constants and every positive stoichiometric class `P`, the set of positive steady
states meets `P`.

Clause map. The source labels complexes by the columns of a matrix `Y` and allows two labels to
carry the same column; here complexes are identified by their coefficient vectors, which keeps
weak reversibility and does not change the vector field. Parallel reactions add their rates and
reactions with `src r = prod r` contribute nothing, so neither changes the set of positive steady
states of the aggregated digraph. The source's weak reversibility (every weak component of the
reaction digraph is strongly connected) is equivalent to every reaction lying on a directed cycle.
Finiteness of the set of positive steady states in a class is not claimed. The deficiency-zero
special case is proved in `Domains.Biology.Dynamics.DeficiencyZero.Integration` for networks
with natural-number coefficients. The network, its stoichiometric subspace, weak reversibility
and mass-action field are the shared definitions of
`MathlibExt.Dynamics.PolynomialNetworks.RealExponent`, also used by the permanence theorems of
`WantedExt.Biology.Biophysics.StronglyEndotacticPermanenceWanted`.

Sources: B. Boros, "Existence of positive steady states for weakly reversible mass-action
systems", SIAM J. Math. Anal. 51 (2019) 435–449, Theorem 1 (arXiv:1710.04732, Section 4).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Dynamics.PolynomialNetworks.RealExponent

@[expose] public section

namespace WantedExt.Biology.Biophysics.WeaklyReversiblePositiveSteadyStateWanted

open MathlibExt.Biology.Dynamics

/-- **Boros's existence theorem** (Boros 2019, Theorem 1). Let `N` be a weakly reversible
reaction network with real stoichiometric coefficients and finitely many species and reactions,
let `k` be positive rate constants and let `x₀` be a positive state. Then the positive
stoichiometric class of `x₀` contains a positive steady state of the mass-action system: there is
`x` with all coordinates positive, `x - x₀` in the stoichiometric subspace and
`massActionField k x = 0`.

Source: B. Boros, SIAM J. Math. Anal. 51 (2019) 435–449, Theorem 1. -/
theorem_wanted exists_pos_steadyState_mem_class {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : RealExponentNetwork S ρ) (hwr : N.IsWeaklyReversible) {k : ρ → ℝ}
    (hk : ∀ r, 0 < k r) {x₀ : S → ℝ} (hx₀ : ∀ s, 0 < x₀ s) :
    ∃ x : S → ℝ, (∀ s, 0 < x s) ∧ x - x₀ ∈ N.stoichiometricSubspace ∧
      N.massActionField k x = 0

end WantedExt.Biology.Biophysics.WeaklyReversiblePositiveSteadyStateWanted
