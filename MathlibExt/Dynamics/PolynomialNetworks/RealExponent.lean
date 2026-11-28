/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Relation

/-!
# Reaction networks with real stoichiometric coefficients

A reaction network with real exponents has reactions `r` turning a source complex
`src r : S → ℝ` into a product complex `prod r : S → ℝ`. Such networks arise in generalized
mass-action kinetics and in the geometric study of persistence and permanence, where complexes
are arbitrary real points. This file gives the shared vocabulary: the reaction vectors and the
stoichiometric subspace, the complexes, the directed reaction relation, weak reversibility, and
the mass-action vector field with real powers.

`MathlibExt.Dynamics.PolynomialNetworks.Deficiency` is the natural-number counterpart, used for
chemical networks with integer stoichiometry.

## Main definitions

* `RealExponentNetwork S ρ`: reactions `src r → prod r` with complexes in `S → ℝ`;
* `reactionVector r`: `prod r - src r`;
* `stoichiometricSubspace`: the span of the reaction vectors;
* `complexes`: the sources and products of the reactions;
* `Reacts y y'`: some reaction has source `y` and product `y'`;
* `IsWeaklyReversible`: every reaction `y → y'` has a directed path of reactions back from `y'`
  to `y`;
* `massActionField k x`: for finite species (`[Fintype S]`) and finite reactions (`[Fintype ρ]`),
  `∑_{r : ρ} k r (∏_{s : S} x_s ^ (src r s)) (prod r - src r)` with real powers, meant for
  positive states `x`.

## References

* M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019).
* B. Boros, "Existence of positive steady states for weakly reversible mass-action systems",
  SIAM J. Math. Anal. 51 (2019) 435–449.
* M. Gopalkrishnan, E. Miller and A. Shiu, "A geometric approach to the global attractor
  conjecture", SIAM J. Appl. Dyn. Syst. 13 (2014) 758–797.
-/

@[expose] public section

namespace MathlibExt.Biology.Dynamics

/-- A reaction network on the species `S` with reactions indexed by `ρ` and real stoichiometric
coefficients: reaction `r` turns the source complex `src r` into the product complex `prod r`. -/
structure RealExponentNetwork (S ρ : Type*) where
  /-- The source (reactant) complex of each reaction. -/
  src : ρ → S → ℝ
  /-- The product complex of each reaction. -/
  prod : ρ → S → ℝ

namespace RealExponentNetwork

variable {S ρ : Type*} (N : RealExponentNetwork S ρ)

/-- The reaction vector `prod r - src r` of the reaction `r`. -/
def reactionVector (r : ρ) : S → ℝ :=
  N.prod r - N.src r

/-- The stoichiometric subspace: the span of the reaction vectors `prod r - src r`. -/
def stoichiometricSubspace : Submodule ℝ (S → ℝ) :=
  Submodule.span ℝ (Set.range N.reactionVector)

/-- The complexes of the network: the sources and products of its reactions. -/
def complexes : Set (S → ℝ) :=
  Set.range N.src ∪ Set.range N.prod

/-- The directed reaction relation on complexes: `y ⟶ y'` if some reaction has source `y` and
product `y'`. -/
def Reacts (y y' : S → ℝ) : Prop :=
  ∃ r, N.src r = y ∧ N.prod r = y'

/-- The network is weakly reversible: for every reaction `y → y'` there is a directed path of
reactions from `y'` back to `y`. -/
def IsWeaklyReversible : Prop :=
  ∀ r, Relation.ReflTransGen N.Reacts (N.prod r) (N.src r)

/-- For a network with finite species set `S` (`[Fintype S]`) and finite reaction set `ρ`
(`[Fintype ρ]`), the mass-action vector field with rate constants `k`, using real powers:
`x ↦ ∑_{r : ρ} k r (∏_{s : S} x_s ^ (src r s)) (prod r - src r)`. It is meant for positive states
`x`. -/
noncomputable def massActionField [Fintype S] [Fintype ρ] (k : ρ → ℝ) (x : S → ℝ) : S → ℝ :=
  ∑ r, (k r * ∏ s, x s ^ N.src r s) • N.reactionVector r

end RealExponentNetwork

end MathlibExt.Biology.Dynamics
