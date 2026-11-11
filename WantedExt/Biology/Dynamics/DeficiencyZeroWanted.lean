/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The deficiency-zero theorem for mass-action reaction networks

A chemical reaction network on a finite set `S` of species is a finite family of reactions
`r : ρ`, each turning a source complex `src r : S → ℕ` into a product complex `prod r : S → ℕ`
(stoichiometric coefficients). Its complexes are the sources and products, its reaction graph
has an edge `src r → prod r` for each reaction, and its linkage classes are the connected
components of the undirected reaction graph (`numLinkageClasses`). The stoichiometric subspace
is the span of the reaction vectors `prod r - src r` in `S → ℝ` (`stoichiometricSubspace`).
The **deficiency** is `δ = n - ℓ - s`, where `n` is the number of complexes, `ℓ` the number of
linkage classes and `s` the dimension of the stoichiometric subspace (`deficiency`). The network
is **weakly reversible** if for every reaction `y → y'` there is a directed path of reactions
from `y'` back to `y`.

With positive rate constants `k`, mass-action kinetics gives the polynomial system
`ẋ = ∑_r k r x^{src r} (prod r - src r)`, where `x^y = ∏_s x_s ^ y_s` (`massActionField`).
A positive stoichiometric compatibility class is `(x₀ + span) ∩ ℝ_{>0}^S` for a positive
`x₀`.

**Deficiency-zero theorem** (Horn 1972, Feinberg 1972, Horn–Jackson 1972; Feinberg 1987).
Let the network have deficiency zero.
* If it is weakly reversible, then for every choice of positive rate constants each positive
  stoichiometric compatibility class contains exactly one equilibrium of the mass-action system.
* If it is not weakly reversible, then for no choice of positive rate constants does the
  mass-action system have a positive equilibrium.

Feinberg's theorem also asserts that the equilibrium in the weakly reversible case is complex
balanced (stated here as `exists_pos_isComplexBalanced`) and locally asymptotically stable, and
the second part holds for arbitrary kinetics; stability and general kinetics are not stated
here. The reaction networks, the stoichiometric subspace, the mass-action vector field and
complex balancing are defined in `MathlibExt.Biology.Dynamics.ComplexBalanced`, which also
proves the Horn–Jackson theorem: given one positive complex-balanced equilibrium, each positive
stoichiometric compatibility class contains exactly one positive equilibrium.

Sources: M. Feinberg, "Chemical reaction network structure and the stability of complex
isothermal reactors — I. The deficiency zero and deficiency one theorems", Chem. Eng. Sci. 42
(1987) 2229–2268; F. Horn, "Necessary and sufficient conditions for complex balancing in
chemical kinetics", Arch. Rational Mech. Anal. 49 (1972) 172–186; F. Horn and R. Jackson,
"General mass action kinetics", Arch. Rational Mech. Anal. 47 (1972) 81–116; M. Feinberg,
"Complex balancing in general kinetic systems", Arch. Rational
Mech. Anal. 49 (1972) 187–194; M. Feinberg, *Foundations of Chemical Reaction Network Theory*
(2019).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Biology.Dynamics.ComplexBalanced
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Logic.Relation

@[expose] public section

-- The extension declarations live in the namespace of `ReactionNetwork` so that dot notation
-- (`N.deficiency`) resolves.
namespace MathlibExt.Biology.Dynamics.ComplexBalanced

variable {S ρ : Type*}

namespace ReactionNetwork

variable (N : ReactionNetwork S ρ)

/-- The complexes of the network: the sources and products of its reactions. -/
def complexes : Set (S → ℕ) :=
  Set.range N.src ∪ Set.range N.prod

/-- The directed reaction relation on complexes: `y ⟶ y'` if some reaction has source `y` and
product `y'`. -/
def Reacts (y y' : S → ℕ) : Prop :=
  ∃ r, N.src r = y ∧ N.prod r = y'

/-- The undirected reaction graph on the complexes: distinct complexes are adjacent when one
reacts to the other. -/
def linkageGraph : SimpleGraph N.complexes :=
  SimpleGraph.fromRel fun c c' => N.Reacts c c'

/-- The number of linkage classes: connected components of the undirected reaction graph. -/
noncomputable def numLinkageClasses : ℕ :=
  Nat.card N.linkageGraph.ConnectedComponent

/-- The deficiency `δ = n - ℓ - s` (number of complexes, linkage classes, dimension of the
stoichiometric subspace). -/
noncomputable def deficiency : ℤ :=
  (Nat.card N.complexes : ℤ) - N.numLinkageClasses -
    Module.finrank ℝ N.stoichiometricSubspace

/-- The network is weakly reversible: for every reaction `y → y'` there is a directed path of
reactions from `y'` back to `y`. -/
def IsWeaklyReversible : Prop :=
  ∀ r, Relation.ReflTransGen N.Reacts (N.prod r) (N.src r)

/-- **Horn–Feinberg: complex balancing for every choice of rate constants.** A weakly
reversible mass-action network of deficiency zero has, for any positive rate constants, a
positive complex-balanced equilibrium. Together with
`existsUnique_equilibrium_of_isComplexBalanced` this gives `existsUnique_equilibrium`.

Source: Horn (1972); Feinberg (1972); Feinberg (1987). -/
theorem_wanted exists_pos_isComplexBalanced [Fintype S] [Fintype ρ] (hδ : N.deficiency = 0)
    (hwr : N.IsWeaklyReversible) {k : ρ → ℝ} (hk : ∀ r, 0 < k r) :
    ∃ c : S → ℝ, (∀ s, 0 < c s) ∧ N.IsComplexBalanced k c

/-- **Deficiency-zero theorem, weakly reversible case.** A weakly reversible mass-action
network of deficiency zero has, for any positive rate constants, exactly one equilibrium in
each positive stoichiometric compatibility class.

Source: Horn (1972); Horn & Jackson (1972); Feinberg (1987). -/
theorem_wanted existsUnique_equilibrium [Fintype S] [Fintype ρ] (hδ : N.deficiency = 0)
    (hwr : N.IsWeaklyReversible) {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {x₀ : S → ℝ} (hx₀ : ∀ s, 0 < x₀ s) :
    ∃! x : S → ℝ, (∀ s, 0 < x s) ∧ x - x₀ ∈ N.stoichiometricSubspace ∧
      N.massActionField k x = 0

/-- **Deficiency-zero theorem, non-weakly-reversible case.** A mass-action network of
deficiency zero that is not weakly reversible has no positive equilibrium for any positive
rate constants.

Source: Feinberg (1987). -/
theorem_wanted not_exists_positive_equilibrium [Fintype S] [Fintype ρ]
    (hδ : N.deficiency = 0) (hwr : ¬ N.IsWeaklyReversible)
    {k : ρ → ℝ} (hk : ∀ r, 0 < k r) :
    ¬ ∃ x : S → ℝ, (∀ s, 0 < x s) ∧ N.massActionField k x = 0

end ReactionNetwork

end MathlibExt.Biology.Dynamics.ComplexBalanced
