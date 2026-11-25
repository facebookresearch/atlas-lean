/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Relation

/-!
# The graph and vector field of a polynomial network

An indexed pair of nonnegative integer exponent vectors specifies each directed edge.
Its displacement vectors span a real subspace and its source monomials give a polynomial
vector field. The difference between the graph rank and the dimension of this subspace
is the deficiency. Both equilibrium statements and graph calculations use these definitions.

See M. Feinberg, *Foundations of Chemical Reaction Network Theory* (2019), chapters 3 and 6.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.Dynamics.ComplexBalanced

variable {S ρ : Type*}

/-- A chemical reaction network on the species `S` with reactions indexed by `ρ`: reaction `r`
turns the source complex `src r` into the product complex `prod r` (stoichiometric
coefficients). -/
structure ReactionNetwork (S ρ : Type*) where
  /-- The source (reactant) complex of each reaction. -/
  src : ρ → S → ℕ
  /-- The product complex of each reaction. -/
  prod : ρ → S → ℕ

namespace ReactionNetwork

variable (N : ReactionNetwork S ρ)

/-- The stoichiometric subspace: the span of the reaction vectors `prod r - src r`. -/
def stoichiometricSubspace : Submodule ℝ (S → ℝ) :=
  Submodule.span ℝ (Set.range fun r s => (N.prod r s : ℝ) - N.src r s)

/-- The mass-action vector field with rate constants `k`:
`x ↦ ∑_r k r (∏_s x_s ^ (src r s)) (prod r - src r)`. -/
noncomputable def massActionField [Fintype S] [Fintype ρ] (k : ρ → ℝ) (x : S → ℝ) :
    S → ℝ :=
  fun s => ∑ r, k r * (∏ s', x s' ^ N.src r s') * ((N.prod r s : ℝ) - N.src r s)

/-- The complexes of the network: the sources and products of its reactions.

Source: Feinberg (1987), §2; Feinberg (2019), Def. 3.1.1. -/
def complexes : Set (S → ℕ) :=
  Set.range N.src ∪ Set.range N.prod

/-- The directed reaction relation on complexes: `y ⟶ y'` if some reaction has source `y` and
product `y'`.

Source: Feinberg (2019), §3.1. -/
def Reacts (y y' : S → ℕ) : Prop :=
  ∃ r, N.src r = y ∧ N.prod r = y'

/-- The undirected reaction graph on the complexes: distinct complexes are adjacent when one
reacts to the other.

Source: Feinberg (1987), §2.2 (the standard reaction diagram, undirected). -/
def linkageGraph : SimpleGraph N.complexes :=
  SimpleGraph.fromRel fun c c' => N.Reacts c c'

/-- The number of linkage classes of a network with finitely many complexes: connected
components of the undirected reaction graph.

Source: Feinberg (1987), §2.2; Feinberg (2019), Def. 3.1.4. -/
noncomputable def numLinkageClasses [Finite N.complexes] : ℕ :=
  Nat.card N.linkageGraph.ConnectedComponent

/-- The deficiency `δ = n - ℓ - s` (number of complexes, linkage classes, dimension of the
stoichiometric subspace) of a network with finitely many complexes.

Source: Feinberg (1987), §3; Feinberg (2019), Def. 6.1.1. -/
noncomputable def deficiency [Finite N.complexes] : ℤ :=
  (Nat.card N.complexes : ℤ) - N.numLinkageClasses -
    Module.finrank ℝ N.stoichiometricSubspace

/-- The network is weakly reversible: for every reaction `y → y'` there is a directed path of
reactions from `y'` back to `y`.

Source: Feinberg (1987), §2.4; Feinberg (2019), Def. 3.4.1. -/
def IsWeaklyReversible : Prop :=
  ∀ r, Relation.ReflTransGen N.Reacts (N.prod r) (N.src r)

variable {N}

theorem finite_complexes [Finite ρ] : N.complexes.Finite :=
  (Set.finite_range _).union (Set.finite_range _)

instance [Finite ρ] : Finite N.complexes :=
  N.finite_complexes.to_subtype

end ReactionNetwork

end MathlibExt.Biology.Dynamics.ComplexBalanced
