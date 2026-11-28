/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear triple systems: definitions
-/
module

public import Mathlib.Data.Finset.Card

/-!
# Linear triple systems: definitions

Linear triple systems (`IsLinearTripleSystem`): families of three-element sets any two distinct
members of which share at most one element, also called `3`-uniform linear hypergraphs or partial
Steiner triple systems. This is the definition that the statements of
`WantedExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted`, and of the wanted
modules built on it, use, moved here unchanged (name included) so that their proofs can import it.

Source: T. F. Bloom, Erdős Problems, Problem #1024, https://www.erdosproblems.com/1024.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted

/-- **Linear triple systems.** A finite family $H$ of subsets of $\{0, \dots, n-1\}$ is a linear
triple system (a $3$-uniform linear hypergraph, or partial Steiner triple system) when every
member of $H$ has exactly three elements and any two distinct members of $H$ share at most one
element. -/
def IsLinearTripleSystem {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ H, e.card = 3) ∧ ∀ e ∈ H, ∀ e' ∈ H, e ≠ e' → (e ∩ e').card ≤ 1

end MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted
