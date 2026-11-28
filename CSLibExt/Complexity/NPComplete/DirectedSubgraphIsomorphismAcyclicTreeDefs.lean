/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED SUBGRAPH ISOMORPHISM (G acyclic, H a directed tree): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT48] SUBGRAPH ISOMORPHISM, comment:
"Variant for directed graphs is also NP-complete, even if G is acyclic and H is a directed tree
[Aho and Sethi, 1977]" (A. V. Aho and R. Sethi, 1977, as cited there; the original was not
available).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedSubgraphIsomorphismAcyclicTree

/-- An instance: the vertex count and arc list of `G`, then the vertex count and arc list of
`H`. -/
abbrev DirectedSubgraphIsomorphismAcyclicTreeInstance :=
  ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)

/-- An arc list on `0, …, n - 1`: no repeated arcs, endpoints below `n`, no loops. -/
def IsArcList (n : ℕ) (A : List (ℕ × ℕ)) : Prop :=
  A.Nodup ∧ ∀ a ∈ A, a.1 < n ∧ a.2 < n ∧ a.1 ≠ a.2

/-- Well-formedness of an instance: both lists are arc lists on their vertex sets (`IsArcList`:
no repeated ordered pair, endpoints in range, no loops), `G` is acyclic (a permutation of its
vertices along which every arc goes forward), and `H` is a directed tree (no antiparallel arcs,
and the underlying undirected graph is a tree). -/
def WellFormed (i : DirectedSubgraphIsomorphismAcyclicTreeInstance) : Prop :=
  IsArcList i.1 i.2.1 ∧ IsArcList i.2.2.1 i.2.2.2 ∧
    (∃ order : List ℕ, order.Perm (List.range i.1) ∧
      ∀ a ∈ i.2.1, order.idxOf a.1 < order.idxOf a.2) ∧
    (∀ a ∈ i.2.2.2, (a.2, a.1) ∉ i.2.2.2) ∧
    (Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2).IsTree

/-- `G` contains a subgraph isomorphic to `H`: a one-to-one map `f` from the vertices `Fin n₂` of
`H` to the vertices `Fin n₁` of `G` such that, for every entry `(u, v)` of the arc list of `H`
with both ends below `n₂`, the pair `(f u, f v)` is an entry of the arc list of `G`. An entry of
the arc list of `H` with an end at least `n₂` imposes nothing; under `WellFormed` there is none. -/
def DirectedSubgraphIsomorphismAcyclicTreeFeasible
    (i : DirectedSubgraphIsomorphismAcyclicTreeInstance) : Prop :=
  ∃ f : Fin i.2.2.1 → Fin i.1, Function.Injective f ∧
    ∀ a ∈ i.2.2.2, ∀ (h₁ : a.1 < i.2.2.1) (h₂ : a.2 < i.2.2.1),
      (((f ⟨a.1, h₁⟩ : ℕ), (f ⟨a.2, h₂⟩ : ℕ)) ∈ i.2.1)

open Classical in
/-- DIRECTED SUBGRAPH ISOMORPHISM (G acyclic, H a directed tree) as a decision problem over
bitstrings. -/
noncomputable def directedSubgraphIsomorphismAcyclicTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedSubgraphIsomorphismAcyclicTreeInstance) x with
  | some i => decide (WellFormed i ∧ DirectedSubgraphIsomorphismAcyclicTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DirectedSubgraphIsomorphismAcyclicTree
