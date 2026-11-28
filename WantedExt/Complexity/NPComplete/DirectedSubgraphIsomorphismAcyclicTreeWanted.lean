/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED SUBGRAPH ISOMORPHISM (G acyclic, H a directed tree) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT48] SUBGRAPH ISOMORPHISM, comment:
"Variant for directed graphs is also NP-complete, even if G is acyclic and H is a directed tree
[Aho and Sethi, 1977]" (A. V. Aho and R. Sethi, 1977, as cited there; the original was not
available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedSubgraphIsomorphismAcyclicTree

/-!
# DIRECTED SUBGRAPH ISOMORPHISM (G acyclic, H a directed tree) is NP-complete

INSTANCE: directed graphs `G = (V₁, A₁)` and `H = (V₂, A₂)`, where `G` is acyclic and `H` is a
directed tree.
QUESTION: does `G` contain a subgraph isomorphic to `H`, i.e., a subset `V ⊆ V₁` and a subset
`A ⊆ A₁` with `|V| = |V₂|`, `|A| = |A₂|`, and a one-to-one function `f : V₂ → V` with
`(u, v) ∈ A₂` if and only if `(f(u), f(v)) ∈ A`?

This is the directed variant of SUBGRAPH ISOMORPHISM ([GT48], `SubgraphIsomorphismWanted`) under
the restriction printed in Garey and Johnson's comment, attributed to Aho and Sethi. Taking `A`
to be the image of `A₂`, the question is equivalent to: there is a one-to-one `f : V₂ → V₁` such
that `(f(u), f(v)) ∈ A₁` for every arc `(u, v) ∈ A₂`.

The vertices of `G` are `0, …, n₁ - 1` and those of `H` are `0, …, n₂ - 1`; arcs are lists of
ordered pairs without repetitions or loops. "Acyclic" (no directed cycle) is stated as the
existence of a topological order: a permutation of the vertices of `G` along which every arc of
`G` goes forward. "Directed tree" is read as in Garey and Johnson, who say "rooted directed
tree" when they mean one ([GT41]): a directed graph whose underlying undirected graph is a tree
(Mathlib's `SimpleGraph.IsTree` of `Cslib.Complexity.Karp.edgeGraph` on the arcs, with no pair
of antiparallel arcs, so that each tree edge carries exactly one arc).

Membership in NP: the map `f` is a certificate; acyclicity and the tree condition are checked in
polynomial time. `H` has `n₂ ≥ 1` vertices (a tree is nonempty), so `n₂` is at most the length of
its arc list plus one; vertices of `G` outside its arc list are isolated and cannot carry an arc
of `H`, so a certificate uses only the vertices of `G` on arcs, apart from the single vertex of a
one-vertex `H`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **DIRECTED SUBGRAPH ISOMORPHISM (G acyclic, H a directed tree) is NP-complete.** Source:
Garey and Johnson (1979), [GT48]; Aho and Sethi (1977). -/
public theorem_wanted directedSubgraphIsomorphismAcyclicTree_npComplete :
    directedSubgraphIsomorphismAcyclicTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedSubgraphIsomorphismAcyclicTreeDec

end MetaMathlibExt.Complexity.NPComplete.DirectedSubgraphIsomorphismAcyclicTree
