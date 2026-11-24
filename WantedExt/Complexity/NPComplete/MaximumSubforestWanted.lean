/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM SUBFOREST is NP-complete

Source:
R. Shamir and D. Tsur, "The maximum subforest problem: approximation and exact algorithms",
Proceedings of the Ninth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 1998), 394-399,
doi:10.5555/314613.314769 (Section 1: the maximum subforest problem MSP; Section 1.1: "We show
that MSP is NP-hard");
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry MAXIMUM
SUBFOREST;
A. Abboud, A. Backurs, T. D. Hansen, V. Vassilevska Williams and O. Zamir, "Subtree isomorphism
revisited", ACM Transactions on Algorithms 14(3) (2018), 1-23, doi:10.1145/3093239 (subtree
isomorphism, used for membership in NP).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.InducedSubgraphWithPropertyPiWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumSubforest

open InducedSubgraphWithPropertyPi (SimpleEdgeList)

/-!
# MAXIMUM SUBFOREST is NP-complete

INSTANCE: a tree `G = (V, E)`, a set `H` of trees, and a positive integer `K`.
QUESTION: is there a subset `E' ⊆ E` with `|E'| ≥ K` such that the subgraph `G' = (V, E')`
does not contain any subtree isomorphic to a tree from `H`?

This is the decision version of Shamir and Tsur's maximum subforest problem ("Given a tree `G`
and a set of trees `H`, find a subgraph `G'` of `G` such that `G'` does not contain a subtree
isomorphic to a tree from `H`, and the number of edges in `G'` is maximum"), in the form of the
Crescenzi-Kann compendium entry MAXIMUM SUBFOREST. Shamir and Tsur write `T ⊆ G'` when the tree
`T` is isomorphic to a subgraph of `G'`, and call `G'` `H`-free when no tree of `H` is; since a
tree's copy in `G'` is a subtree of `G'`, this is Mathlib's `SimpleGraph.Free`: `T.Free G'` says
that `G'` contains no copy of `T` (`SimpleGraph.Copy`, an injective edge-preserving map).
Shamir and Tsur show that MSP is NP-hard (Section 1.1). Membership in NP: the edge set `E'` is a
certificate, and whether a tree occurs in a tree (subtree isomorphism; see Abboud et al.) is
decided in polynomial time, so `H`-freeness of each component of `G'` is checked in polynomial
time.

Graphs are given by vertex counts and simple edge lists
(`InducedSubgraphWithPropertyPi.SimpleEdgeList`), as `Cslib.Complexity.Karp.edgeGraph` on
`Fin n`; trees are Mathlib's `SimpleGraph.IsTree` (connected, which needs a vertex, and
acyclic). `H` is a list of trees `(m, edges)`. The subset `E'` is a sublist of the edge list of
`G`, which has no duplicates, so its length is `|E'|`. The vertex counts are binary numbers, but
a tree has one vertex more than edges, so they are bounded by the input length. `K` uses the
canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertex count `n` and edge list of the tree `G`, the trees of `H` (each a
vertex count and an edge list), and the bound `K`. -/
abbrev MaximumSubforestInstance :=
  ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ)) × ℕ

/-- Well-formedness of an instance: `G` and every tree of `H` are simple graphs that are trees,
and `0 < K`. -/
def WellFormed (i : MaximumSubforestInstance) : Prop :=
  SimpleEdgeList i.1 i.2.1 ∧ (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsTree ∧
    (∀ T ∈ i.2.2.1, SimpleEdgeList T.1 T.2 ∧ (Cslib.Complexity.Karp.edgeGraph T.1 T.2).IsTree) ∧
    0 < i.2.2.2

/-- Some subset `E'` of at least `K` edges of `G` spans a subgraph `(V, E')` containing no copy
of a tree of `H`. -/
def MaximumSubforestFeasible (i : MaximumSubforestInstance) : Prop :=
  ∃ E' : List (ℕ × ℕ), E'.Sublist i.2.1 ∧ i.2.2.2 ≤ E'.length ∧
    ∀ T ∈ i.2.2.1,
      (Cslib.Complexity.Karp.edgeGraph T.1 T.2).Free (Cslib.Complexity.Karp.edgeGraph i.1 E')

open Classical in
/-- MAXIMUM SUBFOREST as a decision problem over bitstrings. -/
noncomputable def maximumSubforestDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumSubforestInstance) x with
  | some i => decide (WellFormed i ∧ MaximumSubforestFeasible i)
  | none => false

/-- **MAXIMUM SUBFOREST is NP-complete.** Source: Shamir and Tsur (1998), Section 1.1
(hardness); membership in NP as in the module docstring. -/
public theorem_wanted maximumSubforest_npComplete :
    maximumSubforestDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumSubforestDec

end MetaMathlibExt.Complexity.NPComplete.MaximumSubforest
