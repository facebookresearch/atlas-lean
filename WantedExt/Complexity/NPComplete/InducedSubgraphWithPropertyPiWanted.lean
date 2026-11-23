/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED SUBGRAPH WITH PROPERTY Π is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT21] INDUCED
SUBGRAPH WITH PROPERTY Π;
J. M. Lewis and M. Yannakakis, "The node-deletion problem for hereditary
properties is NP-complete", Journal of Computer and System Sciences 20 (1980),
219-230, doi:10.1016/0022-0000(80)90060-4;
V. Raman and S. Sikdar, "Parameterized complexity of the induced subgraph
problem in directed graphs", Information Processing Letters 104 (2007), 79-85,
doi:10.1016/j.ipl.2007.05.005 (Section 2 restates the Lewis-Yannakakis theorem:
NP-hard for every nontrivial hereditary property, NP-complete when the property
can moreover be tested in polynomial time).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedSubgraphWithPropertyPi

/-!
# INDUCED SUBGRAPH WITH PROPERTY Π is NP-complete

For a fixed graph property `Π` that is hereditary (closed under induced subgraphs) and
nontrivial (true for infinitely many graphs and false for infinitely many graphs):
INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: is there a subset
`V' ⊆ V` with `|V'| ≥ K` such that the subgraph of `G` induced by `V'` has property `Π`?
The problem is NP-hard for every such `Π`, and NP-complete when `Π` can be tested in
polynomial time; the theorem states the NP-complete case. `Π` is written `Φ` in Lean, where
`Π` is reserved syntax.

A graph property is a predicate on the graphs `SimpleGraph (Fin m)`, one for each vertex count
`m`. For an injective map `f : Fin m ↪ Fin n`, `G.comap f` is the subgraph of `G` induced by the
range of `f`, numbered by `f`; so "the subgraph induced by `V'` has `Π`" is `Φ m (G.comap f)`
for an `f` with range `V'` and `|V'| = m`. Closing `Φ` under every such `comap` (`IsHereditary`)
says that `Φ` is hereditary and, taking `f` bijective, invariant under isomorphism, as a graph
property must be. Because there are finitely many graphs on each `Fin m`, "true for infinitely
many graphs" means true for graphs of arbitrarily large size, and likewise for "false"
(`IsNontrivial`). "Tested in polynomial time" is membership of `propertyDec Φ`, the property as
a decision problem on encoded graphs, in `MetaMathlibExt.ComplexityTheory.P`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A graph property: a predicate on the simple graphs on `Fin m`, for each vertex count `m`. -/
abbrev GraphProperty := ∀ m : ℕ, SimpleGraph (Fin m) → Prop

/-- `Φ` is hereditary: whenever a graph has `Φ`, so does each of its induced subgraphs, in every
numbering of its vertices (`G.comap f` for an injective `f : Fin m ↪ Fin n`). -/
def IsHereditary (Φ : GraphProperty) : Prop :=
  ∀ ⦃m n : ℕ⦄ (G : SimpleGraph (Fin n)) (f : Fin m ↪ Fin n), Φ n G → Φ m (G.comap f)

/-- `Φ` is nontrivial: it holds for graphs of arbitrarily large size and fails for graphs of
arbitrarily large size. -/
def IsNontrivial (Φ : GraphProperty) : Prop :=
  (∀ m, ∃ n, m ≤ n ∧ ∃ G : SimpleGraph (Fin n), Φ n G) ∧
    ∀ m, ∃ n, m ≤ n ∧ ∃ G : SimpleGraph (Fin n), ¬ Φ n G

/-- A simple edge list on `Fin n`: no duplicate edges in either orientation, no self-loops,
endpoints in range. -/
def SimpleEdgeList (n : ℕ) (es : List (ℕ × ℕ)) : Prop :=
  es.Nodup ∧ ∀ e ∈ es, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ es

open Classical in
/-- The property `Φ` as a decision problem over bitstrings: an encoded graph (vertex count and
simple edge list) is a yes-instance when it has `Φ`. -/
noncomputable def propertyDec (Φ : GraphProperty) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ × List (ℕ × ℕ)) x with
  | some g => decide (SimpleEdgeList g.1 g.2 ∧ Φ g.1 (Cslib.Complexity.Karp.edgeGraph g.1 g.2))
  | none => false

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev InducedSubgraphWithPropertyPiInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : InducedSubgraphWithPropertyPiInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, and
`0 < K ≤ |V|`. -/
def WellFormed (i : InducedSubgraphWithPropertyPiInstance) : Prop :=
  SimpleEdgeList i.1 i.2.1 ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at least `K` vertices induces a subgraph with property `Φ`: for some `m ≥ K`
and some injective `f : Fin m ↪ Fin n`, the subgraph induced by the range of `f` has `Φ`. -/
def InducedSubgraphWithPropertyPiFeasible (Φ : GraphProperty)
    (i : InducedSubgraphWithPropertyPiInstance) : Prop :=
  ∃ m, i.2.2 ≤ m ∧ ∃ f : Fin m ↪ Fin i.1, Φ m ((Graph i).comap f)

open Classical in
/-- INDUCED SUBGRAPH WITH PROPERTY `Φ` as a decision problem over bitstrings. -/
noncomputable def inducedSubgraphWithPropertyPiDec (Φ : GraphProperty) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InducedSubgraphWithPropertyPiInstance) x with
  | some i => decide (WellFormed i ∧ InducedSubgraphWithPropertyPiFeasible Φ i)
  | none => false

/-- **INDUCED SUBGRAPH WITH PROPERTY Π is NP-complete** for every hereditary, nontrivial
property `Π` that can be tested in polynomial time. Source: Garey and Johnson (1979), [GT21];
Lewis and Yannakakis (1980). -/
public theorem_wanted inducedSubgraphWithPropertyPi_npComplete (Φ : GraphProperty)
    (hHer : IsHereditary Φ) (hNontriv : IsNontrivial Φ)
    (hPoly : propertyDec Φ ∈ MetaMathlibExt.ComplexityTheory.P) :
    inducedSubgraphWithPropertyPiDec Φ ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (inducedSubgraphWithPropertyPiDec Φ)

end MetaMathlibExt.Complexity.NPComplete.InducedSubgraphWithPropertyPi
