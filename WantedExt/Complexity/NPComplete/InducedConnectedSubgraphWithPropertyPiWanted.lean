/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED CONNECTED SUBGRAPH WITH PROPERTY Π is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT22] INDUCED CONNECTED SUBGRAPH
WITH PROPERTY Π;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proc. 10th ACM Symposium on
Theory of Computing (STOC 1978), 253-264, doi:10.1145/800133.804355;
M. Yannakakis, "The effect of a connectivity requirement on the complexity of maximum subgraph
problems", Journal of the ACM 26 (1979), 618-630, doi:10.1145/322154.322157.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import WantedExt.Complexity.NPComplete.InducedSubgraphWithPropertyPiWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedConnectedSubgraphWithPropertyPi

open MetaMathlibExt.Complexity.NPComplete.InducedSubgraphWithPropertyPi

/-!
# INDUCED CONNECTED SUBGRAPH WITH PROPERTY Π is NP-complete

For a fixed hereditary graph property `Π` that holds for arbitrarily large connected graphs but
not for all connected graphs: INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is there a subset `V' ⊆ V` with `|V'| ≥ K` such that the subgraph of `G` induced by
`V'` is connected and has property `Π`?

Garey and Johnson, [GT22], comment: "NP-hard for any hereditary property that holds for
arbitrarily large connected graphs but not for all connected graphs. If, in addition, one can
determine in polynomial time whether `Π` holds for a graph, then the problem is NP-complete."
The theorem states the NP-complete case. Crescenzi and Kann's [GT30] MINIMUM VERTEX DELETION TO
OBTAIN CONNECTED SUBGRAPH WITH PROPERTY P is the same question with the deleted set
`V - V'` bounded by `|V| - K`.

The instance, its graph and well-formedness (a simple edge list and `0 < K ≤ |V|`), graph
properties (`GraphProperty`, a predicate on the graphs `SimpleGraph (Fin m)` for each `m`),
heredity (`IsHereditary`: closed under induced subgraphs `G.comap f` for injective `f`, which
includes isomorphism invariance) and polynomial-time testability (`propertyDec Φ ∈ P`) are those
of INDUCED SUBGRAPH WITH PROPERTY Π
(`WantedExt.Complexity.NPComplete.InducedSubgraphWithPropertyPiWanted`), reused unchanged. `Π` is
written `Φ` in Lean, where `Π` is reserved syntax. The subgraph induced by `V'`, numbered by an
injective `f : Fin m ↪ Fin n` with range `V'`, is `G.comap f`, and "connected" is Mathlib's
`SimpleGraph.Connected` (which requires a vertex; here `m ≥ K ≥ 1`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `Φ` holds for arbitrarily large connected graphs but not for all connected graphs. -/
def IsConnectedNontrivial (Φ : GraphProperty) : Prop :=
  (∀ m, ∃ n, m ≤ n ∧ ∃ G : SimpleGraph (Fin n), G.Connected ∧ Φ n G) ∧
    ∃ n, ∃ G : SimpleGraph (Fin n), G.Connected ∧ ¬ Φ n G

/-- Some set of at least `K` vertices induces a connected subgraph with property `Φ`: for some
`m ≥ K` and some injective `f : Fin m ↪ Fin n`, the subgraph induced by the range of `f` is
connected and has `Φ`. -/
def InducedConnectedSubgraphWithPropertyPiFeasible (Φ : GraphProperty)
    (i : InducedSubgraphWithPropertyPiInstance) : Prop :=
  ∃ m, i.2.2 ≤ m ∧ ∃ f : Fin m ↪ Fin i.1,
    ((Graph i).comap f).Connected ∧ Φ m ((Graph i).comap f)

open Classical in
/-- INDUCED CONNECTED SUBGRAPH WITH PROPERTY `Φ` as a decision problem over bitstrings. -/
noncomputable def inducedConnectedSubgraphWithPropertyPiDec (Φ : GraphProperty) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InducedSubgraphWithPropertyPiInstance) x with
  | some i => decide (WellFormed i ∧ InducedConnectedSubgraphWithPropertyPiFeasible Φ i)
  | none => false

/-- **INDUCED CONNECTED SUBGRAPH WITH PROPERTY Π is NP-complete** for every hereditary property
`Π` that holds for arbitrarily large connected graphs but not for all connected graphs and can
be tested in polynomial time. Source: Garey and Johnson (1979), [GT22]; Yannakakis (1978,
1979). -/
public theorem_wanted inducedConnectedSubgraphWithPropertyPi_npComplete (Φ : GraphProperty)
    (hHer : IsHereditary Φ) (hNontriv : IsConnectedNontrivial Φ)
    (hPoly : propertyDec Φ ∈ MetaMathlibExt.ComplexityTheory.P) :
    inducedConnectedSubgraphWithPropertyPiDec Φ ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (inducedConnectedSubgraphWithPropertyPiDec Φ)

end MetaMathlibExt.Complexity.NPComplete.InducedConnectedSubgraphWithPropertyPi
