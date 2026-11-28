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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.InducedSubgraphWithPropertyPiDefs

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
