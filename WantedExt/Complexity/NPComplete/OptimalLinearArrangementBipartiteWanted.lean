/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL LINEAR ARRANGEMENT for bipartite graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT42] OPTIMAL LINEAR ARRANGEMENT,
comment: "Remains NP-complete if G is bipartite [Even and Shiloach, 1975]" (S. Even and
Y. Shiloach, "NP-completeness of several arrangement problems", Technical Report 43, Department
of Computer Science, Technion, Haifa (1975); the report itself was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumLinearArrangementWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalLinearArrangementBipartite

open MinimumLinearArrangement (MinimumLinearArrangementInstance
  MinimumLinearArrangementFeasible)

/-!
# OPTIMAL LINEAR ARRANGEMENT for bipartite graphs is NP-complete

INSTANCE: a bipartite graph `G = (V, E)` and a positive integer `K`.
QUESTION: is there a one-to-one function `f : V → {1, 2, …, |V|}` such that
`∑_{{u, v} ∈ E} |f(u) - f(v)| ≤ K`?

This is OPTIMAL LINEAR ARRANGEMENT ([GT42], `MinimumLinearArrangementWanted`) restricted to
bipartite graphs, which Garey and Johnson record as NP-complete with the attribution to Even and
Shiloach. The instance (vertex count, edge list, bound), the simple-edge-list conditions and the
question (a labelling of the vertices by the positions `0, …, n - 1` of a permutation of
`List.range n`, with total edge length at most `K`; positions `0, …, n - 1` instead of
`1, …, |V|` change no difference) are those of `MinimumLinearArrangementWanted`; the restriction
adds to `WellFormed` that `Cslib.Complexity.Karp.edgeGraph` is bipartite (Mathlib's
`SimpleGraph.IsBipartite`, a proper `2`-colouring) and Garey and Johnson's `0 < K`.

Membership in NP holds as for OPTIMAL LINEAR ARRANGEMENT, and bipartiteness is checked in linear
time; isolated vertices (outside the edge list) can be placed last without changing any edge
length, so the binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed OPTIMAL LINEAR ARRANGEMENT instance (a simple
edge list on `0, …, n - 1`) whose graph is bipartite, and `0 < K`. -/
def WellFormed (i : MinimumLinearArrangementInstance) : Prop :=
  MinimumLinearArrangement.WellFormed i ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsBipartite ∧ 0 < i.2.2

open Classical in
/-- OPTIMAL LINEAR ARRANGEMENT for bipartite graphs as a decision problem over bitstrings. -/
noncomputable def optimalLinearArrangementBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumLinearArrangementInstance) x with
  | some i => decide (WellFormed i ∧ MinimumLinearArrangementFeasible i)
  | none => false

/-- **OPTIMAL LINEAR ARRANGEMENT for bipartite graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT42]; Even and Shiloach (1975). -/
public theorem_wanted optimalLinearArrangementBipartite_npComplete :
    optimalLinearArrangementBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L optimalLinearArrangementBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.OptimalLinearArrangementBipartite
