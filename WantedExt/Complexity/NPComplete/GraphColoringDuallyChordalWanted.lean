/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY on dually chordal graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER) (the parent problem);
A. Leitert, "3-Colourability of dually chordal graphs in linear time", arXiv:1206.0233 (2012),
Theorem 1 (4-COLOURABILITY is NP-complete for dually chordal graphs);
A. Brandstädt, V. D. Chepoi and F. F. Dragan, "The algorithmic use of hypertree structure and
maximum neighbourhood orderings", Discrete Applied Mathematics 82(1-3) (1998), 43-77,
doi:10.1016/s0166-218x(97)00125-x (cited by Wikipedia, "Dually chordal graph", for this
result);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_185` (dually
chordal), problem Colourability: NP-complete (note `ref_1504`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted
public import WantedExt.Complexity.NPComplete.IndependentSetDuallyChordalWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringDuallyChordal

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)
open IndependentSetDuallyChordal (DuallyChordal)

/-!
# GRAPH K-COLORABILITY on dually chordal graphs is NP-complete

INSTANCE: a dually chordal graph `G = (V, E)`, and a positive integer `K ≤ |V|`.
QUESTION: is `G` `K`-colorable, i.e. is there a function `f : V → {1, 2, ..., K}` such that
`f(u) ≠ f(v)` whenever `{u, v} ∈ E`?

This is GRAPH K-COLORABILITY ([GT4]) on the ISGCI class `gc_185`. Dually chordal graphs are
those with a maximum neighbourhood ordering; the predicate is
`IndependentSetDuallyChordal.DuallyChordal`, which states ISGCI's definition and is reused here
unchanged.

The instance type (vertex count `n`, edge list, bound `K`), the graph
(`Cslib.Complexity.Karp.edgeGraph` on `Fin n`), the simple-edge-list condition
(`GraphColoring.WellFormed`) and the question (`GraphColoring.GraphColoringFeasible`, Mathlib's
`SimpleGraph.Colorable K`) are those of `GraphColoringWanted`. `WellFormed` adds [GT4]'s
`0 < K ≤ |V|` and the class.

Leitert (2012, Theorem 1) proves 4-COLOURABILITY NP-complete for dually chordal graphs: adding a
vertex adjacent to all others makes any graph dually chordal, and the new graph is 4-colorable
exactly when the old one is 3-colorable. Hence the problem with `K` part of the input is
NP-hard; Wikipedia ("Dually chordal graph", Complexity of problems) and ISGCI record coloring as
NP-complete on dually chordal graphs.

Membership in NP, with `n` written in binary (so most vertices may be isolated): an isolated
vertex is its own maximum neighbour and lies in no other closed neighbourhood, so it can sit
anywhere in a maximum neighbourhood ordering, and the graph is dually chordal exactly when the
subgraph induced by the at most `2|E|` endpoints of edges is; dually chordal graphs are
recognizable in linear time (Brandstädt, Chepoi and Dragan 1998). Isolated vertices can take any
color (`K ≥ 1`), so a certificate is a coloring of the endpoints of edges with colors below `K`,
of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`
(`GraphColoring.WellFormed`), `0 < K ≤ |V|`, and the graph is dually chordal. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ (0 < i.2.2 ∧ i.2.2 ≤ i.1) ∧ DuallyChordal (Graph i)

open Classical in
/-- GRAPH K-COLORABILITY on dually chordal graphs as a decision problem over bitstrings. -/
noncomputable def graphColoringDuallyChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **GRAPH K-COLORABILITY on dually chordal graphs is NP-complete.** Source: Leitert (2012),
Theorem 1; Brandstädt, Chepoi and Dragan (1998); ISGCI (`gc_185`); Garey and Johnson (1979),
[GT4] (parent problem). -/
public theorem_wanted graphColoringDuallyChordal_npComplete :
    graphColoringDuallyChordalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphColoringDuallyChordalDec

end MetaMathlibExt.Complexity.NPComplete.GraphColoringDuallyChordal
