/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC NUMBER for planar graphs of maximum degree 4 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC NUMBER),
p. 191, comment ("remains NP-complete ... for K = 3, for planar graphs having no vertex degree
exceeding 4");
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticNumberPlanarMaxDegreeFour

open MetaMathlibExt.Complexity.NPComplete.GraphColoring
  (GraphColoringInstance Graph GraphColoringFeasible)

/-!
# CHROMATIC NUMBER for planar graphs of maximum degree 4 is NP-complete

INSTANCE: a planar graph `G = (V, E)` with no vertex degree exceeding 4, and a positive integer
`K ≤ |V|`.
QUESTION: is `G` `K`-colorable, i.e., does there exist a function `f : V → {1, 2, …, K}` such
that `f(u) ≠ f(v)` whenever `{u, v} ∈ E`?

This is GRAPH K-COLORABILITY ([GT4]) with `K` part of the input, restricted to planar graphs of
maximum degree 4 (the ISGCI class "planar of maximum degree 4", gc_909). The instance, its graph,
the simple-edge-list well-formedness and the question (Mathlib's `SimpleGraph.Colorable K`) are
those of `WantedExt.Complexity.NPComplete.GraphColoringWanted`. The restriction adds [GT4]'s
`0 < K ≤ |V|`, planarity as the repository's `SimpleGraph.IsPlanar` (a crossing-free
straight-line drawing, which by Fáry's theorem exists exactly for planar graphs) and the degree
bound as Mathlib's `SimpleGraph.degree`.

Hardness: Garey, Johnson and Stockmeyer prove 3-colorability NP-complete for planar graphs of
maximum degree 4, and those are the instances of this problem with `K = 3`. Membership in NP:
the certificate colors the non-isolated vertices (isolated ones take color 1, so the binary
vertex count does not make the problem succinct); degrees are checked directly and planarity in
linear time (Hopcroft and Tarjan, J. ACM 21 (1974), 549-568).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with
`0 < K ≤ |V|` whose graph is planar with every vertex degree at most 4. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ (Graph i).IsPlanar ∧
    ∀ v, (Graph i).degree v ≤ 4

open Classical in
/-- CHROMATIC NUMBER for planar graphs of maximum degree 4 as a decision problem over
bitstrings. -/
noncomputable def chromaticNumberPlanarMaxDegreeFourDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoringFeasible i)
  | none => false

/-- **CHROMATIC NUMBER for planar graphs of maximum degree 4 is NP-complete.** Source: Garey and
Johnson (1979), [GT4], comment; Garey, Johnson and Stockmeyer (1976). -/
public theorem_wanted chromaticNumberPlanarMaxDegreeFour_npComplete :
    chromaticNumberPlanarMaxDegreeFourDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chromaticNumberPlanarMaxDegreeFourDec

end MetaMathlibExt.Complexity.NPComplete.ChromaticNumberPlanarMaxDegreeFour
