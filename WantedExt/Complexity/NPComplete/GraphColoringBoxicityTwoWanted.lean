/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY ON GRAPHS OF BOXICITY AT MOST 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), the problem restricted here;
H. Imai and T. Asano, "Finding the connected components and a maximum clique of an intersection
graph of rectangles in the plane", Journal of Algorithms 4 (1983), 310-323,
doi:10.1016/0196-6774(83)90012-3 (coloring rectangle intersection graphs is NP-complete);
D. Catanzaro, S. Chaplick, S. Felsner, B. V. Halldórsson, M. M. Halldórsson, T. Hixon, and
J. Stacho, "Max point-tolerance graphs", Discrete Applied Mathematics 216 (2017), 84-97,
doi:10.1016/j.dam.2015.08.019, arXiv:1508.03810 (records the result for boxicity-2 graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.BoxicityTwoWanted
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringBoxicityTwo

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# GRAPH K-COLORABILITY ON GRAPHS OF BOXICITY AT MOST 2 is NP-complete

INSTANCE: a graph `G = (V, E)` of boxicity at most `2` (an intersection graph of axis-parallel
rectangles in the plane) and a positive integer `K ≤ |V|`.
QUESTION: is `G` `K`-colorable, i.e. is there a map `c : V → {1, …, K}` with `c(u) ≠ c(v)` for
every edge `uv`?

This is GRAPH K-COLORABILITY restricted to the graphs of boxicity at most `2` (ISGCI class
`gc_239`, "boxicity 2": graphs with an intersection model of axis-parallel rectangles). Imai and
Asano showed that determining the chromatic number of the intersection graph of a family of
axis-parallel rectangles is NP-hard; Catanzaro et al. record that the coloring problem is
NP-complete on boxicity-2 graphs. Membership in NP: a certificate is a coloring together with a
rectangle representation; whenever a representation exists, one with integer corner coordinates in
`0, …, 2n` exists (intersections depend only on the order of the corner coordinates), so the
certificate has polynomial size.

The instance, the graph and the question are those of `GraphColoringWanted`, reused unchanged:
vertex count, edge list on `Fin n` and number of colors `K`, with `GraphColoring.WellFormed`,
`GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable i.2.2`). The
restriction adds `0 < K ≤ |V|` (the bound of Garey and Johnson's [GT4]) and the rectangle
representation, which is `BoxicityTwo.BoxicityTwoFeasible` of `BoxicityTwoWanted` applied to the
same vertex count and edge list (its graph is the same `Cslib.Complexity.Karp.edgeGraph`): closed
axis-parallel rectangles `Set.Icc (lo v) (hi v)` of `ℝ × ℝ`, distinct vertices adjacent exactly when
their rectangles intersect.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `0 < K ≤ |V|`
whose graph has boxicity at most `2` (`BoxicityTwo.BoxicityTwoFeasible` on its vertex count and
edge list). -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ (0 < i.2.2 ∧ i.2.2 ≤ i.1) ∧
    BoxicityTwo.BoxicityTwoFeasible (i.1, i.2.1)

open Classical in
/-- GRAPH K-COLORABILITY ON GRAPHS OF BOXICITY AT MOST 2 as a decision problem over bitstrings. -/
noncomputable def graphColoringBoxicityTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **GRAPH K-COLORABILITY ON GRAPHS OF BOXICITY AT MOST 2 is NP-complete.** Source: Garey and
Johnson (1979), [GT4]; Imai and Asano (1983); Catanzaro et al. (2017). -/
public theorem_wanted graphColoringBoxicityTwo_npComplete :
    graphColoringBoxicityTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphColoringBoxicityTwoDec

end MetaMathlibExt.Complexity.NPComplete.GraphColoringBoxicityTwo
