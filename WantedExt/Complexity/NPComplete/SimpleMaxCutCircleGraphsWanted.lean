/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT for circle graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT (comment: SIMPLE MAX
CUT, all weights 1);
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1;
C. Buchheim and L. Zheng, "Fixed linear crossing minimization by reduction to the maximum cut
problem", COCOON 2006, Lecture Notes in Computer Science 4112, 507-516,
doi:10.1007/11809678_53;
S. Masuda, K. Nakajima, T. Kashiwabara and T. Fujisawa, "Crossing minimization in linear
embeddings of graphs", IEEE Transactions on Computers 39 (1990), 124-127,
doi:10.1109/12.46286.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MaxCutWanted
public import WantedExt.Complexity.NPComplete.PathwidthCircleGraphsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCircleGraphs

open MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT for circle graphs is NP-complete

INSTANCE: a circle graph `G = (V, E)` (the intersection graph of a family of chords of a circle)
and a positive integer `K`.
QUESTION: is there a partition of `V` into disjoint sets `V₁` and `V₂` such that at least `K`
edges of `E` have one endpoint in `V₁` and one endpoint in `V₂`?

This is SIMPLE MAX CUT (MAX CUT [ND16] with all weights 1) restricted to circle graphs. Johnson's
1985 table lists this entry as apparently open; the 2022 revision of the table by de Figueiredo,
de Melo, Sasaki and Silva lists it as NP-complete, citing Buchheim and Zheng. Masuda, Nakajima,
Kashiwabara and Fujisawa prove that the fixed linear crossing number problem is NP-hard: given a
graph `H` whose vertices lie on a line in a fixed order, draw every edge as a semicircle above or
below the line with as few crossings as possible. Buchheim and Zheng (Section 3.1, Theorem 1)
reduce it to MAX CUT on the conflict graph of `H`, whose vertices are the edges of `H`, two being
adjacent when their endpoints interleave (`v₁ < v₂ < w₁ < w₂`): a split of the edges into the
two sides has exactly `|E'| - c` crossings, where `E'` is the edge set of the conflict graph and
`c` is the size of the corresponding cut. Placing the vertices of `H` around a circle in the same
order turns its edges into chords, and two chords cross exactly when their endpoints interleave
(chords sharing an endpoint can be moved apart without crossing), so the conflict graph is a
circle graph and "at most `C` crossings" becomes "a cut of size at least `|E'| - C`".

The instance, the simple-edge-list conditions and the question are those of MAXIMUM CUT
(`MaxCutWanted`, whose question counts edges), reused as in `MaxCutIntervalGraphsWanted`; the
restriction adds that `Cslib.Complexity.Karp.edgeGraph` is a circle graph, and `0 < K`, to
`WellFormed`. Circle graphs are `PathwidthCircleGraphs.IsCircleGraph` (from
`PathwidthCircleGraphsWanted`): isomorphic to the circle graph of a chord model in the sense of
`DominatingSetCircleGraphWanted`, chords `(a, b)` with `a < b`, all endpoints distinct, two chords
adjacent when their endpoints interleave.

Membership in NP: a chord model of the graph induced on the non-isolated vertices (at most two per
edge) and a cut are a polynomial certificate. Isolated vertices are represented by chords disjoint
from all others and do not change the answer, so the binary vertex count does not make the
problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is a circle graph, and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧
    PathwidthCircleGraphs.IsCircleGraph (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧ 0 < i.2.2

open Classical in
/-- SIMPLE MAX CUT for circle graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutCircleGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

/-- **SIMPLE MAX CUT for circle graphs is NP-complete.** Source: Garey and Johnson (1979),
[ND16]; Masuda, Nakajima, Kashiwabara and Fujisawa (1990); Buchheim and Zheng (2006),
Theorem 1; de Figueiredo, de Melo, Sasaki and Silva (2022), Table 1. -/
public theorem_wanted simpleMaxCutCircleGraphs_npComplete :
    simpleMaxCutCircleGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutCircleGraphsDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCircleGraphs
