/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX for claw-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN5] CHROMATIC INDEX;
L. Cai and J. A. Ellis, "NP-completeness of edge-colouring some restricted graphs", Discrete
Applied Mathematics 30 (1991), 15-27, doi:10.1016/0166-218X(91)90010-T;
E. Galby, P. T. Lima, D. Paulusma and B. Ries, "Classifying k-edge colouring for H-free
graphs", Information Processing Letters 146 (2019), 39-43, doi:10.1016/j.ipl.2019.02.006;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.EdgeColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticIndexClawFree

open EdgeColoring (EdgeColoringInstance EdgeColoringFeasible)

/-!
# CHROMATIC INDEX for claw-free graphs is NP-complete

INSTANCE: a claw-free graph `G = (V, E)` (no induced `K₁,₃`) and a positive integer `K`.
QUESTION: is the chromatic index of `G` at most `K`, i.e. can `E` be partitioned into at most `K`
matchings (sets of edges no two of which share an endpoint)?

This is CHROMATIC INDEX (Garey and Johnson's open problem [OPEN5], shown NP-complete by Holyer;
`EdgeColoringWanted`) restricted to claw-free graphs. Johnson's 1985 table lists this entry as
apparently open; the 2022 revision of the table by de Figueiredo, de Melo, Sasaki and Silva lists
it as NP-complete, citing Cai and Ellis, who proved that deciding whether the chromatic index is
3 is NP-complete for line graphs. Galby, Lima, Paulusma and Ries (Theorem 4) state the result of
Cai and Ellis used here: "Let `k ≥ 3` be an odd integer. Then `k`-Edge Colouring is NP-complete
for `k`-regular line graphs of bipartite graphs." Line graphs are claw-free (the neighbours of an
edge `uv` in the line graph form two cliques, the edges at `u` and the edges at `v`), so the
reductions of Cai and Ellis, which produce cubic line graphs with `K = 3`, produce instances of
this class and prove it NP-hard. Membership in NP: an edge colouring is a certificate, and
claw-freeness is checked in polynomial time on the non-isolated vertices; isolated vertices
change neither the class nor the answer, so the binary vertex count does not make the problem
succinct.

The instance, the simple-edge-list conditions and the question are those of EDGE COLORING
(`EdgeColoringWanted`: vertex count, edge list on the vertices `0, ..., n - 1`, bound `K`; an
assignment of colours `0, ..., K - 1` to the listed edges in which edges sharing an endpoint get
different colours); the restriction adds claw-freeness of `Cslib.Complexity.Karp.edgeGraph` and `0 <
K` to `WellFormed`. Claw-freeness is MathlibExt's `SimpleGraph.IsClawFree` (from
`MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly`, as in `PolarityClawFreeWanted`): no
vertex `c` with three distinct, pairwise non-adjacent neighbours `l₁, l₂, l₃`, equivalently
(`SimpleGraph.isClawFree_iff_not_isIndContained`) no induced `K₁,₃`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed EDGE COLORING instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is claw-free, and `0 < K`. -/
def WellFormed (i : EdgeColoringInstance) : Prop :=
  EdgeColoring.WellFormed i ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsClawFree ∧ 0 < i.2.2

open Classical in
/-- CHROMATIC INDEX for claw-free graphs as a decision problem over bitstrings. -/
noncomputable def chromaticIndexClawFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeColoringInstance) x with
  | some i => decide (WellFormed i ∧ EdgeColoringFeasible i)
  | none => false

/-- **CHROMATIC INDEX for claw-free graphs is NP-complete.** Source: Cai and Ellis (1991);
Galby, Lima, Paulusma and Ries (2019), Theorem 4; de Figueiredo, de Melo, Sasaki and Silva
(2022), Table 1. -/
public theorem_wanted chromaticIndexClawFree_npComplete :
    chromaticIndexClawFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chromaticIndexClawFreeDec

end MetaMathlibExt.Complexity.NPComplete.ChromaticIndexClawFree
