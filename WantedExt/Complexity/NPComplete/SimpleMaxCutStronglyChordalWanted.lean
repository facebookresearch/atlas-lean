/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT for strongly chordal graphs is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (SIMPLE MAX CUT
for strongly chordal graphs, open there);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for
the 21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (entry N [108]: R. Sucupira, L. Faria and
S. Klein, SBPO 2013);
R. Adhikary, K. Bose, S. Mukherjee and B. Roy, "Complexity of maximum cut on interval graphs",
Discrete & Computational Geometry 70 (2023), 307-322, doi:10.1007/s00454-022-00472-y, Theorem 1;
M. Farber, "Characterizations of strongly chordal graphs", Discrete Mathematics 43 (1983),
173-189, doi:10.1016/0012-365X(83)90154-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.StronglyChordalSplitHamiltonianPathWanted
public import WantedExt.Complexity.NPComplete.MaxCutWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutStronglyChordal

open MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT for strongly chordal graphs is NP-complete

INSTANCE: a strongly chordal graph `G = (V, E)` and a positive integer `K`.
QUESTION: is there a partition of `V` into two sets with at least `K` edges between them?

This is SIMPLE MAX CUT (MAX CUT with all edge weights one) restricted to strongly chordal
graphs, an entry of Johnson's Table 1 that de Figueiredo, de Melo, Sasaki and Silva resolve as
NP-complete, citing Sucupira, Faria and Klein (SBPO 2013; not available here). Hardness also
follows from Adhikary, Bose, Mukherjee and Roy, who prove SIMPLE MAX CUT NP-complete on interval
graphs: interval graphs are directed path graphs, which are strongly chordal (both inclusions
are stated in Johnson's column).
The instance, the simple-edge-list conditions and the question are those of MAXIMUM CUT
(`MaxCutWanted`, whose question counts edges), reused as in
`SimpleMaxCutUndirectedPathGraphsWanted`; the restriction adds to `WellFormed` that
`Cslib.Complexity.Karp.edgeGraph` is strongly chordal, and `0 < K`.

"Strongly chordal" is the repository's predicate
`StronglyChordalSplitHamiltonianPath.IsStronglyChordal` (also used by
`HamiltonianCircuitStronglyChordalWanted`): no induced cycle of length at least `4` (chordal),
and every cycle of even length at least `6` has an odd chord.

Membership in NP: a cut is a polynomial certificate, and strongly chordal graphs are recognized
in polynomial time (Farber). Vertices outside the edge list are isolated; they lie on no cycle,
so they change neither the answer nor membership in the class, the check runs on the
non-isolated vertices, and the binary vertex count does not make the problem succinct.

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
`Fin n`) whose graph is strongly chordal, and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧
    StronglyChordalSplitHamiltonianPath.IsStronglyChordal
      (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
    0 < i.2.2

open Classical in
/-- SIMPLE MAX CUT for strongly chordal graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutStronglyChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

/-- **SIMPLE MAX CUT for strongly chordal graphs is NP-complete.**
Source: Johnson (1985), Table 1; de Figueiredo, de Melo, Sasaki and Silva (2022);
Sucupira, Faria and Klein (2013); Adhikary, Bose, Mukherjee and Roy (2023). -/
public theorem_wanted simpleMaxCutStronglyChordal_npComplete :
    simpleMaxCutStronglyChordalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutStronglyChordalDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutStronglyChordal
