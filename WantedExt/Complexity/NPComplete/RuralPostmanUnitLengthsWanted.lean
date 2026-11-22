/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RURAL POSTMAN with unit lengths is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND27] RURAL POSTMAN, comment
(p. 213: "Remains NP-complete even if l(e) = 1 for all e ∈ E");
J. K. Lenstra and A. H. G. Rinnooy Kan, "On general routing problems",
Networks 6 (1976), 273-280, doi:10.1002/net.3230060305 (the entry's reference).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.RuralPostmanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RuralPostmanUnitLengths

open MetaMathlibExt.Complexity.NPComplete.RuralPostman
  (RuralPostmanInstance RuralPostmanFeasible)

/-!
# RURAL POSTMAN with unit lengths is NP-complete

INSTANCE: a graph `G = (V, E)` with length `l(e) = 1` for each `e ∈ E`, a subset `E' ⊆ E`, and
a positive integer `B`. QUESTION: is there a circuit in `G` that includes each edge in `E'` and
that has total length no more than `B`?

This is RURAL POSTMAN ([ND27], `RuralPostmanWanted`) restricted to unit edge lengths, the
restriction recorded in the entry's comment. The instance type,
`RuralPostman.WellFormed` (simple edge list, required edges in the graph, `0 < B`) and
`RuralPostman.RuralPostmanFeasible` (a closed walk through every required edge whose length,
counting repeated traversals, is at most `B`) are the parent's, unchanged; `WellFormed` adds
that every listed length is `1`, so the length of a circuit is its number of edge traversals.
The comment's directed analogue is a separate problem and is not stated here.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (simple edge list, required edges in the graph,
`0 < B`) and every edge length is `1`. -/
def WellFormed (i : RuralPostmanInstance) : Prop :=
  RuralPostman.WellFormed i ∧ ∀ e ∈ i.2.1, e.2.2 = 1

open Classical in
/-- RURAL POSTMAN with unit lengths as a decision problem over bitstrings. -/
noncomputable def ruralPostmanUnitLengthsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RuralPostmanInstance) x with
  | some i => decide (WellFormed i ∧ RuralPostmanFeasible i)
  | none => false

/-- **RURAL POSTMAN is NP-complete with unit lengths.** Source: Garey and Johnson (1979),
[ND27], comment; Lenstra and Rinnooy Kan (1976). -/
public theorem_wanted ruralPostmanUnitLengths_npComplete :
    ruralPostmanUnitLengthsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L ruralPostmanUnitLengthsDec

end MetaMathlibExt.Complexity.NPComplete.RuralPostmanUnitLengths
