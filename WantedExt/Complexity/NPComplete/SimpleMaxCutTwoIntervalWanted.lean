/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on 2-interval graphs is NP-complete

Source:
R. Adhikary, K. Bose, S. Mukherjee and B. Roy, "Complexity of maximum cut on interval graphs",
Discrete & Computational Geometry 70 (2023), 307-322, doi:10.1007/s00454-022-00472-y, Theorem 1
(MAX CUT is NP-complete on interval graphs);
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Nordic Journal
of Computing 7 (2000), 14-31 (the reference ISGCI gives for this class);
ISGCI, class "2-interval" (gc_40), problem Maximum cut, NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.IntervalNumberAtMostKWanted
public import WantedExt.Complexity.NPComplete.MaxCutWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutTwoInterval

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)
open MetaMathlibExt.Complexity.NPComplete.IntervalNumberAtMostK (IsMultipleIntervalGraph)

/-!
# SIMPLE MAX CUT on 2-interval graphs is NP-complete

INSTANCE: a 2-interval graph `G = (V, E)`, i.e. the intersection graph of sets each consisting
of two intervals on the real line, and an integer `K` with `1 ≤ K ≤ |E|`.
QUESTION: is there a partition of `V` into sets `A`, `B` such that at least `K` edges have one
endpoint in `A` and the other in `B`?

This is SIMPLE MAX CUT (MAX CUT with all edge weights one) restricted to 2-interval graphs.
Adhikary, Bose, Mukherjee and Roy prove SIMPLE MAX CUT NP-complete on interval graphs, and every
interval graph is a 2-interval graph (give each vertex its interval twice), so the problem is
NP-hard; ISGCI records it as NP-complete on 2-interval graphs, citing Bodlaender and Jansen.

The instance, the simple-edge-list conditions and the question are those of MAXIMUM CUT
(`WantedExt.Complexity.NPComplete.MaxCutWanted`, whose question counts edges), reused as in
`SimpleMaxCutDegreeThreeWanted`; the restriction adds to `WellFormed` that
`Cslib.Complexity.Karp.edgeGraph` is a 2-interval graph, the repository's
`IntervalNumberAtMostK.IsMultipleIntervalGraph 2` (each vertex gets two closed intervals, possibly
equal, and distinct vertices are adjacent exactly when their unions meet), and `1 ≤ K ≤ |E|`, the
bound of Adhikary et al. (as in `MaxCutIntervalGraphsWanted`; the edge list has no repeated edge,
so `|E|` is its length). Membership in NP: a cut together with a 2-interval model of the
non-isolated vertices whose endpoints are replaced by their ranks is a polynomial certificate
(isolated vertices get far-away intervals), so the binary vertex count does not make the problem
succinct.

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
the vertices `0, ..., n - 1`) whose graph is a 2-interval graph, and `1 ≤ K ≤ |E|`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧ IsMultipleIntervalGraph 2 (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
    1 ≤ i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- A partition `A = S`, `B = V - S` with at least `K` edges between the two sets (the MAXIMUM
CUT question). -/
def SimpleMaxCutTwoIntervalFeasible (i : MaxCutInstance) : Prop :=
  MaxCutFeasible i

open Classical in
/-- SIMPLE MAX CUT on 2-interval graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutTwoIntervalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ SimpleMaxCutTwoIntervalFeasible i)
  | none => false

/-- **SIMPLE MAX CUT on 2-interval graphs is NP-complete.** Source: Adhikary, Bose, Mukherjee
and Roy (2023), Theorem 1 (interval graphs are 2-interval graphs); ISGCI (gc_40). -/
public theorem_wanted simpleMaxCutTwoInterval_npComplete :
    simpleMaxCutTwoIntervalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutTwoIntervalDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutTwoInterval
