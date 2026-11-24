/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POLARITY OF CLAW-FREE GRAPHS is NP-complete

Source:
R. Churchley and J. Huang, "On the polarity and monopolarity of graphs", Journal of Graph Theory
76 (2014), 138-148, doi:10.1002/jgt.21755 (recognizing polarity is NP-complete for claw-free
graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PolarityTwoKTwoCFiveFreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolarityClawFree

open MetaMathlibExt.Complexity.NPComplete.PolarityTwoKTwoCFiveFree
  (PolarityTwoKTwoCFiveFreeInstance Graph PolarityTwoKTwoCFiveFreeFeasible)

/-!
# POLARITY OF CLAW-FREE GRAPHS is NP-complete

INSTANCE: a claw-free graph `G = (V, E)` (no induced subgraph isomorphic to the claw `K₁,₃`; ISGCI
class `gc_62`).
QUESTION: is `G` polar, i.e. can `V` be partitioned into `A` and `B` such that `G[A]` is a complete
multipartite graph (its complement is a disjoint union of cliques) and `G[B]` is a disjoint union of
cliques?

Churchley and Huang prove that recognizing polarity is NP-complete for claw-free graphs (while
monopolarity is polynomial there). Membership in NP: the partition is a polynomial certificate.

The instance type, the graph and the question are reused from `PolarityTwoKTwoCFiveFreeWanted`
(`PolarityTwoKTwoCFiveFree.PolarityTwoKTwoCFiveFreeInstance`, `PolarityTwoKTwoCFiveFree.Graph`,
`PolarityTwoKTwoCFiveFree.PolarityTwoKTwoCFiveFreeFeasible`, which says only that the graph is
polar in the sense of `PolarityTriangleFree.IsPolar`); this module replaces the `(2K₂, C₅)`-freeness
by claw-freeness, MathlibExt's `SimpleGraph.IsClawFree` (no vertex with three pairwise non-adjacent
distinct neighbors, equivalent to the claw not being an induced subgraph,
`SimpleGraph.isClawFree_iff_not_isIndContained`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and the graph is
claw-free. -/
def WellFormed (i : PolarityTwoKTwoCFiveFreeInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsClawFree

open Classical in
/-- POLARITY OF CLAW-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def polarityClawFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PolarityTwoKTwoCFiveFreeInstance) x with
  | some i => decide (WellFormed i ∧ PolarityTwoKTwoCFiveFreeFeasible i)
  | none => false

/-- **POLARITY OF CLAW-FREE GRAPHS is NP-complete.** Source: Churchley and Huang (2014). -/
public theorem_wanted polarityClawFree_npComplete :
    polarityClawFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L polarityClawFreeDec

end MetaMathlibExt.Complexity.NPComplete.PolarityClawFree
