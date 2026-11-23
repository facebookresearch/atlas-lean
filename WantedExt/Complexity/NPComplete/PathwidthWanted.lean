/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH is NP-complete

Source:
T. Ohtsuki, H. Mori, E. S. Kuh, T. Kashiwabara and T. Fujisawa, "One-dimensional logic gate
assignment and interval graphs", IEEE Transactions on Circuits and Systems 26 (1979), 675-684,
doi:10.1109/TCS.1979.1084695 (minimum clique number interval augmentation is NP-complete);
T. Kashiwabara and T. Fujisawa, "NP-completeness of the problem of finding a minimum-clique-number
interval graph containing a given graph as a subgraph", Proc. IEEE International Symposium on
Circuits and Systems (1979), 657-660.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PathwidthChordalGraphsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Pathwidth

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance PathwidthChordalGraphsFeasible)

/-!
# PATHWIDTH is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`.
QUESTION: does `G` have pathwidth at most `K`, i.e., a path decomposition of width at most `K`?

A path decomposition of `G` is a sequence of bags of vertices such that every vertex lies in some
bag, both ends of every edge lie in a common bag, and the bags containing any one vertex are
consecutive; its width is the largest bag size minus one. So the pathwidth is at most `K` exactly
when some path decomposition has all bags of size at most `K + 1`; equivalently, `G` is a subgraph
of an interval graph with clique number at most `K + 1`, the form in which Ohtsuki et al. and
Kashiwabara and Fujisawa proved NP-completeness (minimum clique number interval augmentation).

The instance type, the path decompositions (`IsPathDecomposition`) and the question
(`PathwidthChordalGraphsFeasible`: some path decomposition of the graph `edgeGraph n E` has every
bag of size at most `K + 1`) are those of
`WantedExt.Complexity.NPComplete.PathwidthChordalGraphsWanted`, reused here; that module states
the restriction of this problem to chordal graphs, and the only difference here is that
`WellFormed` does not require chordality.

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
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : PathwidthChordalGraphsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

open Classical in
/-- PATHWIDTH as a decision problem over bitstrings. -/
noncomputable def pathwidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathwidthChordalGraphsInstance) x with
  | some i => decide (WellFormed i ∧ PathwidthChordalGraphsFeasible i)
  | none => false

/-- **PATHWIDTH is NP-complete.** Source: Ohtsuki, Mori, Kuh, Kashiwabara and Fujisawa (1979);
Kashiwabara and Fujisawa (1979). -/
public theorem_wanted pathwidth_npComplete :
    pathwidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathwidthDec

end MetaMathlibExt.Complexity.NPComplete.Pathwidth
