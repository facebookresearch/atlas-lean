/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED DIAMETER on trees is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER, p. 205
(comment: "NP-complete in the strong sense, even if `G` is a tree.");
Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", Theoretical Computer
Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import WantedExt.Complexity.NPComplete.WeightedDiameterWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedDiameterTree

open WeightedDiameter (WeightedDiameterInstance Graph WeightedDiameterFeasible)

/-!
# WEIGHTED DIAMETER on trees is NP-complete

INSTANCE: a tree `G = (V, E)`, a collection `C` of `|E|` not necessarily distinct non-negative
integers, and a positive integer `K`.
QUESTION: is there a one-to-one function `f : E → C` such that, if `f(e)` is taken as the length
of edge `e`, then `G` has diameter `K` or less, i.e., every pair of points `u, v ∈ V` is joined by
a path in `G` of length `K` or less?

This is the restriction of WEIGHTED DIAMETER ([GT65], `WeightedDiameterWanted`) to trees,
named in the entry's comment. The instance type, the graph and
`WeightedDiameter.WeightedDiameterFeasible` are the parent's, unchanged: `C` is a list of
`|E|` naturals, a one-to-one `f : E → C` is a rearrangement of `C` assigning the `k`-th listed
edge the `k`-th length, and a path is a Mathlib `SimpleGraph.Walk` that `IsPath`, whose length
is the sum of its edge lengths. `WellFormed` adds that the graph is a tree, Mathlib's
`SimpleGraph.IsTree` (connected, hence nonempty, and acyclic). Numbers use the binary
encoding; Garey and Johnson record that the problem is NP-complete in the strong sense, even
for trees, and Perl and Zaks prove that finding a labeling of minimal diameter is NP-complete
for trees.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (a simple edge list in range, `C` with `|E|`
members, `K` positive), and the graph is a tree. -/
def WellFormed (i : WeightedDiameterInstance) : Prop :=
  WeightedDiameter.WellFormed i ∧ (Graph i).IsTree

open Classical in
/-- WEIGHTED DIAMETER on trees as a decision problem over bitstrings. -/
noncomputable def weightedDiameterTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedDiameterInstance) x with
  | some i => decide (WellFormed i ∧ WeightedDiameterFeasible i)
  | none => false

/-- **WEIGHTED DIAMETER is NP-complete on trees.** Source: Garey and Johnson (1979), [GT65],
comment; Perl and Zaks (1982). -/
public theorem_wanted weightedDiameterTree_npComplete :
    weightedDiameterTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedDiameterTreeDec

end MetaMathlibExt.Complexity.NPComplete.WeightedDiameterTree
