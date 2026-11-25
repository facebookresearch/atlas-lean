/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED DIAMETER with 0/1 lengths and K = 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER (p. 205),
comment "If C consists entirely of 0's and 1's, then both the diameter and radius versions are
solvable in polynomial time for trees, but are NP-complete for general graphs, even if K is fixed
at 2 (diameter) or 1 (radius)" (credited there to Perl and Zaks, 1978);
Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", Theoretical Computer
Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.WeightedDiameterWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedDiameterZeroOne

open MetaMathlibExt.Complexity.NPComplete.WeightedDiameter (WeightedDiameterInstance)

/-!
# WEIGHTED DIAMETER with 0/1 lengths and K = 2 is NP-complete

INSTANCE: a graph `G = (V, E)` and a collection `C` of `|E|` integers, each `0` or `1`.
QUESTION: is there a one-to-one function `f : E → C` such that, if `f(e)` is taken as the length
of edge `e`, then `G` has diameter `2` or less, i.e., every pair of points `u, v ∈ V` is joined by
a path in `G` of length `2` or less?

This is the restriction of WEIGHTED DIAMETER ([GT65], `WeightedDiameterWanted`) to collections
`C` consisting entirely of `0`s and `1`s and to the bound `K = 2`, on general graphs. The
instance type, `WeightedDiameter.WellFormed` (a simple edge list on `Fin n`, `|C| = |E|`,
`0 < K`) and `WeightedDiameter.WeightedDiameterFeasible` are the parent's, unchanged;
`WellFormed` adds that every member of `C` is `0` or `1` and that `K = 2`. Garey and Johnson
record that this restriction is solvable in polynomial time for trees.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`, `|C| = |E|`,
`0 < K`), every member of `C` is `0` or `1`, and `K = 2`. -/
def WellFormed (i : WeightedDiameterInstance) : Prop :=
  WeightedDiameter.WellFormed i ∧ (∀ c ∈ i.2.2.1, c = 0 ∨ c = 1) ∧ i.2.2.2 = 2

open Classical in
/-- WEIGHTED DIAMETER with 0/1 lengths and `K = 2` as a decision problem over bitstrings. -/
noncomputable def weightedDiameterZeroOneDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedDiameterInstance) x with
  | some i => decide (WellFormed i ∧ WeightedDiameter.WeightedDiameterFeasible i)
  | none => false

/-- **WEIGHTED DIAMETER with 0/1 lengths is NP-complete for `K = 2`.** Source: Garey and Johnson
(1979), [GT65], comment (Perl and Zaks, 1978). -/
public theorem_wanted weightedDiameterZeroOne_npComplete :
    weightedDiameterZeroOneDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedDiameterZeroOneDec

end MetaMathlibExt.Complexity.NPComplete.WeightedDiameterZeroOne
