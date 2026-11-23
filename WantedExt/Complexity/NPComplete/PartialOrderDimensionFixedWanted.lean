/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL ORDER DIMENSION (fixed K >= 3) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN7] PARTIAL
ORDER DIMENSION (the fixed-`K ≥ 3` case is listed as open);
M. Yannakakis, "The complexity of the partial order dimension problem", SIAM
Journal on Algebraic and Discrete Methods 3 (1982), 351-358,
doi:10.1137/0603036.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PartialOrderDimensionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialOrderDimensionFixed

/-!
# PARTIAL ORDER DIMENSION (fixed K >= 3) is NP-complete

For a fixed integer `K ≥ 3`: INSTANCE: a directed acyclic graph `G = (V, A)` that is
transitive, i.e., whenever `(u, v) ∈ A` and `(v, w) ∈ A`, then `(u, w) ∈ A`, with
`K ≤ |V|²`. QUESTION: does there exist a collection of `k ≤ K` linear orderings of `V` such
that `(u, v) ∈ A` if and only if `u` is less than `v` in each of the orderings?

This is PARTIAL ORDER DIMENSION (`MetaMathlibExt.Complexity.NPComplete.PartialOrderDimension`)
with the bound `K` fixed instead of part of the instance. The instance is the adjacency matrix
alone; the parent's instance is the pair of the matrix and the fixed `K`, and the parent's
well-formedness conditions (including Garey and Johnson's `K ≤ |V|²`) and question are reused
unchanged.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance (an adjacency matrix `M`): the parent instance `(M, K)` is
well formed (`M` is `n × n`, the digraph is acyclic and transitive, and `0 < K ≤ n²`). -/
def WellFormed (K : ℕ) (M : List (List Bool)) : Prop :=
  PartialOrderDimension.WellFormed (M, K)

open Classical in
/-- PARTIAL ORDER DIMENSION with the bound fixed to `K`, as a decision problem over
bitstrings. -/
noncomputable def partialOrderDimensionFixedDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := List (List Bool)) x with
  | some M => decide (WellFormed K M ∧
      PartialOrderDimension.PartialOrderDimensionFeasible (M, K))
  | none => false

/-- **PARTIAL ORDER DIMENSION (fixed K >= 3) is NP-complete.** For every fixed `K ≥ 3`,
deciding whether a partial order has dimension at most `K` is NP-complete. Source: Garey and
Johnson (1979), [OPEN7]; Yannakakis (1982). -/
public theorem_wanted partialOrderDimensionFixed_npComplete (K : ℕ) (_hK : 3 ≤ K) :
    partialOrderDimensionFixedDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (partialOrderDimensionFixedDec K)

end MetaMathlibExt.Complexity.NPComplete.PartialOrderDimensionFixed
