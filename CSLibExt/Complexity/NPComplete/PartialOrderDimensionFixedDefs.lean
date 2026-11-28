/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL ORDER DIMENSION (fixed K >= 3): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN7] PARTIAL
ORDER DIMENSION (the fixed-`K ≥ 3` case is listed as open);
M. Yannakakis, "The complexity of the partial order dimension problem", SIAM
Journal on Algebraic and Discrete Methods 3 (1982), 351-358,
doi:10.1137/0603036.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PartialOrderDimensionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialOrderDimensionFixed

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

end MetaMathlibExt.Complexity.NPComplete.PartialOrderDimensionFixed
