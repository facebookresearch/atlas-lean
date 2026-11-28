/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL ORDER DIMENSION for height-one orders (fixed K >= 4): definitions

Source:
M. Yannakakis, "The complexity of the partial order dimension problem", SIAM Journal on
Algebraic and Discrete Methods 3(3) (1982), 351-358, doi:10.1137/0603036;
S. Felsner, I. Mustaţă and M. Pergel, "The complexity of the partial order dimension problem:
closing the gap", SIAM Journal on Discrete Mathematics 31(1) (2017), 172-189,
doi:10.1137/15M1007720 (records the attribution: "Yannakakis also showed that for `k ≥ 4` to
test if a partial order of height 2 has dimension `≤ k` is NP-complete"; their "height 2" counts
the elements of a longest chain, so it is "height one" here);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), open problem [OPEN7] PARTIAL ORDER DIMENSION (parent
problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PartialOrderDimensionFixedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialOrderDimensionHeightOne

/-- Well-formedness of an instance (an adjacency matrix `M`): the fixed-`K` parent instance is
well formed (`M` is `n × n`, the digraph is acyclic and transitive, and `0 < K ≤ n²`), and the
order has height one: there are no arcs `(u, v)` and `(v, w)`. -/
def WellFormed (K : ℕ) (M : List (List Bool)) : Prop :=
  PartialOrderDimensionFixed.WellFormed K M ∧
    ∀ u v w : Fin M.length,
      PartialOrderDimension.Arc (M, K) u v → ¬ PartialOrderDimension.Arc (M, K) v w

open Classical in
/-- PARTIAL ORDER DIMENSION for height-one orders with the bound fixed to `K`, as a decision
problem over bitstrings. -/
noncomputable def partialOrderDimensionHeightOneDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := List (List Bool)) x with
  | some M => decide (WellFormed K M ∧
      PartialOrderDimension.PartialOrderDimensionFeasible (M, K))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartialOrderDimensionHeightOne
