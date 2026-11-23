/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL ORDER DIMENSION for height-one orders (fixed K >= 4) is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PartialOrderDimensionFixedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialOrderDimensionHeightOne

/-!
# PARTIAL ORDER DIMENSION for height-one orders (fixed K >= 4) is NP-complete

For a fixed integer `K ≥ 4`: INSTANCE: a partial order `(V, <)` of height one, i.e. with no
chain of more than two elements (every element is minimal or maximal), given as a directed
acyclic transitive graph `G = (V, A)` with `(u, v) ∈ A` iff `u < v`, with `K ≤ |V|²`.
QUESTION: is the dimension of `(V, <)` at most `K`, i.e. is there a collection of `k ≤ K` linear
orderings of `V` such that `(u, v) ∈ A` if and only if `u` is less than `v` in each of them?

This is PARTIAL ORDER DIMENSION with the bound fixed
(`WantedExt.Complexity.NPComplete.PartialOrderDimensionFixedWanted`) restricted to orders of
height one: the instance (an adjacency matrix), the parent's well-formedness (square matrix,
acyclic, transitive, `0 < K ≤ |V|²`) and the question are reused unchanged, and the restriction
is added to well-formedness: no arcs `(u, v)` and `(v, w)` both exist, so no chain has three
elements. Garey and Johnson's `K ≤ |V|²` (inherited) only excludes orders with fewer than
`√K` elements, which have dimension at most `K` anyway.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PARTIAL ORDER DIMENSION for height-one orders (fixed K >= 4) is NP-complete.** For every
fixed `K ≥ 4`, deciding whether a partial order of height one has dimension at most `K` is
NP-complete. Source: Yannakakis (1982); Felsner, Mustaţă and Pergel (2017). -/
public theorem_wanted partialOrderDimensionHeightOne_npComplete (K : ℕ) (_hK : 4 ≤ K) :
    partialOrderDimensionHeightOneDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (partialOrderDimensionHeightOneDec K)

end MetaMathlibExt.Complexity.NPComplete.PartialOrderDimensionHeightOne
