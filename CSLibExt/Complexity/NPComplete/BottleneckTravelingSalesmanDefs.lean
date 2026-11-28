/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOTTLENECK TRAVELING SALESMAN: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND24] BOTTLENECK TRAVELING
SALESMAN (transformation from HAMILTONIAN CIRCUIT; NP-complete even with all distances in
`{1, 2}`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BottleneckTravelingSalesman

/-- An instance: the number of cities `m`, the distance matrix, and the bound `B`. -/
abbrev BottleneckTravelingSalesmanInstance := ℕ × List (List ℕ) × ℕ

/-- The distance from city `a` to city `b`. -/
def dist (d : List (List ℕ)) (a b : ℕ) : ℕ := (d.getD a []).getD b 0

/-- Well-formedness of an instance: `m ≥ 1`; the distances form an `m × m` symmetric matrix
with zero diagonal and positive off-diagonal entries; and `B` is positive. -/
def WellFormed (i : BottleneckTravelingSalesmanInstance) : Prop :=
  0 < i.1 ∧ i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    (∀ a < i.1, ∀ b < i.1, dist i.2.1 a b = dist i.2.1 b a) ∧
    (∀ a < i.1, dist i.2.1 a a = 0) ∧ (∀ a < i.1, ∀ b < i.1, a ≠ b → 0 < dist i.2.1 a b) ∧
    0 < i.2.2

/-- Some tour has every edge, the return edge included, of length at most `B`. -/
def BottleneckTravelingSalesmanFeasible (i : BottleneckTravelingSalesmanInstance) : Prop :=
  ∃ tour : List ℕ, tour.Perm (List.range i.1) ∧
    ∀ j < i.1, dist i.2.1 (tour.getD j 0) (tour.getD ((j + 1) % i.1) 0) ≤ i.2.2

open Classical in
/-- BOTTLENECK TRAVELING SALESMAN as a decision problem over bitstrings. -/
noncomputable def bottleneckTravelingSalesmanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BottleneckTravelingSalesmanInstance) x with
  | some i => decide (WellFormed i ∧ BottleneckTravelingSalesmanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BottleneckTravelingSalesman
