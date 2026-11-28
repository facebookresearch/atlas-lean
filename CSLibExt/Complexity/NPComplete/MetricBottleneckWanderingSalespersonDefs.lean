/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC BOTTLENECK WANDERING SALESPERSON: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MINIMUM METRIC BOTTLENECK WANDERING SALESPERSON PROBLEM;
D. S. Hochbaum and D. B. Shmoys, "A unified approach to approximation algorithms for bottleneck
problems", Journal of the ACM 33 (1986), 533-550, doi:10.1145/5925.5933 (approximable within 2,
not within `2 - ε` unless P = NP);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH BETWEEN TWO POINTS (the
special case with distances 1 and 2 described below); the tour version is [ND24] BOTTLENECK
TRAVELING SALESMAN.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricBottleneckWanderingSalesperson

open BottleneckTravelingSalesman (BottleneckTravelingSalesmanInstance dist)

/-- An instance: the number of cities `m`, the distance matrix and the bound `K`
(`BottleneckTravelingSalesmanWanted`'s instance), the initial city `s`, and the final city
`f`. -/
abbrev MetricBottleneckWanderingSalespersonInstance :=
  BottleneckTravelingSalesmanInstance × ℕ × ℕ

/-- Well-formedness of an instance: `BottleneckTravelingSalesman.WellFormed` (`m ≥ 1`; the
distances form an `m × m` symmetric matrix with zero diagonal and positive off-diagonal entries;
`K` is positive), the triangle inequality, and `s` and `f` are cities. -/
def WellFormed (i : MetricBottleneckWanderingSalespersonInstance) : Prop :=
  BottleneckTravelingSalesman.WellFormed i.1 ∧
    (∀ a < i.1.1, ∀ b < i.1.1, ∀ c < i.1.1,
      dist i.1.2.1 a c ≤ dist i.1.2.1 a b + dist i.1.2.1 b c) ∧
    i.2.1 < i.1.1 ∧ i.2.2 < i.1.1

/-- Some permutation of the cities starts at `s`, ends at `f`, and has every distance between
consecutive cities at most `K`. -/
def MetricBottleneckWanderingSalespersonFeasible
    (i : MetricBottleneckWanderingSalespersonInstance) : Prop :=
  ∃ path : List ℕ, path.Perm (List.range i.1.1) ∧ path.head? = some i.2.1 ∧
    path.getLast? = some i.2.2 ∧
    ∀ j, j + 1 < i.1.1 → dist i.1.2.1 (path.getD j 0) (path.getD (j + 1) 0) ≤ i.1.2.2

open Classical in
/-- METRIC BOTTLENECK WANDERING SALESPERSON as a decision problem over bitstrings. -/
noncomputable def metricBottleneckWanderingSalespersonDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MetricBottleneckWanderingSalespersonInstance) x with
  | some i => decide (WellFormed i ∧ MetricBottleneckWanderingSalespersonFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MetricBottleneckWanderingSalesperson
