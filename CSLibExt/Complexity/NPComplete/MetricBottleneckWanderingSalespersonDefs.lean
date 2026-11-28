/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDefs

/-!
# METRIC BOTTLENECK WANDERING SALESPERSON: definitions

INSTANCE: a set `C` of `m` cities, an initial city `s ∈ C`, a final city `f ∈ C`, distances
`d(cᵢ, cⱼ) ∈ ℕ` satisfying the triangle inequality (a metric), and a positive integer `K`.
QUESTION: is there a simple path from `s` to `f` through all cities of `C`, i.e. a permutation
`c_π(1), …, c_π(m)` of `C` with `c_π(1) = s` and `c_π(m) = f`, whose largest distance
`max_{1 ≤ i < m} d(c_π(i), c_π(i+1))` is at most `K`?

This is the decision version of MINIMUM METRIC BOTTLENECK WANDERING SALESPERSON PROBLEM in the
compendium of Crescenzi and Kann. With distances `1` and `2` (a metric) and `K = 1`, the
question is whether the graph of the pairs at distance `1` has a Hamiltonian path from `s` to
`f`.

The instance extends the one of `BottleneckTravelingSalesmanWanted` (number of cities `m`,
distance matrix, bound `K`; `BottleneckTravelingSalesman.dist` reads the matrix) with `s` and
`f`. The cities are `0, …, m - 1` with `m ≥ 1`; the distances form an `m × m` symmetric matrix
with zero diagonal and positive off-diagonal entries (`BottleneckTravelingSalesman.WellFormed`),
so they are a metric when they also satisfy the triangle inequality. A path is a permutation of
the cities, given as a list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

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

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricBottleneckWanderingSalesperson

open BottleneckTravelingSalesman (BottleneckTravelingSalesmanInstance dist)

/-- An instance: the number of cities `m`, the distance matrix and the bound `K`
(`BottleneckTravelingSalesman.BottleneckTravelingSalesmanInstance`), and the initial and final
cities `s` and `f`. -/
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
