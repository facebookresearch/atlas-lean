/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC BOTTLENECK WANDERING SALESPERSON is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MetricBottleneckWanderingSalespersonDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricBottleneckWanderingSalesperson

open BottleneckTravelingSalesman (BottleneckTravelingSalesmanInstance dist)

/-!
# METRIC BOTTLENECK WANDERING SALESPERSON is NP-complete

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

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **METRIC BOTTLENECK WANDERING SALESPERSON is NP-complete.** Source: Crescenzi and Kann,
MINIMUM METRIC BOTTLENECK WANDERING SALESPERSON PROBLEM; Hochbaum and Shmoys (1986). The special
case with distances 1 and 2 is Garey and Johnson (1979), [GT39]. -/
public theorem_wanted metricBottleneckWanderingSalesperson_npComplete :
    metricBottleneckWanderingSalespersonDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L metricBottleneckWanderingSalespersonDec

end MetaMathlibExt.Complexity.NPComplete.MetricBottleneckWanderingSalesperson
