/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# TRAVELING REPAIRMAN (MINIMUM LATENCY): definitions

INSTANCE: `n` locations `0, …, n - 1` with a distance matrix `t[a, b] ∈ ℕ` that satisfies the
triangle inequality (symmetric, with zero diagonal), a distinguished starting location `s`, and
a bound `K`. QUESTION: is there a permutation `π(0) = s, π(1), …, π(n - 1)` of the locations
whose total latency `∑_{i=1}^{n-1} ∑_{j=1}^{i} t[π(j - 1), π(j)]` is at most `K`?

The cost is Afrati et al.'s (1986) formula: the latency of `π(i)` is the distance traveled from
`s` until `π(i)` is first visited, and the total latency is their sum (the latency of `s` itself
is `0`). The instance class is that of Crescenzi and Kann's MINIMUM TRAVELING REPAIRMAN and of Blum
et al. (1994): nonnegative integer lengths satisfying the triangle inequality. With the triangle
inequality, visiting the locations in the order `π` along direct legs is no worse than any walk that
first visits them in that order, so permutations capture the compendium entry's walks. Afrati et al.
state the general version NP-complete (crediting Sahni and Gonzalez 1976); Blum et al. observe that
a reduction from the traveling salesman problem makes the problem NP-hard already for points in
the plane, and Sitters (2002) proves it NP-hard for the shortest-path metrics of weighted
trees. The route is listed as a permutation of
`List.range n` that starts at `s`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
F. Afrati, S. Cosmadakis, C. H. Papadimitriou, G. Papageorgiou, and N. Papakostantinou,
"The complexity of the travelling repairman problem", RAIRO Theoretical Informatics and
Applications 20 (1986), 79-87, doi:10.1051/ita/1986200100791 (definition of the problem;
NP-completeness of the general version, credited there to S. Sahni and T. Gonzalez,
"P-complete approximation problems", Journal of the ACM 23 (1976), 555-565,
doi:10.1145/321958.321975);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM TRAVELING REPAIRMAN (metric instances);
A. Blum, P. Chalasani, D. Coppersmith, B. Pulleyblank, P. Raghavan, and M. Sudan, "The minimum
latency problem", Proc. 26th ACM Symposium on Theory of Computing (1994), 163-171,
doi:10.1145/195058.195125 (NP-hard for points in the plane);
R. Sitters, "The minimum latency problem is NP-hard for weighted trees", Integer Programming
and Combinatorial Optimization (IPCO 2002), LNCS 2337, 230-239,
doi:10.1007/3-540-47867-1_17.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TravelingRepairman

/-- An instance: the number `n` of locations, the distance matrix as `n` rows of `n` entries
(`t[a, b]` is entry `b` of row `a`), the starting location `s`, and the bound `K`. -/
abbrev TravelingRepairmanInstance := ℕ × List (List ℕ) × ℕ × ℕ

/-- The distance `t[a, b]`: entry `b` of row `a` of the matrix (`0` outside it). -/
def dist (i : TravelingRepairmanInstance) (a b : ℕ) : ℕ :=
  (i.2.1.getD a []).getD b 0

/-- The length of the route visiting the listed locations in order: the sum of
`t[a, b]` over consecutive entries `a, b`. -/
def routeLength (i : TravelingRepairmanInstance) (route : List ℕ) : ℕ :=
  ((route.zip route.tail).map fun p => dist i p.1 p.2).sum

/-- The total latency of a route `π(0), …, π(n - 1)`: the sum over positions `k` of the length
of its prefix `π(0), …, π(k)`, i.e. `∑_{k} ∑_{j=1}^{k} t[π(j - 1), π(j)]`. -/
def totalLatency (i : TravelingRepairmanInstance) (route : List ℕ) : ℕ :=
  ∑ k ∈ Finset.range route.length, routeLength i (route.take (k + 1))

/-- Well-formedness of an instance: the matrix has `n` rows of `n` entries, `s < n`, and the
distances form a metric on the locations in the sense of the compendium entry: `t[a, a] = 0`,
`t[a, b] = t[b, a]`, and `t[a, c] ≤ t[a, b] + t[b, c]`. -/
def WellFormed (i : TravelingRepairmanInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧ i.2.2.1 < i.1 ∧
    (∀ a < i.1, dist i a a = 0) ∧
    (∀ a < i.1, ∀ b < i.1, dist i a b = dist i b a) ∧
    ∀ a < i.1, ∀ b < i.1, ∀ c < i.1, dist i a c ≤ dist i a b + dist i b c

/-- Some route, a permutation of the locations starting at `s`, has total latency at most
`K`. -/
def TravelingRepairmanFeasible (i : TravelingRepairmanInstance) : Prop :=
  ∃ route : List ℕ, route.Perm (List.range i.1) ∧ route.head? = some i.2.2.1 ∧
    totalLatency i route ≤ i.2.2.2

open Classical in
/-- TRAVELING REPAIRMAN (MINIMUM LATENCY) as a decision problem over bitstrings. -/
noncomputable def travelingRepairmanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TravelingRepairmanInstance) x with
  | some i => decide (WellFormed i ∧ TravelingRepairmanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TravelingRepairman
