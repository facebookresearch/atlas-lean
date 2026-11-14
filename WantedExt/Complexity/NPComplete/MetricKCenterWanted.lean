/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC K-CENTER is NP-complete

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem [ND54]
MINIMUM K-CENTER;
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. I: The
p-centers", SIAM Journal on Applied Mathematics 37 (1979), 513-538, doi:10.1137/0137040.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.KCenterWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricKCenter

open KCenter (KCenterInstance KCenterFeasible)

/-!
# METRIC K-CENTER is NP-complete

INSTANCE: a complete graph `G = (V, E)` with distances `d(vᵢ, vⱼ) ∈ ℕ` satisfying the triangle
inequality, a positive integer `k ≤ |V|`, and a positive integer `B`.
QUESTION: is there a `k`-center set, i.e. a subset `C ⊆ V` with `|C| = k`, such that
`max_{v ∈ V} min_{c ∈ C} d(v, c) ≤ B`?

This is the decision version of MINIMUM K-CENTER from the Crescenzi-Kann compendium ([ND54]).
Its NP-hardness is the vertex p-center result of Kariv and Hakimi (the shortest-path distances
of a connected network with positive edge lengths form a metric).

The module restricts the generalized, nonmetric k-center problem
`WantedExt.Complexity.NPComplete.KCenterWanted` (whose docstring names the metric problem as its
special case): it reuses the parent's instance and feasibility condition unchanged and extends
the parent's `WellFormed`. The instance `(d, k, B)` is the distance matrix, one row per vertex,
the number of centers and the radius. `WellFormed` adds the metric conditions: the matrix is
square, `d(u, v) = 0` exactly when `u = v` (the distance from a vertex to itself is zero; the
complete graph has no loops), it is symmetric (the graph is undirected) and it satisfies the
triangle inequality; and the bounds `0 < k ≤ |V|` and `0 < B`. With rows and columns both
indexed by `V`, the parent's condition (at most `k` distinct centers and an assignment of every
vertex to a center within distance `B`) says that some `C ⊆ V` with `|C| ≤ k` has
`min_{c ∈ C} d(v, c) ≤ B` for every `v`; since `k ≤ |V|` and adding centers never increases a
distance to the nearest center, this is the same as `|C| = k`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The distance `d(u, v)`: entry `v` of row `u` of the matrix. -/
def distance (i : KCenterInstance) (u v : ℕ) : ℕ := (i.1.getD u []).getD v 0

/-- Well-formedness of an instance: the parent's condition, a square matrix that is a metric
(zero exactly on the diagonal, symmetric, triangle inequality), `0 < k ≤ |V|`, and `0 < B`. -/
def WellFormed (i : KCenterInstance) : Prop :=
  KCenter.WellFormed i ∧ (∀ row ∈ i.1, row.length = i.1.length) ∧
    (∀ u < i.1.length, ∀ v < i.1.length, distance i u v = 0 ↔ u = v) ∧
    (∀ u < i.1.length, ∀ v < i.1.length, distance i u v = distance i v u) ∧
    (∀ u < i.1.length, ∀ v < i.1.length, ∀ w < i.1.length,
      distance i u w ≤ distance i u v + distance i v w) ∧
    0 < i.2.1 ∧ i.2.1 ≤ i.1.length ∧ 0 < i.2.2

open Classical in
/-- METRIC K-CENTER as a decision problem over bitstrings. -/
noncomputable def metricKCenterDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KCenterInstance) x with
  | some i => decide (WellFormed i ∧ KCenterFeasible i)
  | none => false

/-- **METRIC K-CENTER is NP-complete.** Source: Crescenzi and Kann, [ND54]; Kariv and Hakimi
(1979). -/
public theorem_wanted metricKCenter_npComplete :
    metricKCenterDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L metricKCenterDec

end MetaMathlibExt.Complexity.NPComplete.MetricKCenter
