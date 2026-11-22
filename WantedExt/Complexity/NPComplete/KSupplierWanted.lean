/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-SUPPLIER is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM K-SUPPLIER (decision version);
D. S. Hochbaum and D. B. Shmoys, "A unified approach to approximation algorithms for bottleneck
problems", Journal of the ACM 33(3) (1986), 533-550, doi:10.1145/5925.5933 (weighted center and
supplier problems; "for all of the problems we consider, this decision problem is
NP-complete");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND50] MIN-MAX MULTICENTER, comment
(the vertex `p`-center variant, transformation from DOMINATING SET [GT2]; O. Kariv and
S. L. Hakimi, SIAM J. Appl. Math. 37 (1979), 513-538).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KSupplier

/-!
# K-SUPPLIER is NP-complete

INSTANCE: a complete graph `G = (V, E)`, distances `d(vᵢ, vⱼ) ∈ ℕ` satisfying the triangle
inequality, a center construction cost `c(v) ∈ ℕ` and a usage weight `w(v) ∈ ℕ` for each
`v ∈ V`, a cost bound `L ∈ ℕ`, and a positive integer `K`.
QUESTION: is there a supplier set `S ⊆ V` of legal cost, `∑_{v ∈ S} c(v) ≤ L`, whose measure
`max_{v ∈ V} min_{s ∈ S} w(v) d(v, s)` (the maximum weighted distance from a vertex to its
nearest supplier) is at most `K`?

This is the decision version of the compendium's MINIMUM K-SUPPLIER. It is NP-complete in the
strong sense: with all costs and weights `1`, `L = k`, distance `1` between adjacent vertices of
a graph `H`, `2` between distinct non-adjacent vertices and `0` from a vertex to itself (a metric,
since `2 ≤ 1 + 1`), and `K = 1`, a legal supplier set is a set of at most `k` vertices dominating
`H`, so DOMINATING SET ([GT2]) reduces to it; this is the transformation behind the vertex
`p`-center variant of [ND50] (Kariv and Hakimi). An explicit supplier set is a certificate for
membership in NP.

The vertices are `0, …, n - 1`. The distances are an `n × n` matrix, symmetric (the graph is
undirected), with zero diagonal (the distance from a vertex to itself, which the measure uses
when `v ∈ S`) and satisfying `d(a, c) ≤ d(a, b) + d(b, c)`, as in `TravelingRepairmanWanted`. The
costs and the weights are lists of length `n`. "The maximum over `v` of the minimum over `s ∈ S`
is at most `K`" is stated as: every vertex `v` has a supplier `s ∈ S` with `w(v) · d(v, s) ≤ K`.
`WellFormed` also requires `0 < K` (the record's "positive integer K").

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n`, distance matrix, construction costs `c`, usage weights `w`,
cost bound `L`, and bound `K`. -/
abbrev KSupplierInstance := ℕ × List (List ℕ) × List ℕ × List ℕ × ℕ × ℕ

/-- The distance `d(a, b)`, read from the matrix. -/
def distance (i : KSupplierInstance) (a b : ℕ) : ℕ :=
  (i.2.1.getD a []).getD b 0

/-- Well-formedness of an instance: an `n × n` distance matrix that is symmetric, has zero
diagonal and satisfies the triangle inequality, cost and weight lists of length `n`, and
`0 < K`. -/
def WellFormed (i : KSupplierInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    i.2.2.1.length = i.1 ∧ i.2.2.2.1.length = i.1 ∧
    (∀ a < i.1, distance i a a = 0) ∧
    (∀ a < i.1, ∀ b < i.1, distance i a b = distance i b a) ∧
    (∀ a < i.1, ∀ b < i.1, ∀ c < i.1, distance i a c ≤ distance i a b + distance i b c) ∧
    0 < i.2.2.2.2.2

/-- A supplier set of total construction cost at most `L` such that every vertex `v` has a
supplier `s` with `w(v) · d(v, s) ≤ K`. -/
def KSupplierFeasible (i : KSupplierInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ s ∈ S, s < i.1) ∧ ∑ s ∈ S, i.2.2.1.getD s 0 ≤ i.2.2.2.2.1 ∧
    ∀ v < i.1, ∃ s ∈ S, i.2.2.2.1.getD v 0 * distance i v s ≤ i.2.2.2.2.2

open Classical in
/-- K-SUPPLIER as a decision problem over bitstrings. -/
noncomputable def kSupplierDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KSupplierInstance) x with
  | some i => decide (WellFormed i ∧ KSupplierFeasible i)
  | none => false

/-- **K-SUPPLIER is NP-complete.** Source: Crescenzi and Kann, MINIMUM K-SUPPLIER; Hochbaum and
Shmoys (1986); Garey and Johnson (1979), [ND50], [GT2]. -/
public theorem_wanted kSupplier_npComplete :
    kSupplierDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kSupplierDec

end MetaMathlibExt.Complexity.NPComplete.KSupplier
