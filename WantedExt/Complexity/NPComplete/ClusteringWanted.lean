/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLUSTERING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS9] CLUSTERING;
P. Brucker, "On the complexity of clustering problems", in *Optimization and Operations
Research* (R. Henn, B. Korte, and W. Oettli, eds.), Lecture Notes in Economics and
Mathematical Systems 157, Springer (1978), 45-54, doi:10.1007/978-3-642-95322-4_5;
T. F. Gonzalez, "Clustering to minimize the maximum intercluster distance", Theoretical
Computer Science 38 (1985), 293-306, doi:10.1016/0304-3975(85)90224-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Clustering

/-!
# CLUSTERING is NP-complete

INSTANCE: a finite set `X`, a distance `d(x, y) ∈ ℤ₀⁺` for each pair `x, y ∈ X`, and two
positive integers `K` and `B`. QUESTION: is there a partition of `X` into disjoint sets
`X₁, ..., X_K` such that, for `1 ≤ i ≤ K` and all pairs `x, y ∈ Xᵢ`, `d(x, y) ≤ B`?

Elements are `0, ..., n - 1`; the distance is a symmetric `n × n` matrix with zero diagonal.
The partition is a surjective block map `c : Fin n → Fin K` (the parts of a partition are
nonempty). Any subset of a part is again a valid part, so for `K ≤ |X|` this is the same as a
partition into at most `K` parts; for `K > |X|` there is no partition into `K` nonempty parts.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the rows of the distance matrix (`n` rows of length `n`), the number of
parts `K`, and the bound `B`. -/
abbrev ClusteringInstance := List (List ℕ) × ℕ × ℕ

/-- The distance `d(x, y)`: entry `(x, y)` of the matrix (`0` outside it). -/
def distance (i : ClusteringInstance) (x y : ℕ) : ℕ := (i.1.getD x []).getD y 0

/-- Well-formedness of an instance: the matrix is square, symmetric, and zero on the diagonal,
and `0 < K`, `0 < B`. -/
def WellFormed (i : ClusteringInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.1.length) ∧
    (∀ x < i.1.length, ∀ y < i.1.length, distance i x y = distance i y x) ∧
    (∀ x < i.1.length, distance i x x = 0) ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- Some surjective assignment `c` of the `n` elements to `K` parts puts only elements at
distance at most `B` into a common part. -/
def ClusteringFeasible (i : ClusteringInstance) : Prop :=
  ∃ c : Fin i.1.length → Fin i.2.1, Function.Surjective c ∧
    ∀ x y, c x = c y → distance i x y ≤ i.2.2

open Classical in
/-- CLUSTERING as a decision problem over bitstrings. -/
noncomputable def clusteringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ClusteringInstance) x with
  | some i => decide (WellFormed i ∧ ClusteringFeasible i)
  | none => false

/-- **CLUSTERING is NP-complete.** Source: Garey and Johnson (1979), [MS9]; Brucker (1978);
Gonzalez (1985). -/
public theorem_wanted clustering_npComplete :
    clusteringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L clusteringDec

end MetaMathlibExt.Complexity.NPComplete.Clustering
