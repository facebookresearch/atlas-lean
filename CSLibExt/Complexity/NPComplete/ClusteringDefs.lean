/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLUSTERING: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Clustering

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

end MetaMathlibExt.Complexity.NPComplete.Clustering
