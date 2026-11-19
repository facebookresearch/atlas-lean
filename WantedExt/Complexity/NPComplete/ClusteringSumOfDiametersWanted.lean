/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLUSTERING with the sum of cluster diameters is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS9] CLUSTERING (p. 281), comment
"Variants in which we ask that the sum, over all Xᵢ, of max{d(x,y): x,y ∈ Xᵢ} ... be at most B,
are similarly NP-complete";
P. Brucker, "On the complexity of clustering problems", in *Optimization and Operations
Research* (R. Henn, B. Korte, and W. Oettli, eds.), Lecture Notes in Economics and
Mathematical Systems 157, Springer (1978), 45-54, doi:10.1007/978-3-642-95322-4_5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import WantedExt.Complexity.NPComplete.ClusteringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClusteringSumOfDiameters

open MetaMathlibExt.Complexity.NPComplete.Clustering (ClusteringInstance)

/-!
# CLUSTERING with the sum of cluster diameters is NP-complete

INSTANCE: a finite set `X`, a distance `d(x, y) ∈ ℤ₀⁺` for each pair `x, y ∈ X`, and two
positive integers `K` and `B`. QUESTION: is there a partition of `X` into disjoint sets
`X₁, ..., X_K` such that the sum, over all `Xᵢ`, of `max {d(x, y) : x, y ∈ Xᵢ}` is at most `B`?

This is the variant of CLUSTERING ([MS9], `ClusteringWanted`) that bounds the sum of the cluster
diameters instead of every within-cluster distance. The instance type, the distance
`Clustering.distance` and `Clustering.WellFormed` (a square symmetric matrix with zero diagonal,
`0 < K`, `0 < B`) are the parent's, unchanged, and the partition is, as there, a surjective
block map `c : Fin n → Fin K` (the parts of a partition are nonempty). Splitting a singleton off
a part does not increase the sum of diameters, so for `K ≤ |X|` this is the same as a partition
into at most `K` parts; for `K > |X|` there is no partition into `K` nonempty parts.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The diameter `max {d(x, y) : x, y ∈ S}` of a set `S` of elements (`0` for `S = ∅`). -/
def diameter (i : ClusteringInstance) (S : Finset (Fin i.1.length)) : ℕ :=
  S.sup fun x => S.sup fun y => Clustering.distance i x y

/-- Some surjective assignment `c` of the `n` elements to `K` parts makes the sum, over the
parts `Xⱼ = {x : c x = j}`, of the diameters at most `B`. -/
def ClusteringSumOfDiametersFeasible (i : ClusteringInstance) : Prop :=
  ∃ c : Fin i.1.length → Fin i.2.1, Function.Surjective c ∧
    ∑ j : Fin i.2.1, diameter i (Finset.univ.filter fun x => c x = j) ≤ i.2.2

open Classical in
/-- CLUSTERING with the sum of cluster diameters as a decision problem over bitstrings. -/
noncomputable def clusteringSumOfDiametersDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ClusteringInstance) x with
  | some i => decide (Clustering.WellFormed i ∧ ClusteringSumOfDiametersFeasible i)
  | none => false

/-- **CLUSTERING with the sum of cluster diameters is NP-complete.** Source: Garey and Johnson
(1979), [MS9], comment; Brucker (1978). -/
public theorem_wanted clusteringSumOfDiameters_npComplete :
    clusteringSumOfDiametersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L clusteringSumOfDiametersDec

end MetaMathlibExt.Complexity.NPComplete.ClusteringSumOfDiameters
