/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLUSTERING with the sum of within-cluster distances: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS9] CLUSTERING (p. 281), comment
"Variants in which we ask that the sum, over all Xᵢ, of ... Σ_{x,y ∈ Xᵢ} d(x,y) be at most B,
are similarly NP-complete (with the last one NP-complete even for K = 2)";
P. Brucker, "On the complexity of clustering problems", in *Optimization and Operations
Research* (R. Henn, B. Korte, and W. Oettli, eds.), Lecture Notes in Economics and
Mathematical Systems 157, Springer (1978), 45-54, doi:10.1007/978-3-642-95322-4_5.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.ClusteringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClusteringSumOfDistances

open MetaMathlibExt.Complexity.NPComplete.Clustering (ClusteringInstance)

/-- Some surjective assignment `c` of the `n` elements to `K` parts makes the sum, over the
parts `Xⱼ = {x : c x = j}`, of `Σ_{x, y ∈ Xⱼ} d(x, y)` at most `B`. -/
def ClusteringSumOfDistancesFeasible (i : ClusteringInstance) : Prop :=
  ∃ c : Fin i.1.length → Fin i.2.1, Function.Surjective c ∧
    ∑ j : Fin i.2.1, ∑ x ∈ Finset.univ.filter (fun x => c x = j),
      ∑ y ∈ Finset.univ.filter (fun y => c y = j), Clustering.distance i x y ≤ i.2.2

open Classical in
/-- CLUSTERING with the sum of within-cluster distances as a decision problem over
bitstrings. -/
noncomputable def clusteringSumOfDistancesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ClusteringInstance) x with
  | some i => decide (Clustering.WellFormed i ∧ ClusteringSumOfDistancesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ClusteringSumOfDistances
