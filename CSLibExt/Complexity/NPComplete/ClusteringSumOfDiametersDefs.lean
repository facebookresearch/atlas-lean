/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLUSTERING with the sum of cluster diameters: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import CSLibExt.Complexity.NPComplete.ClusteringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClusteringSumOfDiameters

open MetaMathlibExt.Complexity.NPComplete.Clustering (ClusteringInstance)

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

end MetaMathlibExt.Complexity.NPComplete.ClusteringSumOfDiameters
