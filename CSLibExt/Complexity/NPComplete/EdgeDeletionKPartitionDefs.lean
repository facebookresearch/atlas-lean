/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE DELETION k-PARTITION: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM EDGE DELETION K-PARTITION;
V. Kann, S. Khanna, J. Lagergren and A. Panconesi, "On the hardness of approximating Max k-Cut
and its dual", Chicago J. Theoret. Comput. Sci. 1997, Article 2 (the Min k-Partition problem);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT (the case `k = 2`, by
complementing the bound).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeDeletionKPartition

/-- An instance: vertex count `n`, weighted edge list `(u, v, w)` and bound `K`. -/
abbrev EdgeDeletionKPartitionInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- The unweighted edges of an instance. -/
def edges (i : EdgeDeletionKPartitionInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- Well-formedness of an instance: the edges are distinct, in range, without loops or repeated
pairs; every weight is positive; and `0 < K`. -/
def WellFormed (i : EdgeDeletionKPartitionInstance) : Prop :=
  (edges i).Nodup ∧
    (∀ e ∈ edges i, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ edges i) ∧
    (∀ e ∈ i.2.1, 0 < e.2.2) ∧ 0 < i.2.2

/-- The weight of the edges whose endpoints get the same color under `c`. -/
def monochromaticWeight (i : EdgeDeletionKPartitionInstance) (c : List ℕ) : ℕ :=
  ((i.2.1.filter fun e => c.getD e.1 0 = c.getD e.2.1 0).map fun e => e.2.2).sum

/-- Some assignment of colors below `k` to the vertices has monochromatic weight at most `K`. -/
def EdgeDeletionKPartitionFeasible (k : ℕ) (i : EdgeDeletionKPartitionInstance) : Prop :=
  ∃ c : List ℕ, c.length = i.1 ∧ (∀ v < i.1, c.getD v 0 < k) ∧ monochromaticWeight i c ≤ i.2.2

open Classical in
/-- EDGE DELETION k-PARTITION, for the fixed `k`, as a decision problem over bitstrings. -/
noncomputable def edgeDeletionKPartitionDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeDeletionKPartitionInstance) x with
  | some i => decide (WellFormed i ∧ EdgeDeletionKPartitionFeasible k i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EdgeDeletionKPartition
