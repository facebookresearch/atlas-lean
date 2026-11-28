/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HIERARCHICAL-TREE CLUSTERING (ℓ₁ ultrametric fitting): definitions

Source:
M. Křivánek and J. Morávek, "NP-hard problems in hierarchical-tree clustering", Acta
Informatica 23 (1986), 311-323, doi:10.1007/BF00289116;
M. Křivánek, "The complexity of ultrametric partitions on graphs", Information Processing
Letters 27 (1988), 265-270, doi:10.1016/0020-0190(88)90090-7, problem (P6).
-/
module

public import CSLibExt.Bioinformatics.Phylogenetics.Splits
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HierarchicalTreeClustering

open Cslib.Bioinformatics.Phylogenetics.Splits (IsUltrametric)

/-- An instance: the rows of the dissimilarity matrix `w` and the bound `K`. -/
abbrev HierarchicalTreeClusteringInstance := List (List ℕ) × ℕ

/-- The entry `w(a, b)` of the matrix. -/
def entry (i : HierarchicalTreeClusteringInstance) (a b : ℕ) : ℕ :=
  (i.1.getD a []).getD b 0

/-- Well-formedness of an instance: the matrix is square, symmetric, zero exactly on the
diagonal, and `K` is positive. -/
def WellFormed (i : HierarchicalTreeClusteringInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.1.length) ∧
    (∀ a < i.1.length, ∀ b < i.1.length,
      (entry i a b = 0 ↔ a = b) ∧ entry i a b = entry i b a) ∧ 0 < i.2

/-- Some ultrametric `u` on `Fin n` has `∑_{x < y} |u(x, y) - w(x, y)| ≤ K`. -/
def HierarchicalTreeClusteringFeasible (i : HierarchicalTreeClusteringInstance) : Prop :=
  ∃ u : Fin i.1.length → Fin i.1.length → ℝ, IsUltrametric u ∧
    ∑ x : Fin i.1.length, ∑ y ∈ Finset.univ.filter (x < ·),
      |u x y - (entry i x y : ℝ)| ≤ i.2

open Classical in
/-- HIERARCHICAL-TREE CLUSTERING as a decision problem over bitstrings. -/
noncomputable def hierarchicalTreeClusteringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HierarchicalTreeClusteringInstance) x with
  | some i => decide (WellFormed i ∧ HierarchicalTreeClusteringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HierarchicalTreeClustering
