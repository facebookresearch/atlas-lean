/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM ULTRAMETRIC TREE: definitions

Source:
B. Y. Wu, K.-M. Chao and C. Y. Tang, "Approximation and exact algorithms for constructing
minimum ultrametric trees from distance matrices", Journal of Combinatorial Optimization 3
(1999), 199-211, doi:10.1023/A:1009885610075 (the minimum ultrametric tree problem is NP-hard,
also when the distance matrix is a metric);
M. Křivánek and J. Morávek, "NP-hard problems in hierarchical-tree clustering", Acta
Informatica 23 (1986), 311-323, doi:10.1007/BF00289116.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Bioinformatics.Phylogenetics.Splits

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumUltrametricTree

open Cslib.Bioinformatics.Phylogenetics.Splits (IsHierarchy)

/-- An instance: the rows of the matrix `M` and the bound `K`. -/
abbrev MinimumUltrametricTreeInstance := List (List ℕ) × ℕ

/-- The entry `M[i, j]` of the matrix. -/
def entry (i : MinimumUltrametricTreeInstance) (a b : ℕ) : ℕ :=
  (i.1.getD a []).getD b 0

/-- Well-formedness of an instance: there is at least one species, `M` is square, and it is a
metric: zero diagonal, positive and symmetric off-diagonal entries, and the triangle
inequality. -/
def WellFormed (i : MinimumUltrametricTreeInstance) : Prop :=
  0 < i.1.length ∧ (∀ row ∈ i.1, row.length = i.1.length) ∧
    ∀ a < i.1.length, ∀ b < i.1.length, (a = b ↔ entry i a b = 0) ∧
      entry i a b = entry i b a ∧ ∀ c < i.1.length, entry i a c ≤ entry i a b + entry i b c

/-- Some dated hierarchy (an ultrametric tree with leaves `Fin n`) has every leaf distance at
least the matrix entry and total edge weight at most `K`. -/
def MinimumUltrametricTreeFeasible (i : MinimumUltrametricTreeInstance) : Prop :=
  ∃ (H : Finset (Finset (Fin i.1.length))) (h : Finset (Fin i.1.length) → ℝ)
    (par : Finset (Fin i.1.length) → Finset (Fin i.1.length)),
    IsHierarchy Finset.univ H ∧ (∀ x, h {x} = 0) ∧ (∀ C ∈ H, ∀ D ∈ H, C ⊂ D → h C < h D) ∧
    (∀ C ∈ H, C ≠ Finset.univ → par C ∈ H ∧ C ⊂ par C ∧ ∀ D ∈ H, C ⊂ D → par C ⊆ D) ∧
    (∀ x y, x ≠ y → ∀ C ∈ H, x ∈ C → y ∈ C → (∀ D ∈ H, x ∈ D → y ∈ D → C ⊆ D) →
      (entry i x y : ℝ) ≤ h C) ∧
    ∑ C ∈ H.erase Finset.univ, (h (par C) - h C) / 2 ≤ i.2

open Classical in
/-- MINIMUM ULTRAMETRIC TREE as a decision problem over bitstrings. -/
noncomputable def minimumUltrametricTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumUltrametricTreeInstance) x with
  | some i => decide (WellFormed i ∧ MinimumUltrametricTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumUltrametricTree
