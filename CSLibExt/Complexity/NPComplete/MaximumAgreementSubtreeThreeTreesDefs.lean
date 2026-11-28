/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM AGREEMENT SUBTREE for three trees: definitions

Source:
A. Amir and D. Keselman, "Maximum agreement subtree in a set of evolutionary trees: metrics and
efficient algorithms", SIAM Journal on Computing 26(6) (1997), 1656-1669,
doi:10.1137/S0097539794269461 (the maximum homeomorphic agreement subtree problem is
NP-complete for three trees with unbounded degrees);
C. Semple and M. Steel, *Phylogenetics*, Oxford University Press (2003), Section 3.5 (rooted
phylogenetic trees correspond to their cluster systems, the hierarchies).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Bioinformatics.Phylogenetics.Splits

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumAgreementSubtreeThreeTrees

open Cslib.Bioinformatics.Phylogenetics.Splits (IsHierarchy)

/-- An instance: the number `n` of leaves, the cluster lists of the three trees, and the bound
`K`. -/
abbrev MaximumAgreementSubtreeThreeTreesInstance :=
  ℕ × List (List ℕ) × List (List ℕ) × List (List ℕ) × ℕ

/-- The cluster system of a tree on the leaves `Fin n`, from its cluster lists. -/
def clusters (n : ℕ) (T : List (List ℕ)) : Finset (Finset (Fin n)) :=
  (T.map fun c => Finset.univ.filter fun x : Fin n => (x : ℕ) ∈ c).toFinset

/-- The cluster system of the homeomorphic subtree `T|Y`: the nonempty sets `C ∩ Y` for the
clusters `C` of `T`. -/
def restrict {n : ℕ} (H : Finset (Finset (Fin n))) (Y : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (H.image fun C => C ∩ Y).filter fun C => C.Nonempty

/-- Well-formedness of an instance: every listed leaf is in `X = Fin n`, and each tree's clusters
form a hierarchy on `X`. -/
def WellFormed (i : MaximumAgreementSubtreeThreeTreesInstance) : Prop :=
  (∀ T ∈ [i.2.1, i.2.2.1, i.2.2.2.1], ∀ c ∈ T, ∀ x ∈ c, x < i.1) ∧
    IsHierarchy Finset.univ (clusters i.1 i.2.1) ∧
    IsHierarchy Finset.univ (clusters i.1 i.2.2.1) ∧
    IsHierarchy Finset.univ (clusters i.1 i.2.2.2.1)

/-- Some set `Y` of at least `K` leaves on which the three trees agree: `T₁|Y`, `T₂|Y` and
`T₃|Y` have the same cluster system. -/
def MaximumAgreementSubtreeThreeTreesFeasible
    (i : MaximumAgreementSubtreeThreeTreesInstance) : Prop :=
  ∃ Y : Finset (Fin i.1), i.2.2.2.2 ≤ Y.card ∧
    restrict (clusters i.1 i.2.1) Y = restrict (clusters i.1 i.2.2.1) Y ∧
    restrict (clusters i.1 i.2.2.1) Y = restrict (clusters i.1 i.2.2.2.1) Y

open Classical in
/-- MAXIMUM AGREEMENT SUBTREE for three trees as a decision problem over bitstrings. -/
noncomputable def maximumAgreementSubtreeThreeTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumAgreementSubtreeThreeTreesInstance) x with
  | some i => decide (WellFormed i ∧ MaximumAgreementSubtreeThreeTreesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumAgreementSubtreeThreeTrees
