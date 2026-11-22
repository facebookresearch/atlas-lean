/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM AGREEMENT SUBTREE for three trees is NP-complete

Source:
A. Amir and D. Keselman, "Maximum agreement subtree in a set of evolutionary trees: metrics and
efficient algorithms", SIAM Journal on Computing 26(6) (1997), 1656-1669,
doi:10.1137/S0097539794269461 (the maximum homeomorphic agreement subtree problem is
NP-complete for three trees with unbounded degrees);
C. Semple and M. Steel, *Phylogenetics*, Oxford University Press (2003), Section 3.5 (rooted
phylogenetic trees correspond to their cluster systems, the hierarchies).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Bioinformatics.Phylogenetics.Splits

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumAgreementSubtreeThreeTrees

open Cslib.Bioinformatics.Phylogenetics.Splits (IsHierarchy)

/-!
# MAXIMUM AGREEMENT SUBTREE for three trees is NP-complete

INSTANCE: three rooted trees `T₁, T₂, T₃` (internal degrees unbounded) with the same leaf set
`X`, and an integer `K`. QUESTION: is there a set `Y ⊆ X` with `|Y| ≥ K` such that the
homeomorphic subtrees `T₁|Y, T₂|Y, T₃|Y` (the subtree spanned by `Y`, with vertices of one child
suppressed) are isomorphic as leaf-labeled trees?

Each tree is given by its cluster system: the leaf sets below its vertices. The cluster systems
of the rooted trees with leaf set `X` are exactly the hierarchies on `X` (`IsHierarchy`: `X`,
the singletons, and nonempty subsets any two nested or disjoint), and two such trees are
isomorphic as leaf-labeled trees, once vertices of one child are suppressed, iff their cluster
systems are equal (Semple and Steel 2003, Section 3.5). The clusters of `T|Y` are the nonempty
sets `C ∩ Y` for the clusters `C` of `T`, so `T₁|Y, T₂|Y, T₃|Y` are isomorphic iff these
restricted families coincide. The leaves are `X = Fin n`; a tree is given by a list of its
clusters, each a list of leaves, in any order and possibly with repetitions; `clusters` takes the
set of clusters the list denotes (a hierarchy on `n` leaves has at most `2n - 1` members, so a
tree's cluster list without repetitions has polynomial size).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MAXIMUM AGREEMENT SUBTREE for three trees is NP-complete.** Source: Amir and Keselman
(1997). -/
public theorem_wanted maximumAgreementSubtreeThreeTrees_npComplete :
    maximumAgreementSubtreeThreeTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumAgreementSubtreeThreeTreesDec

end MetaMathlibExt.Complexity.NPComplete.MaximumAgreementSubtreeThreeTrees
