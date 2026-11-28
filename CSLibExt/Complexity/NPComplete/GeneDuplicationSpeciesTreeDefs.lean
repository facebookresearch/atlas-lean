/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENE DUPLICATION (species tree inference): definitions

Source:
B. Ma, M. Li, and L. Zhang, "From gene trees to species trees", SIAM Journal on Computing 30(3)
(2000), 729-752, doi:10.1137/S0097539798343362;
M. S. Bansal, O. Eulenstein, and A. Wehe, "The gene-duplication problem: near-linear time
algorithms for NNI-based local searches", IEEE/ACM Transactions on Computational Biology and
Bioinformatics 6(2) (2009), 221-231, doi:10.1109/TCBB.2009.7, Section 2 (the model and
Problem 1) and Section 1 ("The decision version of the gene-duplication problem is NP-complete
[8]").
-/
module

public import MathlibExt.Combinatorics.Enumerative.UnrootedBinaryTreeCount
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneDuplicationSpeciesTree

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount (IsBinaryHierarchy)

/-- A gene tree: the species of its leaves `0, …, m - 1`, and the list of its clusters, each a
list of leaves. -/
abbrev GeneTree := List ℕ × List (List ℕ)

/-- An instance: the number `k` of species, the gene trees, and the bound `K`. -/
abbrev GeneDuplicationSpeciesTreeInstance := ℕ × List GeneTree × ℕ

/-- The cluster system of a gene tree, as sets of leaves. -/
def geneClusters (G : GeneTree) : Finset (Finset ℕ) :=
  (G.2.map List.toFinset).toFinset

/-- The set `λ(C)` of species labeling the leaves in the gene cluster `C`. -/
def species (G : GeneTree) (C : Finset ℕ) : Finset ℕ :=
  C.image fun x => G.1.getD x 0

/-- The gene cluster `C` is a duplication for the species tree `S` (a binary hierarchy on the
species): for some child `D` of `C` (a gene cluster properly inside `C` with no gene cluster
strictly between them), `M(C) = M(D)`, i.e. every species cluster containing `λ(D)` contains
`λ(C)`. -/
def IsDuplication (S : Finset (Finset ℕ)) (G : GeneTree) (C : Finset ℕ) : Prop :=
  ∃ D ∈ geneClusters G, D ⊂ C ∧ (∀ E ∈ geneClusters G, D ⊂ E → ¬ E ⊂ C) ∧
    ∀ E ∈ S, species G D ⊆ E → species G C ⊆ E

open Classical in
/-- The number of duplications of the gene tree `G` under its lca-mapping into `S`. -/
noncomputable def duplications (S : Finset (Finset ℕ)) (G : GeneTree) : ℕ :=
  ((geneClusters G).filter (IsDuplication S G)).card

/-- Well-formedness of an instance: there is at least one species; every gene leaf is labeled
by a species `< k`, every species labels some gene leaf, and the clusters of every gene tree are
lists of its leaves forming a binary hierarchy on them. -/
def WellFormed (i : GeneDuplicationSpeciesTreeInstance) : Prop :=
  0 < i.1 ∧ (∀ s < i.1, ∃ G ∈ i.2.1, s ∈ G.1) ∧
    ∀ G ∈ i.2.1, (∀ s ∈ G.1, s < i.1) ∧ (∀ c ∈ G.2, ∀ x ∈ c, x < G.1.length) ∧
      IsBinaryHierarchy (Finset.range G.1.length) (geneClusters G)

/-- Some rooted binary species tree, a binary hierarchy on the species `{0, …, k - 1}`, gives at
most `K` duplications in total over the gene trees. -/
def GeneDuplicationSpeciesTreeFeasible (i : GeneDuplicationSpeciesTreeInstance) : Prop :=
  ∃ S : Finset (Finset ℕ), IsBinaryHierarchy (Finset.range i.1) S ∧
    (i.2.1.map (duplications S)).sum ≤ i.2.2

open Classical in
/-- GENE DUPLICATION (species tree inference) as a decision problem over bitstrings. -/
noncomputable def geneDuplicationSpeciesTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeneDuplicationSpeciesTreeInstance) x with
  | some i => decide (WellFormed i ∧ GeneDuplicationSpeciesTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeneDuplicationSpeciesTree
