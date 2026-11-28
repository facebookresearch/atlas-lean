/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENE DUPLICATION (species tree inference) is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeneDuplicationSpeciesTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneDuplicationSpeciesTree

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount (IsBinaryHierarchy)

/-!
# GENE DUPLICATION (species tree inference) is NP-complete

INSTANCE: a collection of rooted binary gene trees whose leaves are labeled by species, and an
integer `K`.
QUESTION: is there a rooted binary species tree `S` on the species such that the total number of
gene duplications, summed over the gene trees under their lca-mappings into `S`, is at most `K`?

Bansal, Eulenstein, and Wehe (Section 2; trees are rooted and fully binary): the leaf-mapping
sends each gene leaf to the species leaf with its label, and its extension `M` maps a gene
node `g` to `lca` of the species of the leaves below `g`; "A node v ∈ V(G) is a (gene)
duplication if M(v) ∈ M(Ch(v))", the reconciliation cost of a gene tree is its number of
duplications and that of a collection is the sum; the gene-duplication problem asks for a
species tree of minimum cost, and its decision version is NP-complete (Ma, Li, and Zhang).

Trees are given by their cluster systems, the leaf sets below their nodes: the cluster systems
of the rooted binary trees on a leaf set `X` are exactly the binary hierarchies on `X`
(MathlibExt's `IsBinaryHierarchy`). The species are `0, …, k - 1`, and the species tree is a
binary hierarchy on `{0, …, k - 1}`. A gene tree with `m` leaves is the list of the species of
its leaves `0, …, m - 1` and a list of its clusters (each a list of leaves), which must form a
binary hierarchy on `{0, …, m - 1}`. The children of a cluster `C` are the maximal clusters
properly inside it. Writing `λ(C)` for the set of species of the leaves in `C`, `M(C)` is the
smallest species cluster containing `λ(C)`, and since `M(D) ⊆ M(C)` for a child `D`, the
condition `M(C) = M(D)` says exactly that every species cluster containing `λ(D)` contains
`λ(C)` (`IsDuplication`). Every species is required to label some gene leaf; species that label
no gene do not change any duplication, and the requirement keeps the species tree polynomial in
the input.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENE DUPLICATION (species tree inference) is NP-complete.** Source: Ma, Li, and Zhang
(2000); Bansal, Eulenstein, and Wehe (2009), Sections 1-2. -/
public theorem_wanted geneDuplicationSpeciesTree_npComplete :
    geneDuplicationSpeciesTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L geneDuplicationSpeciesTreeDec

end MetaMathlibExt.Complexity.NPComplete.GeneDuplicationSpeciesTree
