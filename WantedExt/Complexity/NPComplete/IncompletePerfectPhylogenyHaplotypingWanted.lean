/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INCOMPLETE PERFECT PHYLOGENY HAPLOTYPING is NP-complete

Source:
G. Kimmel and R. Shamir, "The incomplete perfect phylogeny haplotype problem", Journal of
Bioinformatics and Computational Biology 3 (2005), 359-384, doi:10.1142/S0219720005001090,
Problem 2 (IPPH), Section 1 (the unrooted problem is NP-hard by Steel's result for partial
binary characters) and Section 3, Theorems 1 and 2 (the rooted problem is NP-complete);
M. A. Steel, "The complexity of reconstructing trees from qualitative characters and subtrees",
Journal of Classification 9 (1992), 91-116, doi:10.1007/BF02618470.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Bioinformatics.Phylogenetics.Splits
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HaplotypeInferencePureParsimonyWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IncompletePerfectPhylogenyHaplotyping

open HaplotypeInferencePureParsimony (Explains)
open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount (UnrootedBinaryTree)
open Cslib.Bioinformatics.Phylogenetics.Splits (IsPerfectPhylogeny)

/-!
# INCOMPLETE PERFECT PHYLOGENY HAPLOTYPING is NP-complete

INSTANCE: an incomplete genotype matrix `M`: `n ≥ 1` genotypes over `m` sites, with entries
`M[i, j] ∈ {0, 1, 2, ?}`. QUESTION (Kimmel and Shamir, Problem 2): can one complete `M`, i.e.
replace each `?` by `0`, `1` or `2`, so that there exists an expansion `M'` of the completed
matrix which admits a perfect phylogeny?

An expansion of a genotype matrix (Kimmel and Shamir, Section 2) is a binary matrix with two
rows (haplotypes) `M'[i, ∗]` and `M'[i', ∗]` for each genotype `i`: where `M[i, j] ∈ {0, 1}`
both haplotypes carry `M[i, j]`, and where `M[i, j] = 2` they differ. This is
`HaplotypeInferencePureParsimony.Explains`, reused; the haplotypes are indexed by
`Fin n × Bool` (`(i, false)` and `(i, true)` are the two rows of genotype `i`). The entry `?` is
encoded as `3`.

A binary matrix admits a perfect phylogeny when some tree has the haplotypes at its leaves and
every site changes state on exactly one edge (Kimmel and Shamir, Definition 1; Gusfield 1991).
This is `Cslib.Bioinformatics.Phylogenetics.Splits.IsPerfectPhylogeny`, reused: an unrooted binary
phylogenetic tree on the haplotypes in which the split of every non-constant column is an edge
split (a constant column changes state on no edge). Its four-gamete characterization
(`exists_perfectPhylogeny_iff`: no two columns show all four gametes `00, 01, 10, 11`) is the
standard test for Definition 1. Identical haplotypes, for instance the two haplotypes of a
genotype without entries `2`, are distinct leaves separated only by edges on which no site
changes; Definition 1 read literally cannot place two identical rows (every edge carries a
site), and identifying identical rows gives the same yes-instances.

Hardness: Kimmel and Shamir prove the rooted version (a root haplotype is part of the input)
NP-complete (Theorems 1 and 2, from 3-SAT through a mixed-graph completion problem). They note
that the unrooted version, stated here, follows from Steel's NP-completeness of compatibility of
partial binary characters. The instances without entries `2` are such character matrices:
completing a `?` by `2` only splits one genotype into two haplotypes, and keeping one of them
preserves a perfect phylogeny, so such an instance is a yes-instance exactly when its `?`
entries can be replaced by `0`s and `1`s to give a matrix with a perfect phylogeny. Membership
in NP: the completion and the expansion are a certificate, checked with the four-gamete test.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of sites and the genotypes, each a list of `m` entries in
`{0, 1, 2, 3}` (`3` stands for the missing entry `?`). -/
abbrev IncompletePerfectPhylogenyHaplotypingInstance := ℕ × List (List ℕ)

/-- Well-formedness of an instance: there is at least one genotype, and every genotype has `m`
entries, each in `{0, 1, 2, ?}`. -/
def WellFormed (i : IncompletePerfectPhylogenyHaplotypingInstance) : Prop :=
  i.2 ≠ [] ∧ ∀ g ∈ i.2, g.length = i.1 ∧ ∀ x ∈ g, x ≤ 3

/-- `g'` completes the incomplete genotype `g`: it has the same length, its entries are in
`{0, 1, 2}`, and it agrees with `g` at every site where `g` is not `?` (`3`). -/
def Completes (g g' : List ℕ) : Prop :=
  g'.length = g.length ∧ (∀ x ∈ g', x ≤ 2) ∧
    ∀ k < g.length, g.getD k 0 ≠ 3 → g'.getD k 0 = g.getD k 0

/-- Some completion `c` of the genotypes has an expansion `H` (two haplotypes `H (j, false)`
and `H (j, true)` explaining each completed genotype `c j`) that admits a perfect phylogeny. -/
def IncompletePerfectPhylogenyHaplotypingFeasible
    (i : IncompletePerfectPhylogenyHaplotypingInstance) : Prop :=
  ∃ c : Fin i.2.length → List ℕ, ∃ H : Fin i.2.length × Bool → Fin i.1 → Bool,
    (∀ j, Completes (i.2.get j) (c j) ∧ Explains (c j) (H (j, false)) (H (j, true))) ∧
      ∃ T : UnrootedBinaryTree (Fin i.2.length × Bool), IsPerfectPhylogeny T H

open Classical in
/-- INCOMPLETE PERFECT PHYLOGENY HAPLOTYPING as a decision problem over bitstrings. -/
noncomputable def incompletePerfectPhylogenyHaplotypingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IncompletePerfectPhylogenyHaplotypingInstance) x with
  | some i => decide (WellFormed i ∧ IncompletePerfectPhylogenyHaplotypingFeasible i)
  | none => false

/-- **INCOMPLETE PERFECT PHYLOGENY HAPLOTYPING is NP-complete.** Source: Kimmel and Shamir
(2005), Problem 2, Section 1 and Theorems 1-2; Steel (1992). -/
public theorem_wanted incompletePerfectPhylogenyHaplotyping_npComplete :
    incompletePerfectPhylogenyHaplotypingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L incompletePerfectPhylogenyHaplotypingDec

end MetaMathlibExt.Complexity.NPComplete.IncompletePerfectPhylogenyHaplotyping
