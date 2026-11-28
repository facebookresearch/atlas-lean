/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INCOMPLETE PERFECT PHYLOGENY HAPLOTYPING: definitions

Source:
G. Kimmel and R. Shamir, "The incomplete perfect phylogeny haplotype problem", Journal of
Bioinformatics and Computational Biology 3 (2005), 359-384, doi:10.1142/S0219720005001090,
Problem 2 (IPPH), Section 1 (the unrooted problem is NP-hard by Steel's result for partial
binary characters) and Section 3, Theorems 1 and 2 (the rooted problem is NP-complete);
M. A. Steel, "The complexity of reconstructing trees from qualitative characters and subtrees",
Journal of Classification 9 (1992), 91-116, doi:10.1007/BF02618470.
-/
module

public import CSLibExt.Bioinformatics.Phylogenetics.Splits
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HaplotypeInferencePureParsimonyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IncompletePerfectPhylogenyHaplotyping

open HaplotypeInferencePureParsimony (Explains)
open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount (UnrootedBinaryTree)
open Cslib.Bioinformatics.Phylogenetics.Splits (IsPerfectPhylogeny)

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

end MetaMathlibExt.Complexity.NPComplete.IncompletePerfectPhylogenyHaplotyping
