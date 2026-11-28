/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAPLOTYPE INFERENCE BY PURE PARSIMONY: definitions

Source:
G. Lancia, M. C. Pinotti, and R. Rizzi, "Haplotyping populations by pure parsimony: complexity
of exact and approximation algorithms", INFORMS Journal on Computing 16 (2004), 348-359,
doi:10.1287/ijoc.1040.0085;
R. Sharan, B. V. Halldórsson, and S. Istrail, "Islands of tractability for parsimony
haplotyping", IEEE/ACM Transactions on Computational Biology and Bioinformatics 3 (2006),
303-311, doi:10.1109/TCBB.2006.40 (NP-hardness, crediting the first proof to E. Hubbell,
unpublished).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HaplotypeInferencePureParsimony

/-- An instance: the number `m` of sites, the genotypes, and the bound `K`. -/
abbrev HaplotypeInferencePureParsimonyInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every genotype has length `m` and entries in
`{0, 1, 2}`. -/
def WellFormed (i : HaplotypeInferencePureParsimonyInstance) : Prop :=
  ∀ g ∈ i.2.1, g.length = i.1 ∧ ∀ x ∈ g, x ≤ 2

/-- The haplotypes `h₁` and `h₂` explain the genotype `g`: at a site where `g` is `0` or `1`
both haplotypes carry that value, and at a site where `g` is `2` they differ. -/
def Explains {m : ℕ} (g : List ℕ) (h₁ h₂ : Fin m → Bool) : Prop :=
  ∀ k : Fin m, (g.getD k 0 = 0 → h₁ k = false ∧ h₂ k = false) ∧
    (g.getD k 0 = 1 → h₁ k = true ∧ h₂ k = true) ∧ (g.getD k 0 = 2 → h₁ k ≠ h₂ k)

/-- Some set of at most `K` haplotypes explains every genotype by two of its members. -/
def HaplotypeInferencePureParsimonyFeasible (i : HaplotypeInferencePureParsimonyInstance) :
    Prop :=
  ∃ H : Finset (Fin i.1 → Bool), H.card ≤ i.2.2 ∧
    ∀ g ∈ i.2.1, ∃ h₁ ∈ H, ∃ h₂ ∈ H, Explains g h₁ h₂

open Classical in
/-- HAPLOTYPE INFERENCE BY PURE PARSIMONY as a decision problem over bitstrings. -/
noncomputable def haplotypeInferencePureParsimonyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HaplotypeInferencePureParsimonyInstance) x with
  | some i => decide (WellFormed i ∧ HaplotypeInferencePureParsimonyFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HaplotypeInferencePureParsimony
