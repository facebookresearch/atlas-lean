/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAPLOTYPE INFERENCE BY PURE PARSIMONY is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HaplotypeInferencePureParsimony

/-!
# HAPLOTYPE INFERENCE BY PURE PARSIMONY is NP-complete

INSTANCE: a set `G` of genotypes, each a vector of length `m` with entries in `{0, 1, 2}`, and an
integer `K`. QUESTION: is there a set `H` of at most `K` haplotypes (vectors of length `m` with
entries in `{0, 1}`) such that every genotype `g ∈ G` is explained by two haplotypes
`h₁, h₂ ∈ H`, i.e., for each position `k`, `g[k] ∈ {0, 1}` implies `h₁[k] = h₂[k] = g[k]`, and
`g[k] = 2` implies `h₁[k] ≠ h₂[k]`?

The two haplotypes explaining a genotype need not be distinct: a genotype without entries `2`
is explained by one haplotype taken twice. Haplotypes are functions `Fin m → Bool` (`false`
for `0`, `true` for `1`) and `H` is a `Finset` of them, so `|H|` counts distinct haplotypes.
Genotypes are lists of natural numbers, so the alphabet `{0, 1, 2}` and the common length `m`
go in `WellFormed`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **HAPLOTYPE INFERENCE BY PURE PARSIMONY is NP-complete.** Source: Lancia, Pinotti, and Rizzi
(2004); Sharan, Halldórsson, and Istrail (2006). -/
public theorem_wanted haplotypeInferencePureParsimony_npComplete :
    haplotypeInferencePureParsimonyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L haplotypeInferencePureParsimonyDec

end MetaMathlibExt.Complexity.NPComplete.HaplotypeInferencePureParsimony
