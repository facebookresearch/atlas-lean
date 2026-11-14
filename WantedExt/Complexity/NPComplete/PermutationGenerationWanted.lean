/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PERMUTATION GENERATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS6] PERMUTATION GENERATION;
M. R. Garey, D. S. Johnson, G. L. Miller, and C. H. Papadimitriou, "The complexity of coloring
circular arcs and chords", SIAM Journal on Algebraic and Discrete Methods 1 (1980), 216-227,
doi:10.1137/0601025 (the word problem for products of symmetric groups);
H. U. Simon, "The word problem for products of symmetric groups", arXiv:2506.13655 (2025),
Section 3 (definition and Theorem 3.1, attributed to Garey, Johnson, Miller, and Papadimitriou).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PermutationGeneration

/-!
# PERMUTATION GENERATION is NP-complete

INSTANCE: a permutation `σ` of `{1, ..., N}` and a sequence `S₁, ..., Sₘ` of subsets of
`{1, ..., N}`. QUESTION: can `σ` be written as `σ = σ₁ σ₂ ⋯ σₘ`, where each `σᵢ` is a
permutation of `{1, ..., N}` fixing every element of `{1, ..., N} - Sᵢ`?

This is the word problem for products of symmetric groups of Garey, Johnson, Miller, and
Papadimitriou. Elements are `0, ..., N - 1`. The permutation `σ` is given by its list of images
`[σ 0, ..., σ (N - 1)]`; the factors are `Equiv.Perm (Fin N)`. The product `σ₁ σ₂ ⋯ σₘ` applies
`σ₁` first, then `σ₂`, and so on, as in the cited sources: the image of `x` is
`(List.ofFn τ).foldl (fun y s => s y) x`. For `m = 0` the product is the identity.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the image list `[σ 0, ..., σ (N - 1)]` of `σ` (so `N` is its length), and the
subsets `S₁, ..., Sₘ`, each as a list of elements. -/
abbrev PermutationGenerationInstance := List ℕ × List (List ℕ)

/-- Well-formedness of an instance: the image list is a permutation of `[0, ..., N - 1]`, and
every listed subset element is below `N`. -/
def WellFormed (i : PermutationGenerationInstance) : Prop :=
  i.1.Perm (List.range i.1.length) ∧ ∀ s ∈ i.2, ∀ x ∈ s, x < i.1.length

/-- There are permutations `τ k` of `Fin N`, one for each subset, each fixing every element
outside its subset, such that applying `τ 0`, then `τ 1`, ..., then `τ (m - 1)` sends every `x`
to `σ x`. -/
def PermutationGenerationFeasible (i : PermutationGenerationInstance) : Prop :=
  ∃ τ : Fin i.2.length → Equiv.Perm (Fin i.1.length),
    (∀ k (x : Fin i.1.length), (x : ℕ) ∉ i.2.get k → τ k x = x) ∧
    ∀ x : Fin i.1.length,
      (((List.ofFn τ).foldl (fun (y : Fin i.1.length) s => s y) x : Fin i.1.length) : ℕ) =
        i.1.getD x 0

open Classical in
/-- PERMUTATION GENERATION as a decision problem over bitstrings. -/
noncomputable def permutationGenerationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PermutationGenerationInstance) x with
  | some i => decide (WellFormed i ∧ PermutationGenerationFeasible i)
  | none => false

/-- **PERMUTATION GENERATION is NP-complete.** Source: Garey and Johnson (1979), [MS6];
Garey, Johnson, Miller, and Papadimitriou (1980). -/
public theorem_wanted permutationGeneration_npComplete :
    permutationGenerationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L permutationGenerationDec

end MetaMathlibExt.Complexity.NPComplete.PermutationGeneration
