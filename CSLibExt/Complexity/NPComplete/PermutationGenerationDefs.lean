/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PERMUTATION GENERATION: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PermutationGeneration

/-- An instance: the image list `[σ 0, ..., σ (N - 1)]` of `σ` (so `N` is its length), and the
subsets `S₁, ..., Sₘ`, each as a list of elements. -/
abbrev PermutationGenerationInstance := List ℕ × List (List ℕ)

/-- Well-formedness of an instance: `N ≥ 1`, the image list is a permutation of
`[0, ..., N - 1]`, there is at least one subset (`m ≥ 1`), and every listed subset element is
below `N`. -/
def WellFormed (i : PermutationGenerationInstance) : Prop :=
  0 < i.1.length ∧ i.1.Perm (List.range i.1.length) ∧ 0 < i.2.length ∧
    ∀ s ∈ i.2, ∀ x ∈ s, x < i.1.length

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

end MetaMathlibExt.Complexity.NPComplete.PermutationGeneration
