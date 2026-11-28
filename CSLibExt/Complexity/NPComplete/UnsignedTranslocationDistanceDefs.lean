/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNSIGNED TRANSLOCATION DISTANCE: definitions

Source:
D. Zhu and L. Wang, "On the complexity of unsigned translocation distance", Theoretical
Computer Science 352 (2006), 322-328, doi:10.1016/j.tcs.2005.09.078 (Section 2: the model;
Theorem 3: computing the unsigned translocation distance is NP-hard).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnsignedTranslocationDistance

/-- An instance: the genomes `A` and `B`, each a list of chromosomes given as lists of genes,
and the bound `K`. -/
abbrev UnsignedTranslocationDistanceInstance := List (List ℕ) × List (List ℕ) × ℕ

/-- Unsigned chromosome `X` is identical to chromosome `Y`: `X = Y` or `X` is the reversal
`Yᴿ = y_q, …, y₁` of `Y`. -/
def ChromosomeIdentical (X Y : List ℕ) : Prop :=
  X = Y ∨ X = Y.reverse

/-- Genome `A` is identical to genome `B`: the sets of chromosomes of `A` and `B` are the same,
up to identical chromosomes. -/
def GenomeIdentical (A B : List (List ℕ)) : Prop :=
  (∀ X ∈ A, ∃ Y ∈ B, ChromosomeIdentical X Y) ∧ ∀ Y ∈ B, ∃ X ∈ A, ChromosomeIdentical X Y

/-- One translocation transforms genome `A` into `A'`: it acts on two chromosomes
`X = A[i] = X₁ X₂` and `Y = A[j] = Y₁ Y₂` (`i ≠ j`, all four segments nonempty) and replaces
them by `X₁ Y₂` and `Y₁ X₂` (prefix–prefix) or by `X₁ Y₁ᴿ` and `X₂ᴿ Y₂` (prefix–suffix). -/
def Translocation (A A' : List (List ℕ)) : Prop :=
  ∃ i j : Fin A.length, i ≠ j ∧ ∃ X₁ X₂ Y₁ Y₂ : List ℕ,
    X₁ ≠ [] ∧ X₂ ≠ [] ∧ Y₁ ≠ [] ∧ Y₂ ≠ [] ∧ A.get i = X₁ ++ X₂ ∧ A.get j = Y₁ ++ Y₂ ∧
      (A' = (A.set i (X₁ ++ Y₂)).set j (Y₁ ++ X₂) ∨
        A' = (A.set i (X₁ ++ Y₁.reverse)).set j (X₂.reverse ++ Y₂))

/-- Well-formedness of an instance: every gene is a positive integer, every chromosome is
nonempty, each gene occurs once in `A`, and `B` has the same genes as `A`. -/
def WellFormed (i : UnsignedTranslocationDistanceInstance) : Prop :=
  (∀ X ∈ i.1 ++ i.2.1, X ≠ [] ∧ ∀ g ∈ X, 0 < g) ∧ i.1.flatten.Nodup ∧
    i.1.flatten.Perm i.2.1.flatten

/-- Some sequence of `t ≤ K` translocations `A = G₀ → G₁ → ⋯ → Gₜ` ends in a genome `Gₜ`
identical to `B`. -/
def UnsignedTranslocationDistanceFeasible (i : UnsignedTranslocationDistanceInstance) : Prop :=
  ∃ t ≤ i.2.2, ∃ G : ℕ → List (List ℕ), G 0 = i.1 ∧
    (∀ s < t, Translocation (G s) (G (s + 1))) ∧ GenomeIdentical (G t) i.2.1

open Classical in
/-- UNSIGNED TRANSLOCATION DISTANCE as a decision problem over bitstrings. -/
noncomputable def unsignedTranslocationDistanceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnsignedTranslocationDistanceInstance) x with
  | some i => decide (WellFormed i ∧ UnsignedTranslocationDistanceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnsignedTranslocationDistance
