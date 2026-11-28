/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.List.Perm.Basic

/-!
# UNSIGNED TRANSLOCATION DISTANCE: definitions

INSTANCE: two unsigned genomes `A` and `B` over the same genes, and a nonnegative integer `K`.
QUESTION: is the translocation distance `d(A, B)` at most `K`, i.e. can `A` be transformed into
`B` by at most `K` translocations?

The model is that of Zhu and Wang (2006), Section 2. A genome is a set of chromosomes, a
chromosome `X = x₁, …, xₚ` is a sequence of genes, and for unsigned genomes each gene is a
positive integer. A translocation acts on two chromosomes `X = x₁, …, x_{b-1}, x_b, …, xₚ` and
`Y = y₁, …, y_{c-1}, y_c, …, y_q` of the genome: the prefix–prefix translocation `(X, Y, b, c)`
replaces them by `x₁, …, x_{b-1}, y_c, …, y_q` and `y₁, …, y_{c-1}, x_b, …, xₚ`, and the
prefix–suffix translocation `(X, Y, b, c)` by `x₁, …, x_{b-1}, y_{c-1}, …, y₁` and
`xₚ, …, x_b, y_c, …, y_q`. A chromosome `X` is identical to `Y` if `X = Y` or `X` is the
reversal of `Y`, and genome `A` is identical to genome `B` if they have the same set of
chromosomes. The translocation distance `d(A, B)` is the minimum number of translocations
required to transform `A` into `B`. Zhu and Wang prove that computing it is NP-hard
(Theorem 3, by a reduction whose question is "at most `3n - 3 - J` translocations"); this is
the decision form, at most `K` translocations.

A genome is a list of chromosomes and a chromosome a list of genes. The source writes both
segments `x₁, …, x_{b-1}` and `x_b, …, xₚ` of a chromosome cut by a translocation, so both are
nonempty (`2 ≤ b ≤ p`), and likewise for `Y`; `Translocation` states this with the four
nonempty segments `X₁ X₂ Y₁ Y₂`. As in the source's model and its reduction, each gene occurs
once in each genome, the two genomes have the same genes, and chromosomes are nonempty
(`WellFormed`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
D. Zhu and L. Wang, "On the complexity of unsigned translocation distance", Theoretical
Computer Science 352 (2006), 322-328, doi:10.1016/j.tcs.2005.09.078 (Section 2: the model;
Theorem 3: computing the unsigned translocation distance is NP-hard).
-/

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
