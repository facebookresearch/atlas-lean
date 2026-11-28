/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WORD HOMOMORPHISM: definitions

Source:
A. Ehrenfeucht and G. Rozenberg, "Finding a homomorphism between two words is NP-complete",
Information Processing Letters 9 (1979), 86-88, doi:10.1016/0020-0190(79)90135-2;
M. L. Schmid, *On the membership problem for pattern languages and related topics*, PhD thesis,
Loughborough University (2012) (records that NP-completeness for nonerasing substitutions,
NE-pattern languages, "has been shown by Angluin and independently by Ehrenfeucht and
Rozenberg").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WordHomomorphism

/-- An instance: `|Δ|`, the word `u`, `|Σ|`, and the word `w`. -/
abbrev WordHomomorphismInstance := ℕ × List ℕ × ℕ × List ℕ

/-- Well-formedness of an instance: `u` is a word over `Δ` and `w` is a word over `Σ`. -/
def WellFormed (i : WordHomomorphismInstance) : Prop :=
  (∀ a ∈ i.2.1, a < i.1) ∧ ∀ b ∈ i.2.2.2, b < i.2.2.1

/-- A nonerasing homomorphism `h`, sending each letter of `Δ` to a nonempty word over `Σ`, with
`h(u) = w`. -/
def WordHomomorphismFeasible (i : WordHomomorphismInstance) : Prop :=
  ∃ h : ℕ → List ℕ, MetaMathlibExt.IsNonErasing h ∧ (∀ a < i.1, ∀ b ∈ h a, b < i.2.2.1) ∧
    MetaMathlibExt.morphExtend h i.2.1 = i.2.2.2

open Classical in
/-- WORD HOMOMORPHISM as a decision problem over bitstrings. -/
noncomputable def wordHomomorphismDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WordHomomorphismInstance) x with
  | some i => decide (WellFormed i ∧ WordHomomorphismFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WordHomomorphism
