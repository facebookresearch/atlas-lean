/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WORD HOMOMORPHISM is NP-complete

Source:
A. Ehrenfeucht and G. Rozenberg, "Finding a homomorphism between two words is NP-complete",
Information Processing Letters 9 (1979), 86-88, doi:10.1016/0020-0190(79)90135-2;
M. L. Schmid, *On the membership problem for pattern languages and related topics*, PhD thesis,
Loughborough University (2012) (records that NP-completeness for nonerasing substitutions,
NE-pattern languages, "has been shown by Angluin and independently by Ehrenfeucht and
Rozenberg").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WordHomomorphism

/-!
# WORD HOMOMORPHISM is NP-complete

INSTANCE: a word `u` over an alphabet `Δ` and a word `w` over an alphabet `Σ`. QUESTION: is there
a nonerasing homomorphism `h : Δ* → Σ*` (every letter of `Δ` is sent to a nonempty word over
`Σ`) with `h(u) = w`?

Representation. The alphabets are `Δ = {0, ..., |Δ| - 1}` and `Σ = {0, ..., |Σ| - 1}`, given by
their sizes, and words are lists of letters. A homomorphism is given by its letter map
`h : ℕ → List ℕ`, extended to words by concatenation (`MetaMathlibExt.morphExtend`, i.e.
`List.flatMap`); nonerasing is `MetaMathlibExt.IsNonErasing` (every letter image is nonempty),
and the images of the letters of `Δ` are words over `Σ`. The letter map is also defined (and
nonempty) on naturals outside `Δ`; those values never affect `h(u)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **WORD HOMOMORPHISM is NP-complete.** Source: Ehrenfeucht and Rozenberg (1979). -/
public theorem_wanted wordHomomorphism_npComplete :
    wordHomomorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L wordHomomorphismDec

end MetaMathlibExt.Complexity.NPComplete.WordHomomorphism
