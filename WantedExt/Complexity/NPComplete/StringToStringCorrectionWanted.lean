/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRING-TO-STRING CORRECTION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR20]
STRING-TO-STRING CORRECTION;
R. A. Wagner, "On the complexity of the extended string-to-string correction
problem", Proceedings of the 7th Annual ACM Symposium on Theory of Computing
(1975), 218-223, doi:10.1145/800116.803771.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.List.Chain

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StringToStringCorrection

/-!
# STRING-TO-STRING CORRECTION is NP-complete

INSTANCE: a finite alphabet `Σ`, strings `x` and `y` over `Σ`, and a positive integer `K`.
QUESTION: can `y` be derived from `x` by a sequence of `K` or fewer operations, each of which is
either a single symbol deletion or an interchange of two adjacent symbols?

The alphabet is `Σ = {0, ..., s - 1}` and strings are lists of symbols. One operation is
`Step a b`: `b` is `a` with one symbol deleted, or `a` with two adjacent symbols interchanged.
A derivation with at most `K` operations is a list of strings `x = w₀, w₁, ..., wₘ = y` with
`m ≤ K` (so at most `K + 1` strings) in which each consecutive pair is one `Step`
(`List.IsChain`). The case `m = 0` (no operation, `x = y`) is included.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the alphabet size `s` (symbols `0, ..., s - 1`), the strings `x` and `y`, and
the bound `K`. -/
abbrev StringToStringCorrectionInstance := ℕ × List ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: `x` and `y` are strings over the alphabet, and `K` is
positive. -/
def WellFormed (i : StringToStringCorrectionInstance) : Prop :=
  (∀ a ∈ i.2.1, a < i.1) ∧ (∀ a ∈ i.2.2.1, a < i.1) ∧ 0 < i.2.2.2

/-- One operation: `b` is `a` with a single symbol deleted, or `a` with two adjacent symbols
interchanged. -/
def Step (a b : List ℕ) : Prop :=
  (∃ (l₁ l₂ : List ℕ) (c : ℕ), a = l₁ ++ c :: l₂ ∧ b = l₁ ++ l₂) ∨
    ∃ (l₁ l₂ : List ℕ) (c d : ℕ), a = l₁ ++ c :: d :: l₂ ∧ b = l₁ ++ d :: c :: l₂

/-- `y` is derived from `x` by at most `K` operations: there is a list of strings from `x` to
`y` with at most `K + 1` entries, each obtained from the previous one by one `Step`. -/
def StringToStringCorrectionFeasible (i : StringToStringCorrectionInstance) : Prop :=
  ∃ ws : List (List ℕ), ws.head? = some i.2.1 ∧ ws.getLast? = some i.2.2.1 ∧
    ws.length ≤ i.2.2.2 + 1 ∧ ws.IsChain Step

open Classical in
/-- STRING-TO-STRING CORRECTION as a decision problem over bitstrings. -/
noncomputable def stringToStringCorrectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StringToStringCorrectionInstance) x with
  | some i => decide (WellFormed i ∧ StringToStringCorrectionFeasible i)
  | none => false

/-- **STRING-TO-STRING CORRECTION is NP-complete.** Source: Garey and Johnson (1979), [SR20];
Wagner (1975). -/
public theorem_wanted stringToStringCorrection_npComplete :
    stringToStringCorrectionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L stringToStringCorrectionDec

end MetaMathlibExt.Complexity.NPComplete.StringToStringCorrection
