/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXTERNAL MACRO DATA COMPRESSION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR22] EXTERNAL MACRO DATA
COMPRESSION, p. 231 (references [Storer, 1977], [Storer and Szymanski, 1978]; transformation
from VERTEX COVER);
J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the
ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompression

/-- An instance: the alphabet size `k` (`Σ = {0, …, k - 1}`), the string `s`, the pointer cost
`h`, and the bound `B`. -/
abbrev ExternalMacroDataCompressionInstance := ℕ × List ℕ × ℕ × ℕ

/-- A symbol of `Σ ∪ {pᵢ}`: a letter `Sum.inl a` or a pointer `Sum.inr j`. -/
abbrev MacroSymbol := ℕ ⊕ ℕ

/-- `u` is a string over `{0, …, k - 1} ∪ {p₁, …, p_m}`: its letters are below `k` and its
pointer indices below `m`. -/
def IsOver (k m : ℕ) (u : List MacroSymbol) : Prop :=
  ∀ c ∈ u, Sum.elim (· < k) (· < m) c

/-- The number of occurrences of pointers in `u`. -/
def pointerCount (u : List MacroSymbol) : ℕ := u.countP Sum.isRight

/-- One replacement step: an occurrence of a pointer `p` in `u` is replaced by the string
`σ p`. -/
def ReplaceStep (σ : ℕ → List MacroSymbol) (u v : List MacroSymbol) : Prop :=
  ∃ x y : List MacroSymbol, ∃ p : ℕ, u = x ++ Sum.inr p :: y ∧ v = x ++ σ p ++ y

/-- External macro compression of `s ∈ {0, …, k - 1}*` with pointer cost `c` within the bound
`B`: strings `D` and `C` over `Σ ∪ {p₁, …, p_|s|}` with
`|D| + |C| + (c - 1) · (pointer occurrences in D and C) ≤ B`, and substrings `σ p` of `D` for the
pointers, such that repeated replacement leads from `C` to `s`. -/
def Compresses (k : ℕ) (s : List ℕ) (c B : ℕ) : Prop :=
  ∃ D C : List MacroSymbol, IsOver k s.length D ∧ IsOver k s.length C ∧
    D.length + C.length + (c - 1) * (pointerCount D + pointerCount C) ≤ B ∧
    ∃ σ : ℕ → List MacroSymbol, (∀ p < s.length, σ p <:+: D) ∧
      Relation.ReflTransGen (ReplaceStep σ) C (s.map Sum.inl)

/-- Well-formedness of an instance: `s` is a string over `{0, …, k - 1}`, and `h` and `B` are
positive. -/
def WellFormed (i : ExternalMacroDataCompressionInstance) : Prop :=
  (∀ a ∈ i.2.1, a < i.1) ∧ 0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- `s` has an external macro compression with pointer cost `h` within the bound `B`. -/
def ExternalMacroDataCompressionFeasible (i : ExternalMacroDataCompressionInstance) : Prop :=
  Compresses i.1 i.2.1 i.2.2.1 i.2.2.2

open Classical in
/-- EXTERNAL MACRO DATA COMPRESSION as a decision problem over bitstrings. -/
noncomputable def externalMacroDataCompressionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExternalMacroDataCompressionInstance) x with
  | some i => decide (WellFormed i ∧ ExternalMacroDataCompressionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompression
