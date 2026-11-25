/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXTERNAL MACRO DATA COMPRESSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR22] EXTERNAL MACRO DATA
COMPRESSION, p. 231 (references [Storer, 1977], [Storer and Szymanski, 1978]; transformation
from VERTEX COVER);
J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the
ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompression

/-!
# EXTERNAL MACRO DATA COMPRESSION is NP-complete

INSTANCE: an alphabet `Σ`, a string `s ∈ Σ*`, a pointer cost `h ∈ Z⁺`, and a bound `B ∈ Z⁺`.
QUESTION: are there strings `D` (dictionary string) and `C` (compressed string) in
`(Σ ∪ {pᵢ : 1 ≤ i ≤ |s|})*`, where the symbols `pᵢ` are "pointers", such that
`|D| + |C| + (h - 1) · (number of occurrences of pointers in D and C) ≤ B` and such that there
is a way of identifying pointers with substrings of `D` so that `s` can be obtained from `C` by
repeatedly replacing pointers in `C` by their corresponding substrings in `D`?

The alphabet is `Σ = {0, …, k - 1}`. A symbol of `Σ ∪ {pᵢ}` is `Sum.inl a` (the letter `a`) or
`Sum.inr j` (the pointer `p_{j+1}`, indexed from `0`); `IsOver k m u` says that `u` uses only
letters below `k` and pointers `p₁, …, p_m`. The identification of pointers with substrings of
`D` is a map `σ` with `σ j` a contiguous substring (`List.IsInfix`) of `D` for every pointer.
`ReplaceStep σ u v` replaces one occurrence of a pointer `p` in `u` by `σ p`, and `s` is obtained
from `C` when the reflexive-transitive closure of these steps leads from `C` to `s`. Substrings
of `D` may themselves contain pointers, which later steps replace in turn ("repeatedly").
`Compresses k s c B` states the question for a pointer cost `c`, so that variants with another
pointer cost (the [SR22] comment) can reuse it. `C = s` with `D` empty shows that every
`B ≥ |s|` is a yes-instance, so the binary encoding of `B` does not affect membership in `NP`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **EXTERNAL MACRO DATA COMPRESSION is NP-complete.** Source: Garey and Johnson (1979),
[SR22]; Storer and Szymanski (1982). -/
public theorem_wanted externalMacroDataCompression_npComplete :
    externalMacroDataCompressionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L externalMacroDataCompressionDec

end MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompression
