/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERNAL MACRO DATA COMPRESSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR23] INTERNAL MACRO DATA
COMPRESSION, p. 232 (references [Storer, 1977], [Storer and Szymanski, 1978]; transformation
from VERTEX COVER);
J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the
ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ExternalMacroDataCompressionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InternalMacroDataCompression

open ExternalMacroDataCompression (ExternalMacroDataCompressionInstance MacroSymbol IsOver
  pointerCount ReplaceStep WellFormed)

/-!
# INTERNAL MACRO DATA COMPRESSION is NP-complete

INSTANCE: an alphabet `Σ`, a string `s ∈ Σ*`, a pointer cost `h ∈ Z⁺`, and a bound `B ∈ Z⁺`.
QUESTION: is there a single string `C ∈ (Σ ∪ {pᵢ : 1 ≤ i ≤ |s|})*` such that
`|C| + (h - 1) · (number of occurrences of pointers in C) ≤ B` and such that there is a way of
identifying pointers with substrings of `C` so that `s` can be obtained from `C` by using `C`
as both the compressed string and the dictionary string in the manner indicated in [SR22]
EXTERNAL MACRO DATA COMPRESSION?

This reuses `WantedExt.Complexity.NPComplete.ExternalMacroDataCompressionWanted` (GJ [SR22]):
the instance type, `WellFormed` (`s` over `{0, …, k - 1}`, `h` and `B` positive), the symbols
(`Sum.inl a` a letter, `Sum.inr j` the pointer `p_{j+1}`), `IsOver`, `pointerCount`, and the
replacement step `ReplaceStep`. The manner of [SR22] is: pointers are identified with
substrings of the dictionary string (here `C` itself), and `s` is obtained from the compressed
string by repeatedly replacing pointers by their substrings (`Relation.ReflTransGen` of
`ReplaceStep`). A substring of `C` may contain pointers, which later steps replace in turn.
`C = s` shows that every `B ≥ |s|` is a yes-instance, so the binary encoding of `B` does not
affect membership in `NP`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some string `C` over `Σ ∪ {p₁, …, p_|s|}` with `|C| + (h - 1) · (pointer occurrences in C)
≤ B`, and substrings `σ p` of `C` for the pointers, such that repeated replacement leads from `C`
to `s`. -/
def InternalMacroDataCompressionFeasible (i : ExternalMacroDataCompressionInstance) : Prop :=
  ∃ C : List MacroSymbol, IsOver i.1 i.2.1.length C ∧
    C.length + (i.2.2.1 - 1) * pointerCount C ≤ i.2.2.2 ∧
    ∃ σ : ℕ → List MacroSymbol, (∀ p < i.2.1.length, σ p <:+: C) ∧
      Relation.ReflTransGen (ReplaceStep σ) C (i.2.1.map Sum.inl)

open Classical in
/-- INTERNAL MACRO DATA COMPRESSION as a decision problem over bitstrings. -/
noncomputable def internalMacroDataCompressionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExternalMacroDataCompressionInstance) x with
  | some i => decide (WellFormed i ∧ InternalMacroDataCompressionFeasible i)
  | none => false

/-- **INTERNAL MACRO DATA COMPRESSION is NP-complete.** Source: Garey and Johnson (1979),
[SR23]; Storer and Szymanski (1982). -/
public theorem_wanted internalMacroDataCompression_npComplete :
    internalMacroDataCompressionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L internalMacroDataCompressionDec

end MetaMathlibExt.Complexity.NPComplete.InternalMacroDataCompression
