/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERNAL MACRO DATA COMPRESSION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR23] INTERNAL MACRO DATA
COMPRESSION, p. 232 (references [Storer, 1977], [Storer and Szymanski, 1978]; transformation
from VERTEX COVER);
J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the
ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ExternalMacroDataCompressionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InternalMacroDataCompression

open ExternalMacroDataCompression (ExternalMacroDataCompressionInstance MacroSymbol IsOver
  pointerCount ReplaceStep WellFormed)

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

end MetaMathlibExt.Complexity.NPComplete.InternalMacroDataCompression
