/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXTERNAL MACRO DATA COMPRESSION with fixed pointer cost h ≥ 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR22] EXTERNAL MACRO DATA
COMPRESSION, p. 231 (comment: "Remains NP-complete even if `h` is any fixed integer 2 or
greater"; references [Storer, 1977], [Storer and Szymanski, 1978]);
J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the
ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ExternalMacroDataCompressionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompressionFixedPointerCost

/-- An instance: the alphabet size `k` (`Σ = {0, …, k - 1}`), the string `s`, and the bound
`B`; the pointer cost `h` is fixed. -/
abbrev ExternalMacroDataCompressionFixedPointerCostInstance := ℕ × List ℕ × ℕ

/-- The [SR22] instance `(k, s, h, B)` of an instance `(k, s, B)` and the fixed pointer cost
`h`. -/
abbrev withCost (h : ℕ) (i : ExternalMacroDataCompressionFixedPointerCostInstance) :
    ExternalMacroDataCompression.ExternalMacroDataCompressionInstance :=
  (i.1, i.2.1, h, i.2.2)

open Classical in
/-- EXTERNAL MACRO DATA COMPRESSION for a fixed pointer cost `h` as a decision problem over
bitstrings. -/
noncomputable def externalMacroDataCompressionFixedPointerCostDec (h : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExternalMacroDataCompressionFixedPointerCostInstance) x with
  | some i => decide (ExternalMacroDataCompression.WellFormed (withCost h i) ∧
      ExternalMacroDataCompression.ExternalMacroDataCompressionFeasible (withCost h i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompressionFixedPointerCost
