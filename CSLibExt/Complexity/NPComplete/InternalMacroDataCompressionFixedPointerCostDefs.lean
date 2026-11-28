/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERNAL MACRO DATA COMPRESSION with fixed pointer cost h ≥ 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR23] INTERNAL MACRO DATA
COMPRESSION, p. 231, the page that also holds [SR22]. The [SR23] entry's own comment reads:
"Remains NP-complete even if `h` is any fixed integer 2 or greater. For other NP-complete
variants (as in the previous problem), see references." (references [Storer, 1977], [Storer and
Szymanski, 1978]);
J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the
ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.InternalMacroDataCompressionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InternalMacroDataCompressionFixedPointerCost

/-- An instance: the alphabet size `k` (`Σ = {0, …, k - 1}`), the string `s`, and the bound
`B`; the pointer cost `h` is fixed. -/
abbrev InternalMacroDataCompressionFixedPointerCostInstance := ℕ × List ℕ × ℕ

/-- The [SR23] instance `(k, s, h, B)` of an instance `(k, s, B)` and the fixed pointer cost
`h`. -/
abbrev withCost (h : ℕ) (i : InternalMacroDataCompressionFixedPointerCostInstance) :
    ExternalMacroDataCompression.ExternalMacroDataCompressionInstance :=
  (i.1, i.2.1, h, i.2.2)

open Classical in
/-- INTERNAL MACRO DATA COMPRESSION for a fixed pointer cost `h` as a decision problem over
bitstrings. -/
noncomputable def internalMacroDataCompressionFixedPointerCostDec (h : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InternalMacroDataCompressionFixedPointerCostInstance) x with
  | some i => decide (ExternalMacroDataCompression.WellFormed (withCost h i) ∧
      InternalMacroDataCompression.InternalMacroDataCompressionFeasible (withCost h i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.InternalMacroDataCompressionFixedPointerCost
