/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXTERNAL MACRO DATA COMPRESSION with fixed pointer cost h ≥ 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR22] EXTERNAL MACRO DATA
COMPRESSION, p. 231 (comment: "Remains NP-complete even if `h` is any fixed integer 2 or
greater"; references [Storer, 1977], [Storer and Szymanski, 1978]);
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

namespace MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompressionFixedPointerCost

/-!
# EXTERNAL MACRO DATA COMPRESSION with fixed pointer cost h ≥ 2 is NP-complete

For a fixed integer `h ≥ 2`:

INSTANCE: an alphabet `Σ`, a string `s ∈ Σ*`, and a bound `B ∈ Z⁺`.
QUESTION: are there strings `D` (dictionary string) and `C` (compressed string) in
`(Σ ∪ {pᵢ : 1 ≤ i ≤ |s|})*`, where the symbols `pᵢ` are "pointers", such that
`|D| + |C| + (h - 1) · (number of occurrences of pointers in D and C) ≤ B` and such that there
is a way of identifying pointers with substrings of `D` so that `s` can be obtained from `C` by
repeatedly replacing pointers in `C` by their corresponding substrings in `D`?

This is [SR22] EXTERNAL MACRO DATA COMPRESSION
(`WantedExt.Complexity.NPComplete.ExternalMacroDataCompressionWanted`) with the pointer cost `h`
fixed instead of part of the instance. An instance is `(k, s, B)` (alphabet
`Σ = {0, …, k - 1}`); it is decided as the [SR22] instance `(k, s, h, B)` (`withCost h`), whose
`ExternalMacroDataCompression.WellFormed` (`s` over `Σ`, `h` and `B` positive) and
`ExternalMacroDataCompression.ExternalMacroDataCompressionFeasible` are reused unchanged.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **EXTERNAL MACRO DATA COMPRESSION is NP-complete for every fixed pointer cost `h ≥ 2`.**
Source: Garey and Johnson (1979), [SR22], comment; Storer and Szymanski (1982). -/
public theorem_wanted externalMacroDataCompressionFixedPointerCost_npComplete (h : ℕ)
    (hh : 2 ≤ h) :
    externalMacroDataCompressionFixedPointerCostDec h ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (externalMacroDataCompressionFixedPointerCostDec h)

end MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompressionFixedPointerCost
