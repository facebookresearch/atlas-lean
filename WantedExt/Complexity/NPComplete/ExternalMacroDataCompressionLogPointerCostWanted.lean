/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXTERNAL MACRO DATA COMPRESSION with a fixed alphabet and logarithmic pointer cost is
NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR22] EXTERNAL MACRO DATA
COMPRESSION, comment (p. 231): "Remains NP-complete even if `h` is any fixed integer 2 or
greater. Many variants, including those in which `D` can contain no pointers and/or no
pointers can refer to overlapping strings, are also NP-complete. If the alphabet size is fixed
at 3 or greater, and the pointer cost is `⌈h·log|s|⌉`, the problem is also NP-complete"
(references [Storer, 1977], [Storer and Szymanski, 1978]);
J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the
ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import WantedExt.Complexity.NPComplete.ExternalMacroDataCompressionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompressionLogPointerCost

open ExternalMacroDataCompression (Compresses)

/-!
# EXTERNAL MACRO DATA COMPRESSION with a fixed alphabet and logarithmic pointer cost is
NP-complete

For a fixed alphabet `Σ = {0, …, k - 1}` with `k ≥ 3`:
INSTANCE: a string `s ∈ Σ*`, a positive integer `h`, and a bound `B ∈ Z⁺`.
QUESTION: are there strings `D` (dictionary string) and `C` (compressed string) in
`(Σ ∪ {pᵢ : 1 ≤ i ≤ |s|})*` such that
`|D| + |C| + (⌈h · log |s|⌉ - 1) · (number of occurrences of pointers in D and C) ≤ B` and such
that there is a way of identifying pointers with substrings of `D` so that `s` can be obtained
from `C` by repeatedly replacing pointers in `C` by their corresponding substrings in `D`?

This is [SR22] EXTERNAL MACRO DATA COMPRESSION
(`WantedExt.Complexity.NPComplete.ExternalMacroDataCompressionWanted`) with the variant of the
[SR22] comment: the alphabet size is a constant `k ≥ 3` of the problem rather than part of the
instance, and a pointer costs `⌈h · log |s|⌉` instead of `h`. The question is the parent's
`Compresses k s c B` with `c = pointerCost s h`; one `theorem_wanted` states NP-completeness for
every fixed `k ≥ 3`. Two conventions are fixed and disclosed: `h` keeps its role as the positive
integer of the parent instance, and `log` is the binary logarithm (`Real.logb 2`), the usual
reading of a pointer of `log |s|` symbols that addresses a position of `s`. For `|s| ≤ 1` the
pointer cost is `0`, and the cost term `(c - 1) · …` is `0` in `ℕ`, so a pointer then costs one
symbol, its own occurrence. `C = s` shows that every `B ≥ |s|` is a yes-instance, so the binary
encoding of `B` does not affect membership in `NP`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance (for a fixed alphabet `{0, …, k - 1}`): the string `s`, the parameter `h`, and
the bound `B`. -/
abbrev ExternalMacroDataCompressionLogPointerCostInstance := List ℕ × ℕ × ℕ

/-- The pointer cost `⌈h · log₂ |s|⌉`. -/
noncomputable def pointerCost (s : List ℕ) (h : ℕ) : ℕ :=
  ⌈(h : ℝ) * Real.logb 2 s.length⌉₊

/-- Well-formedness of an instance for the alphabet `{0, …, k - 1}`: `s` is a string over it,
and `h` and `B` are positive. -/
def WellFormed (k : ℕ) (i : ExternalMacroDataCompressionLogPointerCostInstance) : Prop :=
  (∀ a ∈ i.1, a < k) ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- For a natural alphabet size `k`, `s` has an external macro compression over the literals
`0, …, k - 1` within the bound `B` with pointer parameter `c = ⌈h · log₂ |s|⌉`; each pointer
occurrence is charged `max 1 c` (one symbol plus `c - 1` in ℕ). -/
def ExternalMacroDataCompressionLogPointerCostFeasible (k : ℕ)
    (i : ExternalMacroDataCompressionLogPointerCostInstance) : Prop :=
  Compresses k i.1 (pointerCost i.1 i.2.1) i.2.2

open Classical in
/-- EXTERNAL MACRO DATA COMPRESSION over the alphabet `{0, …, k - 1}` with pointer cost
`⌈h · log₂ |s|⌉`, as a decision problem over bitstrings. -/
noncomputable def externalMacroDataCompressionLogPointerCostDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExternalMacroDataCompressionLogPointerCostInstance) x with
  | some i => decide (WellFormed k i ∧ ExternalMacroDataCompressionLogPointerCostFeasible k i)
  | none => false

/-- **EXTERNAL MACRO DATA COMPRESSION with a fixed alphabet of size `k ≥ 3` and pointer cost
`⌈h · log |s|⌉` is NP-complete.** Source: Garey and Johnson (1979), [SR22], comment; Storer and
Szymanski (1982). -/
public theorem_wanted externalMacroDataCompressionLogPointerCost_npComplete (k : ℕ)
    (_hk : 3 ≤ k) :
    externalMacroDataCompressionLogPointerCostDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (externalMacroDataCompressionLogPointerCostDec k)

end MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompressionLogPointerCost
