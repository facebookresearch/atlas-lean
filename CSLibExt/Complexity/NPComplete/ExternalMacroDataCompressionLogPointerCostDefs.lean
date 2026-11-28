/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXTERNAL MACRO DATA COMPRESSION with a fixed alphabet and logarithmic pointer cost: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CSLibExt.Complexity.NPComplete.ExternalMacroDataCompressionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompressionLogPointerCost

open ExternalMacroDataCompression (Compresses)

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

/-- `s` has an external macro compression with pointer cost `⌈h · log₂ |s|⌉` within the bound
`B`. -/
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

end MetaMathlibExt.Complexity.NPComplete.ExternalMacroDataCompressionLogPointerCost
