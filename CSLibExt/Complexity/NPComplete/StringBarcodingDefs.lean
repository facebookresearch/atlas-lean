/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRING BARCODING: definitions

Source:
G. Lancia and R. Rizzi, "The approximability of the String Barcoding problem", Algorithms for
Molecular Biology 1 (2006), article 12, doi:10.1186/1748-7188-1-12 (problem introduced by
S. Rash and D. Gusfield, "String barcoding: uncovering optimal virus signatures", RECOMB 2002,
doi:10.1145/565196.565229).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StringBarcoding

/-- An instance: the alphabet size `|Σ|`, the strings `v₁, ..., vₙ`, and the bound `K`. -/
abbrev StringBarcodingInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: the strings are over `Σ` and pairwise distinct (`V` is a
set). -/
def WellFormed (i : StringBarcodingInstance) : Prop :=
  (∀ v ∈ i.2.1, ∀ a ∈ v, a < i.1) ∧ i.2.1.Nodup

/-- A testing set of at most `K` strings over `Σ` exists: a set `Π` such that any two
distinct strings of `V` are separated by some `π ∈ Π` occurring as a substring in exactly one
of them. -/
def StringBarcodingFeasible (i : StringBarcodingInstance) : Prop :=
  ∃ P : Finset (List ℕ), P.card ≤ i.2.2 ∧ (∀ π ∈ P, ∀ a ∈ π, a < i.1) ∧
    ∀ v ∈ i.2.1, ∀ w ∈ i.2.1, v ≠ w → ∃ π ∈ P, ¬ (π <:+: v ↔ π <:+: w)

open Classical in
/-- STRING BARCODING as a decision problem over bitstrings. -/
noncomputable def stringBarcodingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := StringBarcodingInstance) x with
  | some i => decide (WellFormed i ∧ StringBarcodingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StringBarcoding
