/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRING BARCODING is NP-complete

Source:
G. Lancia and R. Rizzi, "The approximability of the String Barcoding problem", Algorithms for
Molecular Biology 1 (2006), article 12, doi:10.1186/1748-7188-1-12 (problem introduced by
S. Rash and D. Gusfield, "String barcoding: uncovering optimal virus signatures", RECOMB 2002,
doi:10.1145/565196.565229).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StringBarcoding

/-!
# STRING BARCODING is NP-complete

INSTANCE: a finite alphabet `Σ`, a set `V = {v₁, ..., vₙ}` of strings over `Σ`, and an integer
`K`. QUESTION: is there a testing set `Π` of at most `K` strings over `Σ`, that is, a set `Π`
such that for every pair `vᵢ, vⱼ` with `i < j` some `π ∈ Π` is a substring of `vᵢ` or of `vⱼ`
but not of both? Equivalently, the barcodes of the `vᵢ` (the vectors recording which members
of `Π` occur in `vᵢ` as substrings) are pairwise distinct.

Rash and Gusfield (2002) introduced the problem and left the complexity of this unconstrained
version (no bound on the length of the probes `π`) open; Lancia and Rizzi (2006) prove it
NP-complete, already for binary alphabets.

The alphabet is `Σ = {0, ..., |Σ| - 1}`, given by its size; strings are lists of letters, and
"substring" is a contiguous block, `List.IsInfix` (`π <:+: v`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **STRING BARCODING is NP-complete.** Source: Lancia and Rizzi (2006); Rash and Gusfield
(2002). -/
public theorem_wanted stringBarcoding_npComplete :
    stringBarcodingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L stringBarcodingDec

end MetaMathlibExt.Complexity.NPComplete.StringBarcoding
