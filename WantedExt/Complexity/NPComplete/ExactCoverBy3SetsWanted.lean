/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXACT COVER BY 3-SETS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EXACT COVER BY 3-SETS.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3Sets

/-!
# EXACT COVER BY 3-SETS is NP-complete

A universe of size `3q` (elements `0, …, 3q - 1`) and a list of three-element subsets. The
question is whether some subcollection covers every element exactly once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An X3C instance: q (universe size 3q), list of three-element sets. -/
abbrev ExactCoverBy3SetsInstance := ℕ × List (List ℕ)

/-- Well-formedness of an instance. -/
def WellFormed (i : ExactCoverBy3SetsInstance) : Prop :=
  ∀ s ∈ i.2, s.length = 3 ∧ s.Nodup ∧ ∀ x ∈ s, x < 3 * i.1

/-- A subcollection covering every element exactly once. -/
def ExactCoverBy3SetsFeasible
    (i : ExactCoverBy3SetsInstance) : Prop :=
  ∃ sub : List (List ℕ), sub.Sublist i.2 ∧
    ∀ x < 3 * i.1, ∃! s ∈ sub, x ∈ s

open Classical in
/-- EXACT COVER BY 3-SETS as a decision problem over bitstrings. -/
noncomputable def exactCoverBy3SetsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExactCoverBy3SetsInstance) x with
  | some i => decide (WellFormed i ∧ ExactCoverBy3SetsFeasible i)
  | none => false

/-- **EXACT COVER BY 3-SETS is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), EXACT COVER BY 3-SETS. -/
public theorem_wanted exactCoverBy3Sets_npComplete :
    exactCoverBy3SetsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L exactCoverBy3SetsDec

end MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3Sets
