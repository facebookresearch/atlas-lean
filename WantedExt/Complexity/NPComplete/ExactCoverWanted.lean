/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXACT COVER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EXACT COVER; R. M. Karp,
"Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExactCover

/-!
# EXACT COVER is NP-complete

A universe of size `n` (elements `0, …, n - 1`) and a list of subsets. The question is whether
some subcollection covers every element exactly once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An exact-cover instance: universe size, list of subsets. -/
abbrev ExactCoverInstance := ℕ × List (List ℕ)

/-- Well-formedness of an instance. -/
def WellFormed (i : ExactCoverInstance) : Prop :=
  ∀ s ∈ i.2, s.Nodup ∧ ∀ x ∈ s, x < i.1

/-- A subcollection covering every element exactly once. -/
def ExactCoverFeasible
    (i : ExactCoverInstance) : Prop :=
  ∃ sub : List (List ℕ), sub.Sublist i.2 ∧
    ∀ x < i.1, ∃! s ∈ sub, x ∈ s

open Classical in
/-- EXACT COVER as a decision problem over bitstrings. -/
noncomputable def exactCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExactCoverInstance) x with
  | some i => decide (WellFormed i ∧ ExactCoverFeasible i)
  | none => false

/-- **EXACT COVER is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), EXACT COVER; R. M. Karp, "Reducibility among combinatorial
problems" (1972). -/
public theorem_wanted exactCover_npComplete :
    exactCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L exactCoverDec

end MetaMathlibExt.Complexity.NPComplete.ExactCover
