/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET COVER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SET COVER; R. M. Karp,
"Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetCover

/-!
# SET COVER is NP-complete

A universe of size `n`, a list of subsets, and a bound `K`. The question is whether at most `K`
subsets cover the universe.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A set-cover instance: universe size, list of subsets, bound. -/
abbrev SetCoverInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : SetCoverInstance) : Prop :=
  ∀ s ∈ i.2.1, s.Nodup ∧ ∀ x ∈ s, x < i.1

/-- At most `K` subsets covering the universe. -/
def SetCoverFeasible
    (i : SetCoverInstance) : Prop :=
  ∃ sub : List (List ℕ), sub.Sublist i.2.1 ∧ sub.length ≤ i.2.2 ∧
    ∀ x < i.1, ∃ s ∈ sub, x ∈ s

open Classical in
/-- SET COVER as a decision problem over bitstrings. -/
noncomputable def setCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetCoverInstance) x with
  | some i => decide (WellFormed i ∧ SetCoverFeasible i)
  | none => false

/-- **SET COVER is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), SET COVER; R. M. Karp, "Reducibility among combinatorial problems"
(1972). -/
public theorem_wanted setCover_npComplete :
    setCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L setCoverDec

end MetaMathlibExt.Complexity.NPComplete.SetCover
