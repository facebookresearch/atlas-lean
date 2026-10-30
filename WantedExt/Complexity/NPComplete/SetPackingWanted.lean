/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET PACKING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SET PACKING; R. M. Karp,
"Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetPacking

/-!
# SET PACKING is NP-complete

A list of subsets of a universe of size `n` and a bound `K`. The question is whether at least
`K` of the subsets are pairwise disjoint. The chosen sublist must have no duplicate sets: two
copies of the same set do not count as disjoint.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A set-packing instance: universe size, list of subsets, bound. -/
abbrev SetPackingInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : SetPackingInstance) : Prop :=
  ∀ s ∈ i.2.1, s.Nodup ∧ ∀ x ∈ s, x < i.1

/-- At least `K` pairwise disjoint subsets. -/
def SetPackingFeasible
    (i : SetPackingInstance) : Prop :=
  ∃ sub : List (List ℕ), sub.Sublist i.2.1 ∧ sub.Nodup ∧ i.2.2 ≤ sub.length ∧
    ∀ s1 ∈ sub, ∀ s2 ∈ sub, s1 ≠ s2 → ∀ x, x ∈ s1 → x ∉ s2

open Classical in
/-- SET PACKING as a decision problem over bitstrings. -/
noncomputable def setPackingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetPackingInstance) x with
  | some i => decide (WellFormed i ∧ SetPackingFeasible i)
  | none => false

/-- **SET PACKING is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), SET PACKING; R. M. Karp, "Reducibility among combinatorial
problems" (1972). -/
public theorem_wanted setPacking_npComplete :
    setPackingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L setPackingDec

end MetaMathlibExt.Complexity.NPComplete.SetPacking
