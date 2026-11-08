/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET SPLITTING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SET SPLITTING (hypergraph
2-coloring); S. Lovasz, "Coverings and colorings of hypergraphs" (1973).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetSplitting

/-!
# SET SPLITTING is NP-complete

A list of subsets of a universe of size `n`. The question is whether the universe can be split
into two parts so that every set meets both parts (hypergraph 2-colorability).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A set-splitting instance: universe size, list of subsets. -/
abbrev SetSplittingInstance := ℕ × List (List ℕ)

/-- Well-formedness of an instance. -/
def WellFormed (i : SetSplittingInstance) : Prop :=
  ∀ s ∈ i.2, s.Nodup ∧ ∀ x ∈ s, x < i.1

/-- A split meeting every set in both parts. -/
def SetSplittingFeasible
    (i : SetSplittingInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ v ∈ S, v < i.1) ∧
    ∀ s ∈ i.2, (∃ x ∈ s, x ∈ S) ∧ ∃ y ∈ s, y ∉ S

open Classical in
/-- SET SPLITTING as a decision problem over bitstrings. -/
noncomputable def setSplittingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetSplittingInstance) x with
  | some i => decide (WellFormed i ∧ SetSplittingFeasible i)
  | none => false

/-- **SET SPLITTING is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), SET SPLITTING (hypergraph 2-coloring); S. Lovasz, "Coverings and
colorings of hypergraphs" (1973). -/
public theorem_wanted setSplitting_npComplete :
    setSplittingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L setSplittingDec

end MetaMathlibExt.Complexity.NPComplete.SetSplitting
