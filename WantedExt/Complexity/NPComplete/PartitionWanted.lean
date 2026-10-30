/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PARTITION; R. M. Karp,
"Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Partition

/-!
# PARTITION is NP-complete

A list of natural numbers. The question is whether some sublist sums to exactly half the total,
equivalently twice its sum equals the total sum.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A partition instance: a list of natural numbers. -/
abbrev PartitionInstance := List ℕ

/-- A sublist summing to half the total. -/
def PartitionFeasible
    (i : PartitionInstance) : Prop :=
  ∃ s : List ℕ, s.Sublist i ∧ s.sum * 2 = i.sum

open Classical in
/-- PARTITION as a decision problem over bitstrings. -/
noncomputable def partitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionInstance) x with
  | some i => decide (PartitionFeasible i)
  | none => false

/-- **PARTITION is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), PARTITION; R. M. Karp, "Reducibility among combinatorial problems"
(1972). -/
public theorem_wanted partition_npComplete :
    partitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionDec

end MetaMathlibExt.Complexity.NPComplete.Partition
