/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-PARTITION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), 3-PARTITION (strongly NP-
complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreePartition

/-!
# 3-PARTITION is NP-complete

A list of `3m` natural numbers and a target `B`. The question is whether the numbers can be
split into `m` triples each summing to `B`. The usual `B / 4 < a < B / 2` promise is not needed
when the triple size is explicit.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A 3-partition instance: numbers (a multiple of 3 of them), target. -/
abbrev ThreePartitionInstance := List ℕ × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : ThreePartitionInstance) : Prop :=
  i.1.length % 3 = 0

/-- A split into triples each summing to the target. -/
def ThreePartitionFeasible
    (i : ThreePartitionInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1.length ∧
    (∀ j < i.1.length, assign.getD j 0 < i.1.length / 3) ∧
    ∀ t < i.1.length / 3,
      ((List.range i.1.length).filter (fun j => assign.getD j 0 == t)).length = 3 ∧
      (Finset.range i.1.length).sum
        (fun j => if assign.getD j 0 = t then i.1.getD j 0 else 0) = i.2

open Classical in
/-- 3-PARTITION as a decision problem over bitstrings. -/
noncomputable def threePartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreePartitionInstance) x with
  | some i => decide (WellFormed i ∧ ThreePartitionFeasible i)
  | none => false

/-- **3-PARTITION is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), 3-PARTITION (strongly NP-complete). -/
public theorem_wanted threePartition_npComplete :
    threePartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threePartitionDec

end MetaMathlibExt.Complexity.NPComplete.ThreePartition
