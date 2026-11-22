/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIWAY NUMBER PARTITION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MULTIWAY NUMBER PARTITION
(the `K = 2` slice is PARTITION).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiwayPartition

/-!
# MULTIWAY NUMBER PARTITION is NP-complete

A list of natural numbers and a number `K` of parts, with `K ≥ 1`. The question is whether the
numbers can be split into `K` nonempty parts all with the same sum, witnessed by an assignment
using every part label and a common target sum.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A multiway-partition instance: numbers, number of parts K. -/
abbrev MultiwayPartitionInstance := List ℕ × ℕ

/-- A split into `K` nonempty parts of equal sum. -/
def MultiwayPartitionFeasible
    (i : MultiwayPartitionInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1.length ∧ 0 < i.2 ∧
    (∀ j < i.1.length, assign.getD j 0 < i.2) ∧
    (∀ p < i.2, ∃ j < i.1.length, assign.getD j 0 = p) ∧
    ∃ T, ∀ p < i.2, (Finset.range i.1.length).sum
      (fun j => if assign.getD j 0 = p then i.1.getD j 0 else 0) = T

open Classical in
/-- MULTIWAY NUMBER PARTITION as a decision problem over bitstrings. -/
noncomputable def multiwayPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiwayPartitionInstance) x with
  | some i => decide (MultiwayPartitionFeasible i)
  | none => false

/-- **MULTIWAY NUMBER PARTITION is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), MULTIWAY NUMBER PARTITION (the `K = 2` slice is
PARTITION). -/
public theorem_wanted multiwayPartition_npComplete :
    multiwayPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiwayPartitionDec

end MetaMathlibExt.Complexity.NPComplete.MultiwayPartition
