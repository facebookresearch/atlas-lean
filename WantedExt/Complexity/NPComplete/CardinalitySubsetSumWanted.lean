/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXACT-CARDINALITY SUBSET SUM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SUBSET SUM; NP-
completeness via the zero-padding reduction from ordinary subset sum.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CardinalitySubsetSum

/-!
# EXACT-CARDINALITY SUBSET SUM is NP-complete

A list of natural numbers, a cardinality `K`, and a target `T`. The question is whether some
sublist of exactly `K` numbers sums to `T`. Exact-cardinality subset sum, with `K` part of the
input (not the fixed-`K` k-SUM family). NP-completeness follows from ordinary subset sum by
zero-padding: `(as, T)` maps to `(as ++ [0]^|as|, |as|, T)`; a subset of `as` summing to `T`
extends with zeros to size `|as|`, and removing appended zeros preserves the sum.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A cardinality-constrained subset-sum instance: numbers, cardinality K, target. -/
abbrev CardinalitySubsetSumInstance := List ℕ × ℕ × ℕ

/-- A sublist of exactly `K` numbers summing to the target. -/
def CardinalitySubsetSumFeasible
    (i : CardinalitySubsetSumInstance) : Prop :=
  ∃ s : List ℕ, s.Sublist i.1 ∧ s.length = i.2.1 ∧ s.sum = i.2.2

open Classical in
/-- EXACT-CARDINALITY SUBSET SUM as a decision problem over bitstrings. -/
noncomputable def cardinalitySubsetSumDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CardinalitySubsetSumInstance) x with
  | some i => decide (CardinalitySubsetSumFeasible i)
  | none => false

/-- **EXACT-CARDINALITY SUBSET SUM is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), SUBSET SUM; NP-completeness via the zero-padding
reduction from ordinary subset sum. -/
public theorem_wanted cardinalitySubsetSum_npComplete :
    cardinalitySubsetSumDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cardinalitySubsetSumDec

end MetaMathlibExt.Complexity.NPComplete.CardinalitySubsetSum
