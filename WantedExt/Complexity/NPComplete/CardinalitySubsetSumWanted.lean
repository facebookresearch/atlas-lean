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

/-- **Exact-cardinality subset-sum instances.** An exact-cardinality subset-sum instance is a
triple $(a, K, T)$ consisting of a list $a$ of natural numbers, a natural number $K$ (the
cardinality) and a natural number $T$ (the target). -/
abbrev CardinalitySubsetSumInstance := List ℕ × ℕ × ℕ

/-- **Feasibility of an exact-cardinality subset-sum instance.** An exact-cardinality subset-sum
instance $(a, K, T)$ is feasible when some subsequence of the list $a$ (entries kept in order, not
necessarily contiguous) has exactly $K$ entries and sum $T$. -/
def CardinalitySubsetSumFeasible
    (i : CardinalitySubsetSumInstance) : Prop :=
  ∃ s : List ℕ, s.Sublist i.1 ∧ s.length = i.2.1 ∧ s.sum = i.2.2

open Classical in
/-- **Exact-cardinality subset sum as a decision problem.** The decision problem
EXACT-CARDINALITY SUBSET SUM accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding, to an exact-cardinality subset-sum instance that is feasible; it rejects every
bitstring that does not decode. -/
noncomputable def cardinalitySubsetSumDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CardinalitySubsetSumInstance) x with
  | some i => decide (CardinalitySubsetSumFeasible i)
  | none => false

/-- **EXACT-CARDINALITY SUBSET SUM is NP-complete.** The decision problem EXACT-CARDINALITY
SUBSET SUM lies in NP, and every decision problem in NP has a polynomial-time many-one reduction
to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), SUBSET SUM; NP-completeness via the zero-padding
reduction from ordinary subset sum. -/
public theorem_wanted cardinalitySubsetSum_npComplete :
    cardinalitySubsetSumDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cardinalitySubsetSumDec

end MetaMathlibExt.Complexity.NPComplete.CardinalitySubsetSum
