/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIAL DIGEST SUPERSET is NP-complete

Source:
M. Cieliebak, S. Eidenbenz and P. Penna, "Noisy data make the partial digest problem NP-hard",
in *Algorithms in Bioinformatics (WABI 2003)*, Lecture Notes in Computer Science 2812 (2003),
111-123, doi:10.1007/978-3-540-39763-2_9; also Technical Report 381, Department of Computer
Science, ETH Zurich (2002), doi:10.3929/ethz-a-006665694, Section 2, Theorem 1 (MIN PARTIAL
DIGEST SUPERSET is NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartialDigestSuperset

/-!
# PARTIAL DIGEST SUPERSET is NP-complete

INSTANCE: a multiset `D = {d₁, …, d_k}` of positive integers and an integer `t`.
QUESTION: is there a set `P = {p₁, …, p_m}` of `m ≤ t` integers such that
`D ⊆ Δ(P) = {|pᵢ - pⱼ| | 1 ≤ i < j ≤ m}`, the inclusion and `Δ(P)` taken as multisets?

This is the decision version of Cieliebak, Eidenbenz and Penna's MIN PARTIAL DIGEST SUPERSET
(find the minimum `m` such that some set of `m` integers covers `D`): the partial digest problem
with omitted distances. Their Theorem 1 reduces EQUAL SUM SUBSETS on `n` numbers to the question
whether `D` (the same `n` numbers) is covered by at most `t = n` points, so this decision problem
is NP-hard.

The multiset `D` is a list of natural numbers, read as a `Multiset`. `P` is a finite set of
integers, and `Δ(P)` is the multiset of `q - p` over the pairs `p < q` of points of `P`, one
entry per pair. Points that are an endpoint of no pair used to cover `D` can be dropped, and the
remaining points split into groups linked by those pairs, each spanning at most the sum of `D`;
shifting the groups apart gives a witness with coordinates in `[0, sum D + t]`, so membership in
NP holds. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the distances `D` (a list read as a multiset) and the bound `t`. -/
abbrev PartialDigestSupersetInstance := List ℕ × ℕ

/-- Well-formedness of an instance: every distance is positive. -/
def WellFormed (i : PartialDigestSupersetInstance) : Prop :=
  ∀ d ∈ i.1, 0 < d

/-- The multiset `Δ(P)` of pairwise distances of a finite set of integers, one entry per pair of
points. -/
def distances (P : Finset ℤ) : Multiset ℕ :=
  (((P ×ˢ P).filter fun q => q.1 < q.2).val.map fun q => (q.2 - q.1).toNat)

/-- Some set `P` of at most `t` integers whose distance multiset contains `D`. -/
def PartialDigestSupersetFeasible (i : PartialDigestSupersetInstance) : Prop :=
  ∃ P : Finset ℤ, P.card ≤ i.2 ∧ (i.1 : Multiset ℕ) ≤ distances P

open Classical in
/-- PARTIAL DIGEST SUPERSET as a decision problem over bitstrings. -/
noncomputable def partialDigestSupersetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartialDigestSupersetInstance) x with
  | some i => decide (WellFormed i ∧ PartialDigestSupersetFeasible i)
  | none => false

/-- **PARTIAL DIGEST SUPERSET is NP-complete.** Source: Cieliebak, Eidenbenz and Penna (2003),
Theorem 1. -/
public theorem_wanted partialDigestSuperset_npComplete :
    partialDigestSupersetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partialDigestSupersetDec

end MetaMathlibExt.Complexity.NPComplete.PartialDigestSuperset
