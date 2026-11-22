/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HITTING SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP8] HITTING SET;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of
Computer Computations*, Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HittingSet

/-!
# HITTING SET is NP-complete

INSTANCE: a collection `C` of subsets of a finite set `S`, and a positive integer `K ≤ |S|`.
QUESTION: is there a subset `S' ⊆ S` with `|S'| ≤ K` such that `S'` contains at least one
element from each subset in `C`?

The finite set is `S = {0, ..., n - 1}`; the collection `C` is a list of subsets, each given as
a list of elements without repetition, and the hitting set `S'` is a `Finset (Fin n)`.
Garey and Johnson obtain the result from VERTEX COVER (Karp 1972): the instances in which every
subset has two elements are exactly the vertex cover instances.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: `n = |S|` (elements `0, ..., n - 1`), the collection `C` (a list of subsets,
each a list of elements), and the bound `K`. -/
abbrev HittingSetInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every subset in `C` lists elements of `S` without
repetition, and `0 < K ≤ |S|`. -/
def WellFormed (i : HittingSetInstance) : Prop :=
  (∀ c ∈ i.2.1, c.Nodup ∧ ∀ x ∈ c, x < i.1) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- A subset `S'` of `S` with at most `K` elements meets every subset in `C`. -/
def HittingSetFeasible (i : HittingSetInstance) : Prop :=
  ∃ S' : Finset (Fin i.1), S'.card ≤ i.2.2 ∧ ∀ c ∈ i.2.1, ∃ x ∈ S', (x : ℕ) ∈ c

open Classical in
/-- HITTING SET as a decision problem over bitstrings. -/
noncomputable def hittingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HittingSetInstance) x with
  | some i => decide (WellFormed i ∧ HittingSetFeasible i)
  | none => false

/-- **HITTING SET is NP-complete.** Source: Garey and Johnson (1979), [SP8]; Karp (1972). -/
public theorem_wanted hittingSet_npComplete :
    hittingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hittingSetDec

end MetaMathlibExt.Complexity.NPComplete.HittingSet
