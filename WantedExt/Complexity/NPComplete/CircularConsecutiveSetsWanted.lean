/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CIRCULAR CONSECUTIVE SETS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR18] CONSECUTIVE SETS, p. 230,
comment ("The variant in which we ask only that the elements of each Σᵢ occur in a
consecutive block of |Σᵢ| symbols of the string ww (i.e., we allow blocks that circulate from
the end of w back to its beginning) is also NP-complete [Booth, 1975]");
K. S. Booth, *PQ-Tree Algorithms*, Ph.D. thesis, University of California, Berkeley (1975).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircularConsecutiveSets

/-!
# CIRCULAR CONSECUTIVE SETS is NP-complete

INSTANCE: a finite alphabet `Σ`, a collection `C = {Σ₁, Σ₂, ..., Σₙ}` of subsets of `Σ`, and a
positive integer `K`. QUESTION: is there a string `w ∈ Σ*` with `|w| ≤ K` such that, for each
`i`, the elements of `Σᵢ` occur in a consecutive block of `|Σᵢ|` symbols of the string `ww`
(blocks may circulate from the end of `w` back to its beginning)?

This is the variant of CONSECUTIVE SETS ([SR18]) recorded in Garey and Johnson's comment. The
alphabet is `Σ = {0, ..., s - 1}`. Each subset `Σᵢ` is a list of symbols without repetitions,
so `|Σᵢ|` is its length. The elements of `Σᵢ` occur in a consecutive block of `|Σᵢ|` symbols of
`ww` exactly when some contiguous sublist (`List.IsInfix`) of `w ++ w` is a permutation
(`List.Perm`) of `Σᵢ`. Symbols may repeat in `w`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the alphabet size `s` (symbols `0, ..., s - 1`), the subsets `Σᵢ` (each a list
of symbols), and the bound `K`. -/
abbrev CircularConsecutiveSetsInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every subset lists distinct symbols of the alphabet, and
`K` is positive. -/
def WellFormed (i : CircularConsecutiveSetsInstance) : Prop :=
  (∀ S ∈ i.2.1, S.Nodup ∧ ∀ x ∈ S, x < i.1) ∧ 0 < i.2.2

/-- Some string `w` over the alphabet with `|w| ≤ K` has, for each subset `Σᵢ`, a contiguous
block of `ww` that is a permutation of `Σᵢ`. -/
def CircularConsecutiveSetsFeasible (i : CircularConsecutiveSetsInstance) : Prop :=
  ∃ w : List ℕ, w.length ≤ i.2.2 ∧ (∀ x ∈ w, x < i.1) ∧
    ∀ S ∈ i.2.1, ∃ b : List ℕ, b <:+: w ++ w ∧ b.Perm S

open Classical in
/-- CIRCULAR CONSECUTIVE SETS as a decision problem over bitstrings. -/
noncomputable def circularConsecutiveSetsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := CircularConsecutiveSetsInstance) x with
  | some i => decide (WellFormed i ∧ CircularConsecutiveSetsFeasible i)
  | none => false

/-- **CIRCULAR CONSECUTIVE SETS is NP-complete.** Source: Garey and Johnson (1979), [SR18],
comment; Booth (1975). -/
public theorem_wanted circularConsecutiveSets_npComplete :
    circularConsecutiveSetsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L circularConsecutiveSetsDec

end MetaMathlibExt.Complexity.NPComplete.CircularConsecutiveSets
