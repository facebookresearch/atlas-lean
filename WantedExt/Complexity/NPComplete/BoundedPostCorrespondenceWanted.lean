/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED POST CORRESPONDENCE PROBLEM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR11] BOUNDED POST CORRESPONDENCE PROBLEM
(reference: [Constable, Hunt, and Sahni, 1974]; generic transformation);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of scheme
equivalence", Technical Report 74-201, Department of Computer Science, Cornell University
(1974), hdl:1813/6041, proof of Proposition 2.21.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Decidability.PCP
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedPostCorrespondence

open Cslib.Decidability.Post (Domino IsSolution)

/-!
# BOUNDED POST CORRESPONDENCE PROBLEM is NP-complete

INSTANCE: a finite alphabet `Σ`, two sequences `a = (a₁, a₂, ..., aₙ)` and
`b = (b₁, b₂, ..., bₙ)` of strings from `Σ*`, and a positive integer `K ≤ n`.
QUESTION: is there a sequence `i₁, i₂, ..., i_k` of `k ≤ K` (not necessarily distinct) positive
integers, each between `1` and `n`, such that the two strings `a_{i₁} a_{i₂} ⋯ a_{i_k}` and
`b_{i₁} b_{i₂} ⋯ b_{i_k}` are identical?

The alphabet is `{0, …, |Σ| - 1}` and the two sequences are given as the list of the `n` pairs
`(aᵢ, bᵢ)`, CSLib's dominoes (`Cslib.Decidability.Post.Domino`). A sequence of indices is the
same as the sequence of the dominoes they select, and CSLib's PCP solutions
(`Cslib.Decidability.Post.IsSolution`) are the nonempty sequences of dominoes of the instance
whose tops and bottoms concatenate to the same word. The sequence must be nonempty (`k ≥ 1`),
as in the unbounded Post correspondence problem that the source's comment refers to; with
`k = 0` allowed every instance would be a yes-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the size `|Σ|` of the alphabet, the pairs `(aᵢ, bᵢ)`, and the bound `K`. -/
abbrev BoundedPostCorrespondenceInstance := ℕ × List (Domino ℕ) × ℕ

/-- Well-formedness of an instance: all strings are over the alphabet `{0, …, |Σ| - 1}`, and
`0 < K ≤ n`. -/
def WellFormed (i : BoundedPostCorrespondenceInstance) : Prop :=
  (∀ d ∈ i.2.1, (∀ x ∈ d.1, x < i.1) ∧ ∀ x ∈ d.2, x < i.1) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- A nonempty sequence of at most `K` pairs of the instance whose `a`-strings and `b`-strings
concatenate to the same string. -/
def BoundedPostCorrespondenceFeasible (i : BoundedPostCorrespondenceInstance) : Prop :=
  ∃ s : List (Domino ℕ), IsSolution i.2.1 s ∧ s.length ≤ i.2.2

open Classical in
/-- BOUNDED POST CORRESPONDENCE PROBLEM as a decision problem over bitstrings. -/
noncomputable def boundedPostCorrespondenceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedPostCorrespondenceInstance) x with
  | some i => decide (WellFormed i ∧ BoundedPostCorrespondenceFeasible i)
  | none => false

/-- **BOUNDED POST CORRESPONDENCE PROBLEM is NP-complete.** Source: Garey and Johnson (1979),
[SR11]; Constable, Hunt and Sahni (1974). -/
public theorem_wanted boundedPostCorrespondence_npComplete :
    boundedPostCorrespondenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boundedPostCorrespondenceDec

end MetaMathlibExt.Complexity.NPComplete.BoundedPostCorrespondence
