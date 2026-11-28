/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED POST CORRESPONDENCE PROBLEM: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR11] BOUNDED POST CORRESPONDENCE PROBLEM
(reference: [Constable, Hunt, and Sahni, 1974]; generic transformation);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of scheme
equivalence", Technical Report 74-201, Department of Computer Science, Cornell University
(1974), hdl:1813/6041, proof of Proposition 2.21.
-/
module

public import CSLibExt.Computability.Decidability.PCP
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedPostCorrespondence

open Cslib.Decidability.Post (Domino IsSolution)

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

end MetaMathlibExt.Complexity.NPComplete.BoundedPostCorrespondence
