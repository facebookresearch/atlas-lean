/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERSECTION PATTERN with all diagonal entries 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), p. 222, problem [SP9] INTERSECTION PATTERN
(comment: remains NP-complete even if all `a_ii = 3`; reference: [Chvátal, 1978]);
V. Chvátal, "Recognizing intersection patterns", Annals of Discrete Mathematics 8 (1980),
249-251, doi:10.1016/S0167-5060(08)70883-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.IntersectionPatternWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntersectionPatternDiagonalThree

open MetaMathlibExt.Complexity.NPComplete.IntersectionPattern

/-!
# INTERSECTION PATTERN with all diagonal entries 3 is NP-complete

INSTANCE: an `n × n` matrix `A = (a_ij)` with entries in `ℤ₀⁺` and `a_ii = 3` for
`1 ≤ i ≤ n`.
QUESTION: is there a collection `C = {C₁, C₂, ..., Cₙ}` of sets such that for all `i, j`,
`1 ≤ i, j ≤ n`, `a_ij = |Cᵢ ∩ Cⱼ|`?

This is the restriction of `WantedExt.Complexity.NPComplete.IntersectionPatternWanted` ([SP9])
to matrices whose diagonal entries all equal `3`. The instance type, the parent
well-formedness condition and the question are that module's (`IntersectionPatternInstance`,
`IntersectionPattern.WellFormed`, `IntersectionPatternFeasible`): the matrix is the square list
of its rows, indexed from `0`, and the question asks for finite sets of natural numbers
`C : Fin n → Finset ℕ` with `|Cᵢ ∩ Cⱼ| = a_ij` for all `i, j`. `WellFormed` adds the
restriction `a_ii = 3` for every row index `i`. Since `a_ii = |Cᵢ ∩ Cᵢ| = |Cᵢ|`, every `Cᵢ` of a
solution has exactly three elements, so every off-diagonal entry of a yes-instance is at most
`3`; larger entries are allowed in the instance and make it a no-instance.

Garey and Johnson record the restriction in their comment on [SP9], whose reference is
Chvátal's paper (cited there as 1978, published 1980); the comment adds that the case
`a_ii = 2` is solvable in polynomial time. With every set of size three, a certificate lists
at most `3n` elements, so membership in NP holds for this restriction.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the matrix is square and every diagonal entry is `3`. -/
def WellFormed (A : IntersectionPatternInstance) : Prop :=
  IntersectionPattern.WellFormed A ∧ ∀ i : Fin A.length, (A.getD i []).getD i 0 = 3

open Classical in
/-- INTERSECTION PATTERN with all diagonal entries 3 as a decision problem over bitstrings. -/
noncomputable def intersectionPatternDiagonalThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntersectionPatternInstance) x with
  | some A => decide (WellFormed A ∧ IntersectionPatternFeasible A)
  | none => false

/-- **INTERSECTION PATTERN with all diagonal entries 3 is NP-complete.** Source: Garey and
Johnson (1979), [SP9]; Chvátal (1980). -/
public theorem_wanted intersectionPatternDiagonalThree_npComplete :
    intersectionPatternDiagonalThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L intersectionPatternDiagonalThreeDec

end MetaMathlibExt.Complexity.NPComplete.IntersectionPatternDiagonalThree
