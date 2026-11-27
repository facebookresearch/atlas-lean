/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERSECTION PATTERN is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SP9] INTERSECTION PATTERN (reference:
[Chvátal, 1978]; transformation from GRAPH 3-COLORABILITY);
V. Chvátal, "Recognizing intersection patterns", Annals of Discrete Mathematics 8 (1980),
249-251, doi:10.1016/S0167-5060(08)70883-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntersectionPattern

/-!
# INTERSECTION PATTERN is NP-complete

INSTANCE: an `n × n` matrix `A = (a_ij)` with entries in `ℤ₀⁺`.
QUESTION: is there a collection `C = {C₁, C₂, ..., Cₙ}` of sets such that for all `i, j`,
`1 ≤ i, j ≤ n`, `a_ij = |Cᵢ ∩ Cⱼ|`?

The matrix is the list of its `n` rows, each a list of `n` natural numbers; rows and columns are
indexed from `0`. Since `a_ii = |Cᵢ|`, the sets are finite, and a finite family of finite sets
can be relabelled into the natural numbers without changing any intersection size, so the sets
are taken to be finite sets of natural numbers `C : Fin n → Finset ℕ`. The collection is indexed
by `i`, so `Cᵢ = Cⱼ` is allowed for `i ≠ j`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the rows of the matrix `A`. -/
abbrev IntersectionPatternInstance := List (List ℕ)

/-- Well-formedness of an instance: `A` is square, every row having as many entries as there are
rows. -/
def WellFormed (A : IntersectionPatternInstance) : Prop :=
  ∀ row ∈ A, row.length = A.length

/-- Some sets `C₀, ..., C_{n-1}` satisfy `|Cᵢ ∩ Cⱼ| = a_ij` for all `i, j`. -/
def IntersectionPatternFeasible (A : IntersectionPatternInstance) : Prop :=
  ∃ C : Fin A.length → Finset ℕ, ∀ i j : Fin A.length,
    (C i ∩ C j).card = (A.getD i []).getD j 0

open Classical in
/-- INTERSECTION PATTERN as a decision problem over bitstrings. -/
noncomputable def intersectionPatternDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntersectionPatternInstance) x with
  | some A => decide (WellFormed A ∧ IntersectionPatternFeasible A)
  | none => false

/-- **INTERSECTION PATTERN is NP-complete.** Source: Garey and Johnson (1979), [SP9];
Chvátal (1980). -/
public theorem_wanted intersectionPattern_npComplete :
    intersectionPatternDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L intersectionPatternDec

end MetaMathlibExt.Complexity.NPComplete.IntersectionPattern
