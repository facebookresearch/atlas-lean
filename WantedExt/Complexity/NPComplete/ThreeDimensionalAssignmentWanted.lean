/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-DIMENSIONAL ASSIGNMENT is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry
MINIMUM 3-DIMENSIONAL ASSIGNMENT (weighted version of 3-DIMENSIONAL MATCHING);
Y. Crama and F. C. R. Spieksma, "Approximation algorithms for three-dimensional assignment
problems with triangle inequalities", European Journal of Operational Research 60 (1992),
273-279, doi:10.1016/0377-2217(92)90078-N;
R. M. Karp, "Reducibility among combinatorial problems", Complexity of Computer Computations,
Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (3-DIMENSIONAL MATCHING).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalAssignment

/-!
# 3-DIMENSIONAL ASSIGNMENT is NP-complete

INSTANCE: three sets `X`, `Y` and `W`, a cost function `c : X × Y × W → ℕ`, and a positive
integer `K`.
QUESTION: is there an assignment `A`, i.e. a subset `A ⊆ X × Y × W` such that every element of
`X ∪ Y ∪ W` belongs to exactly one triple in `A`, of cost `∑_{(x, y, w) ∈ A} c(x, y, w) ≤ K`?
(The decision version of the compendium's MINIMUM 3-DIMENSIONAL ASSIGNMENT, the weighted
version of 3-DIMENSIONAL MATCHING: with costs `0` on the given triples and `K + 1` elsewhere,
an assignment of cost at most `K` is a perfect 3-dimensional matching.)

The sets are `X = Fin p`, `Y = Fin q`, `W = Fin r` (disjoint, as the three coordinates of a
triple), and the cost function is the `p × q × r` table of its values, `c(x, y, w)` being entry
`w` of entry `y` of entry `x`; costs and `K` in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the sizes `p`, `q`, `r` of `X`, `Y`, `W`, the cost table, and `K`. -/
abbrev ThreeDimensionalAssignmentInstance := ℕ × ℕ × ℕ × List (List (List ℕ)) × ℕ

/-- A triple of `X × Y × W`. -/
abbrev Triple (i : ThreeDimensionalAssignmentInstance) :=
  Fin i.1 × Fin i.2.1 × Fin i.2.2.1

/-- The cost `c(x, y, w)` of a triple. -/
def cost (i : ThreeDimensionalAssignmentInstance) (t : Triple i) : ℕ :=
  ((i.2.2.2.1.getD t.1 []).getD t.2.1 []).getD t.2.2 0

/-- Well-formedness: the cost table is `p × q × r`, and `K` is positive. -/
def WellFormed (i : ThreeDimensionalAssignmentInstance) : Prop :=
  i.2.2.2.1.length = i.1 ∧ (∀ row ∈ i.2.2.2.1, row.length = i.2.1) ∧
    (∀ row ∈ i.2.2.2.1, ∀ col ∈ row, col.length = i.2.2.1) ∧ 0 < i.2.2.2.2

/-- Some assignment `A` (every element of `X`, `Y`, `W` in exactly one triple of `A`) has cost
at most `K`. -/
def ThreeDimensionalAssignmentFeasible (i : ThreeDimensionalAssignmentInstance) : Prop :=
  ∃ A : Finset (Triple i),
    (∀ x, (A.filter fun t => t.1 = x).card = 1) ∧
    (∀ y, (A.filter fun t => t.2.1 = y).card = 1) ∧
    (∀ w, (A.filter fun t => t.2.2 = w).card = 1) ∧
    ∑ t ∈ A, cost i t ≤ i.2.2.2.2

open Classical in
/-- 3-DIMENSIONAL ASSIGNMENT as a decision problem over bitstrings. -/
noncomputable def threeDimensionalAssignmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeDimensionalAssignmentInstance) x with
  | some i => decide (WellFormed i ∧ ThreeDimensionalAssignmentFeasible i)
  | none => false

/-- **3-DIMENSIONAL ASSIGNMENT is NP-complete.** Source: Crescenzi and Kann, MINIMUM 3-DIMENSIONAL
ASSIGNMENT; Crama and Spieksma (1992); Karp (1972). -/
public theorem_wanted threeDimensionalAssignment_npComplete :
    threeDimensionalAssignmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeDimensionalAssignmentDec

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalAssignment
