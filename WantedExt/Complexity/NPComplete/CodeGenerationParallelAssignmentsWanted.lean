/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION FOR PARALLEL ASSIGNMENTS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO6] CODE GENERATION
FOR PARALLEL ASSIGNMENTS;
R. Sethi, "A note on implementing parallel assignment instructions",
Information Processing Letters 2 (1973), 91-95,
doi:10.1016/0020-0190(73)90024-0.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CodeGenerationParallelAssignments

/-!
# CODE GENERATION FOR PARALLEL ASSIGNMENTS is NP-complete

INSTANCE: a set `V = {v₁, ..., vₙ}` of variables, a set `A = {A₁, ..., Aₙ}` of assignments,
each `Aᵢ` of the form "`vᵢ ← op(Bᵢ)`" for some subset `Bᵢ ⊆ V`, and a positive integer `K`.
QUESTION: is there an ordering `v_π(1), ..., v_π(n)` of `V` such that there are at most `K`
values of `i`, `1 ≤ i ≤ n`, for which `v_π(i) ∈ B_π(j)` for some `j > i`?

Executing the assignments in the order `π`, the counted positions are those whose variable is
overwritten before a later assignment reads it (each needs a temporary). Variables are
`Fin n`, `Bᵢ` is the `i`-th list of the instance, the ordering is a permutation `π` of
`Fin n` (position `i` executes assignment `A_π(i)`, which writes `v_π(i)`), and positions
are 0-based.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables (and assignments), the operand sets
`B₁, ..., Bₙ` as lists of variable indices, and the bound `K`. -/
abbrev CodeGenerationParallelAssignmentsInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: there are exactly `n` operand sets, each a list of
distinct variables in range (a subset of `V`), and `K` is positive. -/
def WellFormed (i : CodeGenerationParallelAssignmentsInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ b ∈ i.2.1, b.Nodup ∧ ∀ v ∈ b, v < i.1) ∧ 0 < i.2.2

/-- An ordering `π` of the variables with at most `K` positions `i` whose variable `v_π(i)`
lies in `B_π(j)` for some later position `j > i`. -/
def CodeGenerationParallelAssignmentsFeasible (i : CodeGenerationParallelAssignmentsInstance) :
    Prop :=
  ∃ π : Equiv.Perm (Fin i.1),
    {p : Fin i.1 | ∃ q, p < q ∧ ((π p : ℕ) ∈ i.2.1.getD (π q) [])}.ncard ≤ i.2.2

open Classical in
/-- CODE GENERATION FOR PARALLEL ASSIGNMENTS as a decision problem over bitstrings. -/
noncomputable def codeGenerationParallelAssignmentsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CodeGenerationParallelAssignmentsInstance) x with
  | some i => decide (WellFormed i ∧ CodeGenerationParallelAssignmentsFeasible i)
  | none => false

/-- **CODE GENERATION FOR PARALLEL ASSIGNMENTS is NP-complete.** Source: Garey and Johnson
(1979), [PO6]; Sethi (1973). -/
public theorem_wanted codeGenerationParallelAssignments_npComplete :
    codeGenerationParallelAssignmentsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L codeGenerationParallelAssignmentsDec

end MetaMathlibExt.Complexity.NPComplete.CodeGenerationParallelAssignments
