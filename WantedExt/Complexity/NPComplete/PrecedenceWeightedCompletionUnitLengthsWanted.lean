/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME with unit task lengths is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 237, problem [SS4] SEQUENCING TO
MINIMIZE WEIGHTED COMPLETION TIME, comment: "NP-complete in the strong sense and remains so
even if all task lengths are 1";
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PrecedenceWeightedCompletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceWeightedCompletionUnitLengths

open MetaMathlibExt.Complexity.NPComplete.PrecedenceWeightedCompletion

/-!
# SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME with unit task lengths is NP-complete

INSTANCE: a set `T` of tasks, a partial order `<` on `T`, for each task `t ∈ T` the length
`l(t) = 1` and a weight `w(t) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there a
one-processor schedule `σ` for `T` that obeys the precedence constraints and for which the sum,
over all `t ∈ T`, of `(σ(t) + l(t)) · w(t)` is `K` or less?

This is the restriction of SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME, stated in
`WantedExt.Complexity.NPComplete.PrecedenceWeightedCompletionWanted` as an ordering of the
jobs whose weighted sum of completion times is at most `K`, to instances in which every task
has length `1`. The instance type, its `WellFormed` and `PrecedenceWeightedCompletionFeasible`
are reused unchanged. The restricted well-formedness adds unit lengths and the source's
`w(t) ∈ ℤ⁺` and `K ∈ ℤ⁺`, which that module's `WellFormed` does not check. A precedence list
with a cycle is not a partial order; such an instance has no feasible ordering, so it is a
no-instance either way.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance of the restriction: the instance is well-formed for
`PrecedenceWeightedCompletion`, every job has processing time `1` and a positive weight, and
the bound `K` is positive. -/
def RestrictedWellFormed (i : PrecedenceWeightedCompletionInstance) : Prop :=
  WellFormed i ∧ (∀ j ∈ i.1, j.1 = 1 ∧ 0 < j.2) ∧ 0 < i.2.2

open Classical in
/-- SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME with unit task lengths, as a decision
problem over bitstrings. -/
noncomputable def precedenceWeightedCompletionUnitLengthsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceWeightedCompletionInstance) x with
  | some i => decide (RestrictedWellFormed i ∧ PrecedenceWeightedCompletionFeasible i)
  | none => false

/-- **SEQUENCING TO MINIMIZE WEIGHTED COMPLETION TIME remains NP-complete when all task
lengths are `1`.** Source: Garey and Johnson (1979), [SS4], comment; Lenstra and Rinnooy Kan
(1978). -/
public theorem_wanted precedenceWeightedCompletionUnitLengths_npComplete :
    precedenceWeightedCompletionUnitLengthsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceWeightedCompletionUnitLengthsDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceWeightedCompletionUnitLengths
