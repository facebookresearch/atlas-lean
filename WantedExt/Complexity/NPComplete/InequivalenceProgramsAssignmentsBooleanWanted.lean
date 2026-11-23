/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS for `V = {0, 1}` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO12] INEQUIVALENCE OF PROGRAMS
WITH ASSIGNMENTS, p. 275 (comment: remains NP-complete for `V = {0, 1}`; reference
[Downey and Sethi, 1976]);
P. J. Downey and R. Sethi, "Assignment commands and array structures", Proceedings of the
17th Annual Symposium on Foundations of Computer Science (1976), 57-66,
doi:10.1109/SFCS.1976.7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.InequivalenceProgramsAssignmentsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceProgramsAssignmentsBoolean

/-!
# INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS for `V = {0, 1}` is NP-complete

Given a finite set `X` of variables, two programs `P₁` and `P₂`, each a sequence of assignments
of the form `x₀ ← if x₁ = x₂ then x₃ else x₄` with the `xᵢ` in `X`, and the value set
`V = {0, 1}`, is there an initial assignment of a value from `V` to each variable in `X` such
that the two programs yield different final values for some variable in `X`?

This is the restriction of `WantedExt.Complexity.NPComplete.InequivalenceProgramsAssignmentsWanted`
to the value set `V = {0, 1}`. The instance type, the program semantics, the parent
well-formedness condition and the question are that module's
(`InequivalenceProgramsAssignments.InequivalenceProgramsAssignmentsInstance`,
`InequivalenceProgramsAssignments.run`, `InequivalenceProgramsAssignments.WellFormed`,
`InequivalenceProgramsAssignments.InequivalenceProgramsAssignmentsFeasible`); the parent
gives the value set `{0, …, |V| - 1}` by its size `|V|`, and the restriction `|V| = 2`, that
is `V = {0, 1}`, is added to `WellFormed`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed INEQUIVALENCE OF PROGRAMS WITH
ASSIGNMENTS instance (every assignment names only variables of `X`), and the value set is
`V = {0, 1}` (`|V| = 2`). -/
def WellFormed
    (i : InequivalenceProgramsAssignments.InequivalenceProgramsAssignmentsInstance) : Prop :=
  InequivalenceProgramsAssignments.WellFormed i ∧ i.2.2.2 = 2

open Classical in
/-- INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS for `V = {0, 1}` as a decision problem over
bitstrings. -/
noncomputable def inequivalenceProgramsAssignmentsBooleanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InequivalenceProgramsAssignments.InequivalenceProgramsAssignmentsInstance) x with
  | some i =>
      decide (WellFormed i ∧
        InequivalenceProgramsAssignments.InequivalenceProgramsAssignmentsFeasible i)
  | none => false

/-- **INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS is NP-complete for `V = {0, 1}`.** Source:
Garey and Johnson (1979), [PO12]; Downey and Sethi (1976). -/
public theorem_wanted inequivalenceProgramsAssignmentsBoolean_npComplete :
    inequivalenceProgramsAssignmentsBooleanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inequivalenceProgramsAssignmentsBooleanDec

end MetaMathlibExt.Complexity.NPComplete.InequivalenceProgramsAssignmentsBoolean
