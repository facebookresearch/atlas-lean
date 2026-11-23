/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING (deadline 3) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING (comment: remains NP-complete for `D = 3`);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingDeadlineThree

/-!
# PRECEDENCE CONSTRAINED SCHEDULING (deadline 3) is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1`, a number `m ∈ ℤ⁺` of processors,
a partial order `<` on `T`, and the deadline `D = 3`. QUESTION: is there an `m`-processor
schedule `σ` for `T` that meets the overall deadline `D` and obeys the precedence constraints,
i.e., such that `t < t'` implies `σ(t') ≥ σ(t) + l(t) = σ(t) + 1`?

This is PRECEDENCE CONSTRAINED SCHEDULING
(`MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling`) restricted to
instances with deadline `D = 3`; the instance type, schedules and the question are reused from
that module unchanged. The number `m` of processors stays part of the input. Binary encoding
of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed PRECEDENCE CONSTRAINED SCHEDULING instance
whose deadline `D` is `3`. -/
def WellFormed (i : PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingInstance) :
    Prop :=
  PrecedenceConstrainedScheduling.WellFormed i ∧ i.2.2.2 = 3

open Classical in
/-- PRECEDENCE CONSTRAINED SCHEDULING (deadline 3) as a decision problem over bitstrings. -/
noncomputable def precedenceConstrainedSchedulingDeadlineThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingInstance) x with
  | some i =>
    decide (WellFormed i ∧
      PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingFeasible i)
  | none => false

/-- **PRECEDENCE CONSTRAINED SCHEDULING (deadline 3) is NP-complete.** Source: Garey and
Johnson (1979), [SS9]; Lenstra and Rinnooy Kan (1978). -/
public theorem_wanted precedenceConstrainedSchedulingDeadlineThree_npComplete :
    precedenceConstrainedSchedulingDeadlineThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceConstrainedSchedulingDeadlineThreeDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingDeadlineThree
