/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR PRECEDENCE CONSTRAINED SCHEDULING (task lengths 1 and 2) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING (comment: the `m = 2` case becomes NP-complete if both task lengths 1 and 2 are
allowed);
J. D. Ullman, "NP-complete scheduling problems", Journal of Computer and System Sciences 10
(1975), 384-393, doi:10.1016/S0022-0000(75)80008-0.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Defs.Unbundled
public import WantedExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorPrecedenceSchedulingLengthsOneTwo

/-!
# TWO-PROCESSOR PRECEDENCE CONSTRAINED SCHEDULING (task lengths 1 and 2) is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) ∈ {1, 2}`, `m = 2` processors, a
partial order `<` on `T`, and a deadline `D ∈ ℤ⁺`. QUESTION: is there a `2`-processor schedule
`σ` for `T` that meets the overall deadline `D` and obeys the precedence constraints, i.e.,
such that `t < t'` implies `σ(t') ≥ σ(t) + l(t)`?

This is the variant of PRECEDENCE CONSTRAINED SCHEDULING
(`MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling`) in which the number of
processors is `2` and every task has length `1` or `2` (instead of length `1`). The instance
type, tasks, the precedence relation and the question (`PrecedenceConstrainedSchedulingFeasible`,
which uses each task's listed length `l(t)` both in the processor bound and in the precedence
constraints) are reused from that module unchanged; only the well-formedness condition differs.
An `m`-processor schedule meeting the overall deadline `D` (Garey and Johnson, [SS8]) is a
function `σ : T → ℤ₀⁺` such that, for all `u ≥ 0`, at most `m` tasks `t` have
`σ(t) ≤ u < σ(t) + l(t)`, and `σ(t) + l(t) ≤ D` for all `t ∈ T`. Binary encoding of all
numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: every task has length `1` or `2`, the number `m` of
processors is `2`, every listed pair names two tasks, the listed pairs form a strict partial
order, and `D` is positive. -/
def WellFormed (i : PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingInstance) :
    Prop :=
  (∀ l ∈ i.1, l = 1 ∨ l = 2) ∧ i.2.1 = 2 ∧
    (∀ p ∈ i.2.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧
    IsStrictOrder (PrecedenceConstrainedScheduling.Task i)
      (PrecedenceConstrainedScheduling.Prec i) ∧ 0 < i.2.2.2

open Classical in
/-- TWO-PROCESSOR PRECEDENCE CONSTRAINED SCHEDULING (task lengths 1 and 2) as a decision
problem over bitstrings. -/
noncomputable def twoProcessorPrecedenceSchedulingLengthsOneTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingInstance) x with
  | some i =>
    decide (WellFormed i ∧
      PrecedenceConstrainedScheduling.PrecedenceConstrainedSchedulingFeasible i)
  | none => false

/-- **TWO-PROCESSOR PRECEDENCE CONSTRAINED SCHEDULING (task lengths 1 and 2) is
NP-complete.** Source: Garey and Johnson (1979), [SS9]; Ullman (1975). -/
public theorem_wanted twoProcessorPrecedenceSchedulingLengthsOneTwo_npComplete :
    twoProcessorPrecedenceSchedulingLengthsOneTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorPrecedenceSchedulingLengthsOneTwoDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorPrecedenceSchedulingLengthsOneTwo
