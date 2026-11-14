/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR SCHEDULING with two processors is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS8] MULTIPROCESSOR SCHEDULING
(comment: remains NP-complete for `m = 2`) and Section 3.2.1, p. 65 (proof by restriction to
PARTITION, allowing only instances with `m = 2`);
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X, Theorem 3(a) (PARTITION reduces to `P2 || Cmax`);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (PARTITION).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiprocessorSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingTwoProcessors

/-!
# MULTIPROCESSOR SCHEDULING with two processors is NP-complete

The restriction of MULTIPROCESSOR SCHEDULING to instances with `m = 2` processors: given tasks
with lengths `l(t) ∈ ℤ⁺` and a deadline `D ∈ ℤ⁺`, is there a `2`-processor schedule
`σ : T → ℤ₀⁺` (for all `u ≥ 0`, at most `2` tasks `t` have `σ(t) ≤ u < σ(t) + l(t)`) with
`σ(t) + l(t) ≤ D` for all `t ∈ T`? The instance type, the base well-formedness and the question
are those of `MultiprocessorSchedulingWanted`, reused unchanged; this module adds only `m = 2`
to `WellFormed`.

Binary encoding of all numbers: for fixed `m` the problem is solvable in pseudo-polynomial
time, so it is NP-complete only in the ordinary sense.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance, as in `MultiprocessorSchedulingWanted`: the task lengths `l(t)`, the number `m`
of processors, and the deadline `D`. -/
abbrev MultiprocessorSchedulingTwoProcessorsInstance :=
  MultiprocessorScheduling.MultiprocessorSchedulingInstance

/-- Well-formedness of an instance: the MULTIPROCESSOR SCHEDULING instance is well-formed and
the number of processors is `m = 2`. -/
def WellFormed (i : MultiprocessorSchedulingTwoProcessorsInstance) : Prop :=
  MultiprocessorScheduling.WellFormed i ∧ i.2.1 = 2

/-- Some `m`-processor schedule meets the overall deadline, exactly as in
`MultiprocessorSchedulingWanted`. -/
def MultiprocessorSchedulingTwoProcessorsFeasible
    (i : MultiprocessorSchedulingTwoProcessorsInstance) : Prop :=
  MultiprocessorScheduling.MultiprocessorSchedulingFeasible i

open Classical in
/-- MULTIPROCESSOR SCHEDULING with two processors as a decision problem over bitstrings. -/
noncomputable def multiprocessorSchedulingTwoProcessorsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorSchedulingTwoProcessorsInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorSchedulingTwoProcessorsFeasible i)
  | none => false

/-- **MULTIPROCESSOR SCHEDULING with two processors is NP-complete.** Source: Garey and Johnson
(1979), [SS8] and Section 3.2.1; Lenstra, Rinnooy Kan, and Brucker (1977), Theorem 3(a);
Karp (1972). -/
public theorem_wanted multiprocessorSchedulingTwoProcessors_npComplete :
    multiprocessorSchedulingTwoProcessorsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorSchedulingTwoProcessorsDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingTwoProcessors
