/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR SCHEDULING with two processors: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiprocessorSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingTwoProcessors

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

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingTwoProcessors
