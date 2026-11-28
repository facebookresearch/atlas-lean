/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR SCHEDULING WITH RELEASE DATES on a fixed number `m ≥ 2` of processors
(`Pm|r_i|Cmax`): definitions

Source:
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X (Theorem 3(a) for `m = 2`, Theorem 1(c) for `m ≥ 2`);
E. L. Lawler, J. K. Lenstra, A. H. G. Rinnooy Kan and D. B. Shmoys, "Sequencing and
scheduling: algorithms and complexity", in *Logistics of Production and Inventory*, Handbooks in
Operations Research and Management Science 4, North-Holland (1993), 445-522,
doi:10.1016/S0927-0507(05)80189-6;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück
(`Pm|r_i|C_max`, maximal pseudo-polynomially solvable, citing Lawler et al.).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiprocessorSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParallelFixedMachinesReleaseDatesMakespan

open MultiprocessorScheduling (MultiprocessorSchedulingInstance Task taskLength running)

/-- An instance: a MULTIPROCESSOR SCHEDULING instance (the task lengths, the number `m` of
processors, the deadline `D`) and the release dates, task `t` having the `t`-th listed release
date `r(t)`. -/
abbrev ParallelFixedMachinesReleaseDatesMakespanInstance :=
  MultiprocessorSchedulingInstance × List ℕ

/-- The release date `r(t)` of task `t`. -/
def releaseDate (i : ParallelFixedMachinesReleaseDatesMakespanInstance) (t : Task i.1) : ℕ :=
  i.2.getD t 0

/-- Well-formedness of an instance for the fixed number `m` of processors: it is a well-formed
MULTIPROCESSOR SCHEDULING instance (positive lengths, `m` and `D`) with exactly `m` processors,
and there is one release date per task. -/
def WellFormed (m : ℕ) (i : ParallelFixedMachinesReleaseDatesMakespanInstance) : Prop :=
  MultiprocessorScheduling.WellFormed i.1 ∧ i.1.2.1 = m ∧ i.2.length = i.1.1.length

/-- Some `m`-processor schedule (at every time `u` at most `m` tasks run) starts every task no
earlier than its release date and completes every task by `D`. -/
def ParallelFixedMachinesReleaseDatesMakespanFeasible
    (i : ParallelFixedMachinesReleaseDatesMakespanInstance) : Prop :=
  ∃ σ : Task i.1 → ℕ, (∀ u, (running i.1 σ u).card ≤ i.1.2.1) ∧
    (∀ t, releaseDate i t ≤ σ t) ∧ ∀ t, σ t + taskLength i.1 t ≤ i.1.2.2

open Classical in
/-- `Pm|r_i|Cmax` for the fixed number `m` of processors, as a decision problem over
bitstrings. -/
noncomputable def parallelFixedMachinesReleaseDatesMakespanDec (m : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ParallelFixedMachinesReleaseDatesMakespanInstance) x with
  | some i => decide (WellFormed m i ∧ ParallelFixedMachinesReleaseDatesMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ParallelFixedMachinesReleaseDatesMakespan
