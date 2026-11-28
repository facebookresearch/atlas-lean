/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR SCHEDULING WITH RELEASE DATES on a fixed number `m ≥ 2` of processors
(`Pm|r_i|Cmax`) is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiprocessorSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParallelFixedMachinesReleaseDatesMakespan

open MultiprocessorScheduling (MultiprocessorSchedulingInstance Task taskLength running)

/-!
# MULTIPROCESSOR SCHEDULING WITH RELEASE DATES on `m` processors, `m ≥ 2` fixed, is NP-complete

For a fixed number `m ≥ 2` of identical processors: INSTANCE: a set `T` of tasks, for each task
`t ∈ T` a length `l(t) ∈ ℤ⁺` and a release date `r(t) ∈ ℤ₀⁺`, and a deadline `D ∈ ℤ⁺`.
QUESTION: is there an `m`-processor schedule `σ : T → ℤ₀⁺` (for all `u ≥ 0`, at most `m` tasks
`t` have `σ(t) ≤ u < σ(t) + l(t)`) with `r(t) ≤ σ(t)` and `σ(t) + l(t) ≤ D` for all `t ∈ T`,
that is, with makespan at most `D`?

This is `Pm|r_i|C_max` in the Brucker-Knust classification, one decision problem for each fixed
`m`. The tasks, processors and schedule conditions are those of MULTIPROCESSOR SCHEDULING
(`MultiprocessorSchedulingWanted`, Garey and Johnson [SS8]): an instance is a MULTIPROCESSOR
SCHEDULING instance (the task lengths, task `t` being the `t`-th entry, so tasks are listed one
per entry; the number `m` of processors; the deadline `D`) whose well-formedness (positive
lengths, `m` and `D`) is kept, together with the release dates, one per task, the `t`-th listed
release date being `r(t)`; `WellFormed` adds that the number of processors is the fixed `m` and
that there is one release date per task. An `m`-processor schedule in this sense is one with an
assignment of the tasks to `m` processors, each processing one task at a time (the interval
graph of the tasks has chromatic number equal to its largest clique). With all release dates `0`
the problem is `Pm||C_max`; Lenstra, Rinnooy Kan and Brucker reduce PARTITION to `P2||C_max`
(Theorem 3(a)), and their Theorem 1(c) reduces a problem on `m'` machines to the same problem on
`m ≥ m'` machines. Membership in NP is the certificate argument: start times below `D`. Binary
encoding of all numbers: for fixed `m` the problem is solvable in pseudo-polynomial time, so it
is NP-complete only in the ordinary sense.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: a MULTIPROCESSOR SCHEDULING instance (the task lengths, the number `m` of
processors, the deadline `D`) and the release dates, task `t` having the `t`-th listed release
date `r(t)`. -/
abbrev ParallelFixedMachinesReleaseDatesMakespanInstance :=
  MultiprocessorSchedulingInstance × List ℕ

/-- The release date `r(t)` of task `t`: entry `t` of the list of release dates, read as `0` when
the list has no entry `t`. -/
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

/-- **MULTIPROCESSOR SCHEDULING WITH RELEASE DATES is NP-complete for every fixed number `m ≥ 2`
of processors (`Pm|r_i|Cmax`).** Source: Lenstra, Rinnooy Kan and Brucker (1977), Theorems 3(a)
and 1(c), as recorded in the Brucker-Knust classification. -/
public theorem_wanted parallelFixedMachinesReleaseDatesMakespan_npComplete (m : ℕ)
    (hm : 2 ≤ m) :
    parallelFixedMachinesReleaseDatesMakespanDec m ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (parallelFixedMachinesReleaseDatesMakespanDec m)

end MetaMathlibExt.Complexity.NPComplete.ParallelFixedMachinesReleaseDatesMakespan
