/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS8] MULTIPROCESSOR SCHEDULING
(transformation from PARTITION, Section 3.2.1);
M. R. Garey and D. S. Johnson, ""Strong" NP-completeness results: motivation, examples, and
implications", Journal of the ACM 25 (1978), 499-508, doi:10.1145/322077.322090;
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X, Theorem 3(a).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorScheduling

/-!
# MULTIPROCESSOR SCHEDULING is NP-complete

INSTANCE: a set `T` of tasks, a number `m ∈ ℤ⁺` of processors, a length `l(t) ∈ ℤ⁺` for each
`t ∈ T`, and a deadline `D ∈ ℤ⁺`. QUESTION: is there an `m`-processor schedule for `T` that
meets the overall deadline `D`, i.e., a function `σ : T → ℤ₀⁺` such that, for all `u ≥ 0`, the
number of tasks `t ∈ T` for which `σ(t) ≤ u < σ(t) + l(t)` is no more than `m` and such that,
for all `t ∈ T`, `σ(t) + l(t) ≤ D`?

The tasks are `Fin n`, one per listed length. Binary encoding of all numbers (the problem is
NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the task lengths `l(t)` (task `t` is the `t`-th entry), the number `m` of
processors, and the deadline `D`. -/
abbrev MultiprocessorSchedulingInstance := List ℕ × ℕ × ℕ

/-- The tasks of the instance, `Fin n` for `n` listed lengths. -/
abbrev Task (i : MultiprocessorSchedulingInstance) : Type := Fin i.1.length

/-- The length `l(t)` of task `t`. -/
def taskLength (i : MultiprocessorSchedulingInstance) (t : Task i) : ℕ :=
  i.1.get t

/-- The tasks running at time `u` under `σ`: those with `σ(t) ≤ u < σ(t) + l(t)`. -/
def running (i : MultiprocessorSchedulingInstance) (σ : Task i → ℕ) (u : ℕ) :
    Finset (Task i) :=
  Finset.univ.filter fun t => σ t ≤ u ∧ u < σ t + taskLength i t

/-- Well-formedness of an instance: every task length is positive, and `m` and `D` are
positive. -/
def WellFormed (i : MultiprocessorSchedulingInstance) : Prop :=
  (∀ l ∈ i.1, 0 < l) ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- Some `m`-processor schedule meets the overall deadline: at every time `u` at most `m`
tasks run, and every task ends by `D`. -/
def MultiprocessorSchedulingFeasible (i : MultiprocessorSchedulingInstance) : Prop :=
  ∃ σ : Task i → ℕ, (∀ u, (running i σ u).card ≤ i.2.1) ∧
    ∀ t, σ t + taskLength i t ≤ i.2.2

open Classical in
/-- MULTIPROCESSOR SCHEDULING as a decision problem over bitstrings. -/
noncomputable def multiprocessorSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorSchedulingFeasible i)
  | none => false

/-- **MULTIPROCESSOR SCHEDULING is NP-complete.** Source: Garey and Johnson (1979), [SS8];
Garey and Johnson (1978); Lenstra, Rinnooy Kan, and Brucker (1977), Theorem 3(a). -/
public theorem_wanted multiprocessorScheduling_npComplete :
    multiprocessorSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorScheduling
