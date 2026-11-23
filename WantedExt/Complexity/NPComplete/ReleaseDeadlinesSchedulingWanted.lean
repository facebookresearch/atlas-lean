/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE SCHEDULING WITH RELEASE TIMES AND DEADLINES is NP-complete

Source:
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362 (strong NP-hardness of
nonpreemptive 1|r_j|L_max; feasibility is L_max <= 0).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ReleaseDeadlinesScheduling

/-!
# SINGLE-MACHINE SCHEDULING WITH RELEASE TIMES AND DEADLINES is NP-complete

Jobs with processing times, release times, and deadlines, on a single nonpreemptive machine.
The question is whether there are start times with each job starting at or after its release,
completing by its deadline, and no two jobs overlapping.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of single-machine scheduling with release times and deadlines.** A
release-deadlines instance is a list of jobs $(p_0, r_0, d_0), \dots, (p_{n-1}, r_{n-1}, d_{n-1})$
of triples of natural numbers, where $p_j$ is the processing time, $r_j$ the release time and
$d_j$ the deadline of job $j$. -/
abbrev ReleaseDeadlinesSchedulingInstance := List (ℕ × ℕ × ℕ)

/-- **Feasible single-machine schedules with release times and deadlines.** A release-deadlines
instance with jobs $(p_j, r_j, d_j)$ for $j < n$ is feasible when there are start times
$s_0, \dots, s_{n-1} \in \mathbb{N}$ such that $r_j \le s_j$ and $s_j + p_j \le d_j$ for every
$j < n$, and for all $a < b < n$ either $s_a + p_a \le s_b$ or $s_b + p_b \le s_a$. -/
def ReleaseDeadlinesSchedulingFeasible
    (i : ReleaseDeadlinesSchedulingInstance) : Prop :=
  ∃ start : List ℕ, start.length = i.length ∧
    (∀ j < i.length, (i.getD j (0, 0, 0)).2.1 ≤ start.getD j 0 ∧
      start.getD j 0 + (i.getD j (0, 0, 0)).1 ≤ (i.getD j (0, 0, 0)).2.2) ∧
    ∀ a < i.length, ∀ b < i.length, a < b →
      start.getD a 0 + (i.getD a (0, 0, 0)).1 ≤ start.getD b 0 ∨
      start.getD b 0 + (i.getD b (0, 0, 0)).1 ≤ start.getD a 0

open Classical in
/-- **Single-machine scheduling with release times and deadlines as a decision problem.**
SINGLE-MACHINE SCHEDULING WITH RELEASE TIMES AND DEADLINES is the decision problem that accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of
release-deadlines instances, to a feasible instance. Bitstrings that do not decode to an instance
are rejected. -/
noncomputable def releaseDeadlinesSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ReleaseDeadlinesSchedulingInstance) x with
  | some i => decide (ReleaseDeadlinesSchedulingFeasible i)
  | none => false

/-- **SINGLE-MACHINE SCHEDULING WITH RELEASE TIMES AND DEADLINES is NP-complete.** The
decision problem SINGLE-MACHINE SCHEDULING WITH RELEASE TIMES AND DEADLINES belongs to NP, and
every decision problem in NP has a polynomial-time many-one reduction to it.

Source: J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362 (strong NP-hardness of
nonpreemptive 1|r_j|L_max; feasibility is L_max <= 0). -/
public theorem_wanted releaseDeadlinesScheduling_npComplete :
    releaseDeadlinesSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L releaseDeadlinesSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.ReleaseDeadlinesScheduling
