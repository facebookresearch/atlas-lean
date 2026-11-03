/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL MACHINES WITH DEADLINES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PARALLEL MACHINE
SCHEDULING WITH DEADLINES.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParallelMachinesDeadlines

/-!
# PARALLEL MACHINES WITH DEADLINES is NP-complete

Jobs with processing times and deadlines, and a number `m` of identical parallel machines. The
question is whether there are start times and machine assignments so that every job completes
by its deadline and no machine runs two jobs at once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Parallel machine scheduling instances.** An instance of parallel machine scheduling with
deadlines is a pair consisting of a finite list of jobs, each a pair $(p, d)$ of natural numbers
giving its processing time $p$ and deadline $d$, and a natural number $m$, the number of
machines. -/
abbrev ParallelMachinesDeadlinesInstance := List (ℕ × ℕ) × ℕ

/-- **Feasible schedules on parallel machines with deadlines.** An instance consisting of jobs
$(p_1, d_1), \dots, (p_k, d_k)$, where job $j$ has processing time $p_j$ and deadline $d_j$, and
a number $m$ of machines is feasible when there are start times $s_1, \dots, s_k \in \mathbb{N}$
and machines $\mu_1, \dots, \mu_k \in \{0, \dots, m - 1\}$ such that $s_j + p_j \le d_j$ for
every $j$, and for all $a \ne b$ with $\mu_a = \mu_b$, either $s_a + p_a \le s_b$ or
$s_b + p_b \le s_a$. -/
def ParallelMachinesDeadlinesFeasible
    (i : ParallelMachinesDeadlinesInstance) : Prop :=
  ∃ start : List ℕ, start.length = i.1.length ∧
    ∃ machine : List ℕ, machine.length = i.1.length ∧
      (∀ j < i.1.length, machine.getD j 0 < i.2) ∧
      (∀ j < i.1.length, start.getD j 0 + (i.1.getD j (0, 0)).1 ≤ (i.1.getD j (0, 0)).2) ∧
      ∀ a < i.1.length, ∀ b < i.1.length, a < b → machine.getD a 0 = machine.getD b 0 →
        start.getD a 0 + (i.1.getD a (0, 0)).1 ≤ start.getD b 0 ∨
        start.getD b 0 + (i.1.getD b (0, 0)).1 ≤ start.getD a 0

open Classical in
/-- **The PARALLEL MACHINES WITH DEADLINES decision problem.** This decision problem accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to jobs
$(p_1, d_1), \dots, (p_k, d_k)$ of natural numbers (processing times and deadlines) and a number
$m$ of machines for which there are start times $s_1, \dots, s_k \in \mathbb{N}$ and machines
$\mu_1, \dots, \mu_k \in \{0, \dots, m - 1\}$ such that $s_j + p_j \le d_j$ for every $j$, and
for all $a \ne b$ with $\mu_a = \mu_b$, either $s_a + p_a \le s_b$ or $s_b + p_b \le s_a$. It
rejects every bitstring that does not decode. -/
noncomputable def parallelMachinesDeadlinesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ParallelMachinesDeadlinesInstance) x with
  | some i => decide (ParallelMachinesDeadlinesFeasible i)
  | none => false

/-- **PARALLEL MACHINES WITH DEADLINES is NP-complete.** The PARALLEL MACHINES WITH DEADLINES
decision problem belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), PARALLEL MACHINE SCHEDULING WITH
DEADLINES. -/
public theorem_wanted parallelMachinesDeadlines_npComplete :
    parallelMachinesDeadlinesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L parallelMachinesDeadlinesDec

end MetaMathlibExt.Complexity.NPComplete.ParallelMachinesDeadlines
