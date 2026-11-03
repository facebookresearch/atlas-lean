/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE-CONSTRAINED MULTIPROCESSOR SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PRECEDENCE-CONSTRAINED
MULTIPROCESSOR SCHEDULING; J. D. Ullman, "NP-complete scheduling problems" (1975).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceMultiprocessorScheduling

/-!
# PRECEDENCE-CONSTRAINED MULTIPROCESSOR SCHEDULING is NP-complete

Jobs with processing times and precedence constraints, `m` identical machines, and a deadline
`D`. The question is whether there are start times and a machine assignment meeting all
precedence constraints and the deadline, with no machine running two jobs at once (same-machine
non-overlap).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of precedence-constrained multiprocessor scheduling.** An instance is a tuple
$(d, P, m, D)$ in which $d = (d_0, \dots, d_{n-1})$ is a list of natural numbers, $d_j$ being the
duration of job $j$; $P$ is a list of pairs $(a, b)$ of natural numbers, each read as the
precedence constraint that job $a$ precedes job $b$; $m$ is a natural number, the number of
machines; and $D$ is a natural number, the deadline. -/
abbrev PrecedenceMultiprocessorSchedulingInstance := List ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- **Well-formed precedence-multiprocessor scheduling instances.** An instance $(d, P, m, D)$
whose list of job durations $d$ has length $n$ is well formed when every precedence pair
$(a, b) \in P$ satisfies $a < n$, $b < n$ and $a \ne b$, and there is an ordering of the jobs
$0, \dots, n-1$ (a permutation of this list) in which $a$ comes before $b$ for every
$(a, b) \in P$. -/
def WellFormed (i : PrecedenceMultiprocessorSchedulingInstance) : Prop :=
  ∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length ∧ p.1 ≠ p.2 ∧
    ∃ ord : List ℕ, ord.Perm (List.range i.1.length) ∧
      ∀ p ∈ i.2.1, ord.idxOf p.1 < ord.idxOf p.2

/-- **Feasible precedence-multiprocessor scheduling instances.** An instance $(d, P, m, D)$ with
job durations $d = (d_0, \dots, d_{n-1})$ is feasible when there are start times
$s_0, \dots, s_{n-1} \in \mathbb{N}$ and machines $\mu_0, \dots, \mu_{n-1} \in \mathbb{N}$ such
that $\mu_j < m$ and $s_j + d_j \le D$ for every $j < n$, $s_a + d_a \le s_b$ for every
precedence pair $(a, b) \in P$, and for all jobs $a < b < n$ with $\mu_a = \mu_b$, either
$s_a + d_a \le s_b$ or $s_b + d_b \le s_a$. Here $s_j$ and $d_j$ are read as $0$ when
$j \ge n$. -/
def PrecedenceMultiprocessorSchedulingFeasible
    (i : PrecedenceMultiprocessorSchedulingInstance) : Prop :=
  ∃ start : List ℕ, start.length = i.1.length ∧
    ∃ machine : List ℕ, machine.length = i.1.length ∧
      (∀ j < i.1.length, machine.getD j 0 < i.2.2.1) ∧
      (∀ j < i.1.length, start.getD j 0 + i.1.getD j 0 ≤ i.2.2.2) ∧
      (∀ p ∈ i.2.1, start.getD p.1 0 + i.1.getD p.1 0 ≤ start.getD p.2 0) ∧
      ∀ a < i.1.length, ∀ b < i.1.length, a < b → machine.getD a 0 = machine.getD b 0 →
        start.getD a 0 + i.1.getD a 0 ≤ start.getD b 0 ∨
        start.getD b 0 + i.1.getD b 0 ≤ start.getD a 0

open Classical in
/-- **The precedence-constrained multiprocessor scheduling decision problem.** The decision
problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to a precedence-multiprocessor scheduling instance that is well formed and feasible.
Bitstrings that do not decode to an instance are rejected. -/
noncomputable def precedenceMultiprocessorSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceMultiprocessorSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceMultiprocessorSchedulingFeasible i)
  | none => false

/-- **PRECEDENCE-CONSTRAINED MULTIPROCESSOR SCHEDULING is NP-complete.** The
precedence-constrained multiprocessor scheduling decision problem is in NP, and every decision
problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey
and D. S. Johnson, *Computers and Intractability* (1979), PRECEDENCE-CONSTRAINED
MULTIPROCESSOR SCHEDULING; J. D. Ullman, "NP-complete scheduling problems" (1975). -/
public theorem_wanted precedenceMultiprocessorScheduling_npComplete :
    precedenceMultiprocessorSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceMultiprocessorSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceMultiprocessorScheduling
