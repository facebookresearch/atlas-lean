/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED NUMBER OF TARDY JOBS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), WEIGHTED NUMBER OF TARDY
JOBS (1||sum w_j U_j).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedTardyJobs

/-!
# WEIGHTED NUMBER OF TARDY JOBS is NP-complete

Jobs with processing times, due dates, and weights, and a bound `K`. The question is whether
some ordering has weighted number of tardy jobs at most `K`: a job is tardy if it completes
after its due date, and contributes its weight when tardy, computed by a fold over the
ordering.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Weighted tardy jobs instances.** An instance of WEIGHTED NUMBER OF TARDY JOBS is a pair
consisting of a finite list of jobs, each a triple $(p, d, w)$ of natural numbers giving its
processing time $p$, due date $d$ and weight $w$, and a natural number $K$, the bound. -/
abbrev WeightedTardyJobsInstance := List (ℕ × ℕ × ℕ) × ℕ


/-- **One step of the weighted tardy jobs computation.** Let $J$ be a list of jobs, each a triple
$(p, d, w)$ of natural numbers (processing time, due date, weight). Given a state $(t, s)$ and a
natural number $j$, let $(p, d, w)$ be the job at position $j$ of $J$, counting from $0$, or
$(0, 0, 0)$ if $J$ has no position $j$, and let $t' = t + p$. The step returns $(t', s + w)$ if
$d < t'$, and $(t', s)$ otherwise. -/
def WeightedTardyStep (jobs : List (ℕ × ℕ × ℕ)) (state : ℕ × ℕ) (j : ℕ) : ℕ × ℕ :=
  let t := state.1 + (jobs.getD j (0, 0, 0)).1
  (t, state.2 + if (jobs.getD j (0, 0, 0)).2.1 < t then (jobs.getD j (0, 0, 0)).2.2 else 0)

/-- **Weighted number of tardy jobs of an ordering.** Let $J$ be a list of jobs, each a triple of
natural numbers (processing time, due date, weight), and write $(p_i, d_i, w_i)$ for the job at
position $i$ of $J$, counting from $0$, with $(p_i, d_i, w_i) = (0, 0, 0)$ when $J$ has no
position $i$. For a list $(j_1, \dots, j_m)$ of natural numbers, the weighted number of tardy
jobs of this order is the sum of $w_{j_k}$ over all $k$ with $d_{j_k} < C_k$, where
$C_k = p_{j_1} + \dots + p_{j_k}$ is the completion time of the $k$-th job. -/
def WeightedTardy (jobs : List (ℕ × ℕ × ℕ)) (order : List ℕ) : ℕ :=
  (order.foldl (WeightedTardyStep jobs) (0, 0)).2


/-- **Feasible weighted tardy jobs instances.** A weighted tardy jobs instance, consisting of a
list of $n$ jobs and a bound $K$, is feasible when there is an ordering of its jobs, that is, a
list of the job indices $0, 1, \dots, n - 1$ in which each index occurs exactly once, whose
weighted number of tardy jobs is at most $K$. -/
def WeightedTardyJobsFeasible
    (i : WeightedTardyJobsInstance) : Prop :=
  ∃ order : List ℕ, order.Perm (List.range i.1.length) ∧
    WeightedTardy i.1 order ≤ i.2

open Classical in
/-- **The weighted number of tardy jobs decision problem.** WEIGHTED NUMBER OF TARDY JOBS is the
decision problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding of weighted tardy jobs instances, to a feasible instance, that is, an instance
having an ordering of its jobs whose weighted number of tardy jobs is at most its bound. A
bitstring that decodes to no instance is rejected. -/
noncomputable def weightedTardyJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedTardyJobsInstance) x with
  | some i => decide (WeightedTardyJobsFeasible i)
  | none => false

/-- **WEIGHTED NUMBER OF TARDY JOBS is NP-complete.** The weighted number of tardy jobs decision
problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to
it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), WEIGHTED NUMBER OF TARDY JOBS (1||sum w_j U_j). -/
public theorem_wanted weightedTardyJobs_npComplete :
    weightedTardyJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedTardyJobsDec

end MetaMathlibExt.Complexity.NPComplete.WeightedTardyJobs
