/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL TARDINESS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), TOTAL TARDINESS (1||sum
T_j); J. Du and J. Y.-T. Leung, "Minimizing total tardiness on one machine is NP-hard" (1990).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalTardiness

/-!
# TOTAL TARDINESS is NP-complete

Jobs with processing times and due dates, and a bound `K`. The question is whether some
ordering has total tardiness at most `K`, where a job's tardiness is the excess of its
completion time over its due date (zero if on time), computed by a fold over the ordering.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of TOTAL TARDINESS.** An instance of TOTAL TARDINESS is a pair $(J, K)$ consisting
of a finite list $J = ((p_0, d_0), \dots, (p_{n-1}, d_{n-1}))$ of jobs, where job $j$ has
processing time $p_j \in \mathbb{N}$ and due date $d_j \in \mathbb{N}$, and a bound
$K \in \mathbb{N}$. -/
abbrev TotalTardinessInstance := List (ℕ × ℕ) × ℕ


/-- **One step of the tardiness computation.** Let $J = ((p_0, d_0), \dots, (p_{n-1}, d_{n-1}))$
be a list of jobs with processing times $p_i \in \mathbb{N}$ and due dates $d_i \in \mathbb{N}$,
let $j \in \mathbb{N}$, and let $(p, d) = (p_j, d_j)$ if $j < n$ and $(p, d) = (0, 0)$ otherwise.
Running job $j$ from the state $(t, s) \in \mathbb{N} \times \mathbb{N}$, where $t$ is the elapsed
time and $s$ the accumulated tardiness, gives the state $(t + p, \, s + \max(t + p - d, 0))$. -/
def TardinessStep (jobs : List (ℕ × ℕ)) (state : ℕ × ℕ) (j : ℕ) : ℕ × ℕ :=
  let t := state.1 + (jobs.getD j (0, 0)).1
  (t, state.2 + (t - (jobs.getD j (0, 0)).2))

/-- **Total tardiness of a job order.** Let $J = ((p_0, d_0), \dots, (p_{n-1}, d_{n-1}))$ be a
list of jobs with processing times $p_i \in \mathbb{N}$ and due dates $d_i \in \mathbb{N}$, and
set $(p_i, d_i) = (0, 0)$ for $i \ge n$. For a list $(j_1, \dots, j_m)$ of natural numbers (job
indices), let $C_k = p_{j_1} + \dots + p_{j_k}$ be the completion time of the $k$-th job when the
jobs are run in this order. The total tardiness of the order is
$\sum_{k=1}^{m} \max(C_k - d_{j_k}, 0)$. -/
def TotalTardinessValue (jobs : List (ℕ × ℕ)) (order : List ℕ) : ℕ :=
  (order.foldl (TardinessStep jobs) (0, 0)).2


/-- **Feasible TOTAL TARDINESS instances.** An instance $(J, K)$ of TOTAL TARDINESS with $n$ jobs
is feasible when some ordering of its jobs, that is, some permutation $(j_1, \dots, j_n)$ of
$(0, 1, \dots, n - 1)$, has total tardiness at most $K$. -/
def TotalTardinessFeasible
    (i : TotalTardinessInstance) : Prop :=
  ∃ order : List ℕ, order.Perm (List.range i.1.length) ∧
    TotalTardinessValue i.1 order ≤ i.2

open Classical in
/-- **The TOTAL TARDINESS decision problem.** The decision problem TOTAL TARDINESS accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding (natural numbers in
binary), to an instance of TOTAL TARDINESS that is feasible, that is, whose jobs admit an ordering
of total tardiness at most its bound. It rejects every bitstring that does not decode to an
instance. -/
noncomputable def totalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TotalTardinessInstance) x with
  | some i => decide (TotalTardinessFeasible i)
  | none => false

/-- **TOTAL TARDINESS is NP-complete.** The TOTAL TARDINESS decision problem belongs to NP, and
every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), TOTAL TARDINESS (1||sum T_j); J. Du and J. Y.-T. Leung,
"Minimizing total tardiness on one machine is NP-hard" (1990). -/
public theorem_wanted totalTardiness_npComplete :
    totalTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalTardinessDec

end MetaMathlibExt.Complexity.NPComplete.TotalTardiness
