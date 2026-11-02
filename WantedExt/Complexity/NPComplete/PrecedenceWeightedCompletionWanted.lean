/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), 1|prec|sum w_j C_j; E. L.
Lawler, "Sequencing jobs to minimize total weighted completion time subject to precedence
constraints", Annals of Discrete Mathematics 2 (1978), 75-90; J. K. Lenstra and A. H. G.
Rinnooy Kan, "Complexity of scheduling under precedence constraints", Operations Research 26
(1978), 22-35.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceWeightedCompletion

/-!
# SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE is NP-complete

Jobs with processing times and weights, precedence constraints, and a bound `K`. The question
is whether some ordering respecting the precedence constraints has weighted sum of completion
times at most `K`, computed by a fold over the ordering.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of single-machine weighted completion with precedence.** An instance of the
scheduling problem $1 \mid \mathrm{prec} \mid \sum w_j C_j$ (one machine, precedence constraints,
objective the sum over jobs $j$ of the weight $w_j$ times the completion time $C_j$) is a triple
$(J, P, K)$: a list $J$ of jobs, each a pair $(p, w)$ of natural numbers giving its processing
time and weight; a list $P$ of pairs of natural numbers, read as precedence constraints between
job indices; and a natural number bound $K$. -/
abbrev PrecedenceWeightedCompletionInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ


/-- **One step of the weighted completion time computation.** Let $J$ be a list of jobs, each a
pair (processing time, weight), let $(t, s)$ be a state consisting of the elapsed time $t$ and the
accumulated weighted completion time $s$, and let $j$ be a job index. With $(p, w)$ the job at
position $j$ of $J$ counting from $0$, or $(0, 0)$ if $J$ has no such position, the step sends
$(t, s)$ to $(t + p, s + w (t + p))$. -/
def WeightedCompletionStep (jobs : List (ℕ × ℕ)) (state : ℕ × ℕ) (j : ℕ) : ℕ × ℕ :=
  let t := state.1 + (jobs.getD j (0, 0)).1
  (t, state.2 + (jobs.getD j (0, 0)).2 * t)

/-- **Total weighted completion time of a job order.** Let $J$ be a list of jobs, each a pair
$(p_i, w_i)$ of processing time and weight indexed from $0$, with $(p_i, w_i) = (0, 0)$ for $i$
outside the list. For a list $j_1, \dots, j_m$ of job indices, the total weighted completion time
is $\sum_{k=1}^{m} w_{j_k} C_k$, where $C_k = p_{j_1} + \dots + p_{j_k}$ is the completion time of
the $k$-th job in the order. -/
def WeightedCompletion (jobs : List (ℕ × ℕ)) (order : List ℕ) : ℕ :=
  (order.foldl (WeightedCompletionStep jobs) (0, 0)).2


/-- **Well-formed weighted completion instances.** An instance $(J, P, K)$ whose job list $J$ has
$n$ jobs is well formed when every precedence pair $(a, b)$ in $P$ satisfies $a < n$, $b < n$ and
$a \ne b$. -/
def WellFormed (i : PrecedenceWeightedCompletionInstance) : Prop :=
  ∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length ∧ p.1 ≠ p.2

/-- **Feasible weighted completion instances.** Let $(J, P, K)$ be an instance whose job list $J$
consists of $n$ jobs $(p_0, w_0), \dots, (p_{n-1}, w_{n-1})$ (processing time, weight). It is
feasible when there is an ordering $j_1, \dots, j_n$ of the indices $0, \dots, n-1$, each listed
exactly once, such that for every pair $(a, b)$ in $P$ the position of $a$ in the ordering is
smaller than the position of $b$, where an index that does not occur gets position $n + 1$, and
$\sum_{k=1}^{n} w_{j_k} (p_{j_1} + \dots + p_{j_k}) \le K$. -/
def PrecedenceWeightedCompletionFeasible
    (i : PrecedenceWeightedCompletionInstance) : Prop :=
  ∃ order : List ℕ, order.Perm (List.range i.1.length) ∧
    (∀ p ∈ i.2.1, order.idxOf p.1 < order.idxOf p.2) ∧
    WeightedCompletion i.1 order ≤ i.2.2

open Classical in
/-- **SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE as a decision problem.** The decision
problem accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding,
to an instance $(J, P, K)$ that is well formed and feasible: every precedence pair in $P$ consists
of two distinct job indices of $J$, and some ordering of all the jobs that puts the first job of
every precedence pair before the second has total weighted completion time at most $K$.
Bitstrings that do not decode to an instance are rejected. -/
noncomputable def precedenceWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceWeightedCompletionFeasible i)
  | none => false

/-- **SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE is NP-complete.** The decision problem
SINGLE-MACHINE WEIGHTED COMPLETION WITH PRECEDENCE on bitstrings belongs to NP, and every
decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey
and D. S. Johnson, *Computers and Intractability* (1979), 1|prec|sum w_j C_j; E. L.
Lawler, "Sequencing jobs to minimize total weighted completion time subject to precedence
constraints", Annals of Discrete Mathematics 2 (1978), 75-90; J. K. Lenstra and A. H. G.
Rinnooy Kan, "Complexity of scheduling under precedence constraints", Operations Research
26 (1978), 22-35. -/
public theorem_wanted precedenceWeightedCompletion_npComplete :
    precedenceWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceWeightedCompletion
