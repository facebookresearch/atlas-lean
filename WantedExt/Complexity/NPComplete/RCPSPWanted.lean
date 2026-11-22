/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE-CONSTRAINED PROJECT SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BIN PACKING; J.
Blazewicz, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Scheduling subject to resource
constraints: classification and complexity", Discrete Applied Mathematics 5 (1983), 11-24
(classification).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RCPSP

/-!
# RESOURCE-CONSTRAINED PROJECT SCHEDULING is NP-complete

Jobs with durations and resource demands, precedence constraints, a single renewable resource
capacity, and a deadline `D`. The question is whether there are start times meeting all
precedence constraints and the deadline, with the total resource demand of simultaneously
active jobs never exceeding the capacity (checked by forbidding an active subset of demand
exceeding capacity at each time). NP-hardness follows from bin packing: items become unit-
duration jobs with demand equal to item size, no precedence, resource capacity equal to bin
capacity, and makespan bound equal to the number of bins.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of resource-constrained project scheduling.** An instance of
resource-constrained project scheduling (an RCPSP instance) is a quadruple $(J, P, C, D)$: a list
$J$ of jobs, each a pair $(p, r) \in \mathbb{N} \times \mathbb{N}$ of a duration $p$ and a
resource demand $r$; a list $P$ of precedence pairs $(a, b) \in \mathbb{N} \times \mathbb{N}$ of
job indices; a resource capacity $C \in \mathbb{N}$; and a deadline $D \in \mathbb{N}$. -/
abbrev RCPSPInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ × ℕ

/-- **Well-formed RCPSP instances.** An RCPSP instance $(J, P, C, D)$ whose job list $J$ has
$n$ jobs is well formed when every precedence pair $(a, b) \in P$ satisfies $a < n$, $b < n$ and
$a \ne b$, and there is a listing of $0, 1, \dots, n-1$, each exactly once, in which $a$ comes
before $b$ for every $(a, b) \in P$. -/
def WellFormed (i : RCPSPInstance) : Prop :=
  ∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length ∧ p.1 ≠ p.2 ∧
    ∃ ord : List ℕ, ord.Perm (List.range i.1.length) ∧
      ∀ p ∈ i.2.1, ord.idxOf p.1 < ord.idxOf p.2

/-- **Feasible RCPSP instances.** Let $(J, P, C, D)$ be an RCPSP instance with $n$ jobs, where
job $j < n$ has duration $p_j$ and resource demand $r_j$, and set $p_j = 0$ for $j \ge n$. The
instance is feasible when there are start times $s_0, \dots, s_{n-1} \in \mathbb{N}$, with
$s_j = 0$ for $j \ge n$, such that every job finishes by the deadline ($s_j + p_j \le D$ for all
$j < n$), every precedence pair $(a, b) \in P$ satisfies $s_a + p_a \le s_b$, and at every time
$t < D$ the total demand of the jobs active at $t$ (the jobs $j < n$ with
$s_j \le t < s_j + p_j$) is at most $C$. -/
def RCPSPFeasible
    (i : RCPSPInstance) : Prop :=
  ∃ start : List ℕ, start.length = i.1.length ∧
    (∀ j < i.1.length, start.getD j 0 + (i.1.getD j (0, 0)).1 ≤ i.2.2.2) ∧
    (∀ p ∈ i.2.1, start.getD p.1 0 + (i.1.getD p.1 0).1 ≤ start.getD p.2 0) ∧
    ∀ t < i.2.2.2, ¬ ∃ active : List ℕ, active.Nodup ∧
      (∀ j ∈ active, j < i.1.length ∧ start.getD j 0 ≤ t ∧
        t < start.getD j 0 + (i.1.getD j (0, 0)).1) ∧
      i.2.2.1 < (active.map (fun j => (i.1.getD j (0, 0)).2)).sum

open Classical in
/-- **Resource-constrained project scheduling as a decision problem.** RESOURCE-CONSTRAINED
PROJECT SCHEDULING is the decision problem that accepts a bitstring $x$ exactly when $x$ decodes,
under the canonical bitstring encoding of RCPSP instances, to an RCPSP instance that is well
formed and feasible. Bitstrings that do not decode to an instance are rejected. -/
noncomputable def rcpspDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RCPSPInstance) x with
  | some i => decide (WellFormed i ∧ RCPSPFeasible i)
  | none => false

/-- **RESOURCE-CONSTRAINED PROJECT SCHEDULING is NP-complete.** The decision problem
RESOURCE-CONSTRAINED PROJECT SCHEDULING belongs to NP, and every decision problem in NP has a
polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BIN PACKING; J.
Blazewicz, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Scheduling subject to resource constraints:
classification and complexity", Discrete Applied Mathematics 5 (1983), 11-24 (classification). -/
public theorem_wanted rcpsp_npComplete :
    rcpspDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rcpspDec

end MetaMathlibExt.Complexity.NPComplete.RCPSP
