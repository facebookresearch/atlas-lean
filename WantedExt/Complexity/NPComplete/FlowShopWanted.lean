/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-MACHINE FLOW SHOP SCHEDULING is NP-complete

Source:
M. R. Garey, D. S. Johnson, and R. Sethi, "The complexity of flowshop and jobshop scheduling",
Mathematics of Operations Research 1 (1976), 117-129; T. F. Gonzalez and S. Sahni, "Flowshop
and jobshop schedules: complexity and approximation", Operations Research 26 (1978), 36-52.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FlowShop

/-!
# 3-MACHINE FLOW SHOP SCHEDULING is NP-complete

A list of jobs, each with three nonnegative integer processing times (on machines 1, 2, 3, in
that order), together with a deadline `D`. The question is whether there are start times, one
per job per machine, so that each job visits the machines in order, no machine processes two
jobs at once, and every job completes by `D`. This is the general (non-permutation) flow shop:
different machines may order the jobs differently.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Flow-shop instances.** A flow-shop instance is a pair consisting of a finite list of jobs,
each a finite list of natural numbers (its processing times on machines 1, 2 and 3, in that
order), and a natural number $D$, the deadline. The type does not force a job to have exactly
three entries; that is part of well-formedness. -/
abbrev FlowShopInstance := List (List ℕ) × ℕ

/-- **Well-formed flow-shop instances.** A flow-shop instance is well formed when every job in
it is a list of exactly three natural numbers. -/
def WellFormed (i : FlowShopInstance) : Prop :=
  ∀ job ∈ i.1, job.length = 3

/-- **Feasible flow-shop schedules.** Let an instance consist of jobs $1, \dots, n$, where job $j$
is a list of natural numbers whose $k$-th entry $p_{j,k}$ is its processing time on machine $k$
(read as $0$ if the list has fewer than $k$ entries), and a deadline $D$. The instance is
feasible when there are natural numbers $s_{j,k}$, for each job $j$ and each $k \in \{1, 2, 3\}$,
such that for every job $j$ we have $s_{j,1} + p_{j,1} \le s_{j,2}$,
$s_{j,2} + p_{j,2} \le s_{j,3}$ and $s_{j,3} + p_{j,3} \le D$, and for every machine
$k \in \{1, 2, 3\}$ and all jobs $a < b$ we have $s_{a,k} + p_{a,k} \le s_{b,k}$ or
$s_{b,k} + p_{b,k} \le s_{a,k}$.

Here $s_{j,k}$ is the start time of job $j$ on machine $k$: each job visits machines 1, 2, 3 in
that order, no machine processes two jobs at once, and every job finishes by $D$. -/
def FlowShopFeasible
    (i : FlowShopInstance) : Prop :=
  ∃ start : List (List ℕ), start.length = i.1.length ∧
    (∀ row ∈ start, row.length = 3) ∧
    (∀ j < i.1.length, (start.getD j []).getD 0 0 + (i.1.getD j []).getD 0 0 ≤
        (start.getD j []).getD 1 0 ∧
      (start.getD j []).getD 1 0 + (i.1.getD j []).getD 1 0 ≤
        (start.getD j []).getD 2 0 ∧
      (start.getD j []).getD 2 0 + (i.1.getD j []).getD 2 0 ≤ i.2) ∧
    ∀ k < 3, ∀ a < i.1.length, ∀ b < i.1.length, a < b →
      (start.getD a []).getD k 0 + (i.1.getD a []).getD k 0 ≤
          (start.getD b []).getD k 0 ∨
        (start.getD b []).getD k 0 + (i.1.getD b []).getD k 0 ≤
          (start.getD a []).getD k 0

open Classical in
/-- **The 3-machine flow shop scheduling decision problem.** The decision problem
3-MACHINE FLOW SHOP SCHEDULING accepts a bitstring $x$ exactly when $x$ decodes, under the
canonical bitstring encoding of flow-shop instances, to an instance that is well formed and
feasible. Bitstrings that do not decode to an instance are rejected. -/
noncomputable def flowShopDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FlowShopInstance) x with
  | some i => decide (WellFormed i ∧ FlowShopFeasible i)
  | none => false

/-- **3-MACHINE FLOW SHOP SCHEDULING is NP-complete.** The 3-machine flow shop scheduling
decision problem belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey, D. S. Johnson, and
R. Sethi, "The complexity of flowshop and jobshop scheduling", Mathematics of Operations
Research 1 (1976), 117-129; T. F. Gonzalez and S. Sahni, "Flowshop and jobshop schedules:
complexity and approximation", Operations Research 26 (1978), 36-52. -/
public theorem_wanted flowShop_npComplete :
    flowShopDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L flowShopDec

end MetaMathlibExt.Complexity.NPComplete.FlowShop
