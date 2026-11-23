/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM FLOW SHOP, OUT-TREE, MAXIMUM LATENESS (FMPM|outtree; p_ij = 1|L_max) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007): Sections 1.2, 1.3, 1.5 and 5.2
(due dates, precedence relations, lateness, out-trees), Chapter 10 (the MPM flow-shop model) and
Table 5.3 (`P|p_i = 1; outtree|L_max` is NP-hard, Brucker, Garey and Johnson);
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `FMPM|outtree; p_ij = 1|L_max` as strongly NP-hard with the attribution
to Brucker, Garey and Johnson (1977).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopOutTreeLateness

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed Prec PrecedenceWellFormed
  IsPrecedenceSchedule completionTime)

/-!
# MPM FLOW SHOP, OUT-TREE, MAXIMUM LATENESS (FMPM|outtree; p_ij = 1|L_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an MPM flow shop with `r ≥ 1` stages and machine sets
`μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij = 1` and with a due date `d_i ∈ ℤ`; a
precedence relation `→` on the jobs that is an out-tree (each job has at most one immediate
predecessor); and a bound `K ∈ ℤ`. QUESTION: is there a feasible schedule in which the maximum
lateness `max_i (C_i - d_i)` is at most `K`?

The MPM flow-shop model, its schedules and precedence constraints are those of
`FMPM|prec; p_ij = 1|C_max`
(`WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted`, which states
Brucker's model: `StagesWellFormed`, `Prec`, `PrecedenceWellFormed`, `IsPrecedenceSchedule`,
`completionTime`, reused here). Out-trees follow Brucker (Section 5.2): "intrees (outtrees) which
are precedence constraints with the property that each `IS(i)` (`IP(i)`) contains at the most
one job", where `IP(i)` is the set of immediate predecessors of `i`. The precedence relation is
given by the list of its pairs, required to be a strict partial order; `j` is an immediate
predecessor of `k` when `j → k` and no job `c` has `j → c → k`. The lateness of job `i` is
`C_i - d_i` (Brucker, Section 1.5: "`L_i := C_i − d_i` lateness"; `L_max` is the maximum
lateness). The due dates and the bound are integers, each encoded as a pair of naturals
`(positive part, negative part)` as in `ZeroOneILPWanted`; `L_max ≤ K` is stated as
`C_i - d_i ≤ K` for every job `i`; `WellFormed` requires `n ≥ 1`, since a maximum over no jobs
is undefined. The jobs are `Fin n` for `n` listed due dates. Binary encoding of all numbers (the
problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of machines `m`, the stage machine sets `[μ_1, …, μ_r]`, the due
dates `[d_1, …, d_n]` (one per job) as `(positive part, negative part)` pairs, the pairs
`(i, k)` with `i → k`, and the bound `K` as a `(positive part, negative part)` pair. -/
abbrev MultipurposeFlowShopOutTreeLatenessInstance :=
  ℕ × List (List ℕ) × List (ℕ × ℕ) × List (ℕ × ℕ) × (ℕ × ℕ)

/-- The jobs of the instance, `Fin n` for `n` due dates. -/
abbrev Job (i : MultipurposeFlowShopOutTreeLatenessInstance) : Type := Fin i.2.2.1.length

/-- The stages of the instance, `Fin r` for `r` machine sets. -/
abbrev Stage (i : MultipurposeFlowShopOutTreeLatenessInstance) : Type := Fin i.2.1.length

/-- The due date `d_j ∈ ℤ` of job `j`. -/
def dueDate (i : MultipurposeFlowShopOutTreeLatenessInstance) (j : Job i) : ℤ :=
  ((i.2.2.1.get j).1 : ℤ) - ((i.2.2.1.get j).2 : ℤ)

/-- The bound `K ∈ ℤ` on the maximum lateness. -/
def bound (i : MultipurposeFlowShopOutTreeLatenessInstance) : ℤ :=
  (i.2.2.2.2.1 : ℤ) - (i.2.2.2.2.2 : ℤ)

/-- `j` is an immediate predecessor of `k` (and `k` an immediate successor of `j`): `j → k`, and
no job `c` has `j → c → k`. -/
def ImmediatePredecessor (i : MultipurposeFlowShopOutTreeLatenessInstance) (j k : Job i) :
    Prop :=
  Prec i.2.2.2.1 j k ∧ ∀ c, ¬ (Prec i.2.2.2.1 j c ∧ Prec i.2.2.2.1 c k)

/-- Well-formedness of an instance: the machine environment is well formed, there is at least
one job (so that `L_max = max_i (C_i - d_i)` is defined), the listed pairs describe a precedence
relation on the jobs, and it is an out-tree (every job has at most one immediate predecessor). -/
def WellFormed (i : MultipurposeFlowShopOutTreeLatenessInstance) : Prop :=
  StagesWellFormed i.1 i.2.1 ∧ i.2.2.1 ≠ [] ∧ PrecedenceWellFormed i.2.2.1.length i.2.2.2.1 ∧
    ∀ k a b, ImmediatePredecessor i a k → ImmediatePredecessor i b k → a = b

/-- Some MPM flow-shop schedule of the unit-time jobs obeys the precedence constraints and has
maximum lateness at most `K`: `C_j - d_j ≤ K` for every job `j`. -/
def MultipurposeFlowShopOutTreeLatenessFeasible
    (i : MultipurposeFlowShopOutTreeLatenessInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin i.1,
    IsPrecedenceSchedule i.1 i.2.1 i.2.2.2.1 σ a ∧
      ∀ j, (completionTime (fun _ _ => 1) σ j : ℤ) - dueDate i j ≤ bound i

open Classical in
/-- `FMPM|outtree; p_ij = 1|L_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeFlowShopOutTreeLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopOutTreeLatenessInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeFlowShopOutTreeLatenessFeasible i)
  | none => false

/-- **`FMPM|outtree; p_ij = 1|L_max` is NP-complete.** Source: Brucker (2007), Chapter 10 and
Table 5.3; Brucker, Garey and Johnson (1977); Brucker and Knust, *Complexity results for
scheduling problems*. -/
public theorem_wanted multipurposeFlowShopOutTreeLateness_npComplete :
    multipurposeFlowShopOutTreeLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeFlowShopOutTreeLatenessDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopOutTreeLateness
