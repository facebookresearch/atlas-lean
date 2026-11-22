/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM FLOW SHOP WITH PRECEDENCE AND UNIT TIMES (FMPM|prec; p_ij = 1|C_max) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007): Section 1.3 (precedence
relations), Chapter 10 (the MPM flow-shop model) and Table 5.3 (`P|p_i = 1; prec|C_max` is
NP-hard, Ullman);
J. D. Ullman, "NP-complete scheduling problems", Journal of Computer and System Sciences 10
(1975), 384-393, doi:10.1016/S0022-0000(75)80008-0;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `FMPM|prec; p_ij = 1|C_max` as strongly NP-hard with the attribution to
Ullman (1975).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespan

/-!
# MPM FLOW SHOP WITH PRECEDENCE AND UNIT TIMES (FMPM|prec; p_ij = 1|C_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an MPM flow shop with `r ≥ 1` stages and machine sets
`μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij = 1`; a precedence relation `→` on the
jobs given by an acyclic digraph; and a bound `K`. QUESTION: is there a feasible schedule with
makespan `max_i C_i ≤ K`?

The MPM flow shop is Brucker's (*Scheduling Algorithms*, Chapter 10): "each job `J_i` has
exactly `r` operations `O_ij` (`j = 1, …, r`) and there is the same machine set `μ_j` associated
with the `j`-th operation of each job. `r` is called the number of stages of the problem.
Furthermore, all machine sets are assumed to be different", and "for `j = 2, …, r`, `O_ij` cannot
start before `O_i,j-1` is completed"; `O_ij` "has to be processed by one machine in the set
`μ_ij`". A schedule is feasible if no two time intervals overlap on the same machine (Section
1.2). Precedence (Section 1.3): `(i, k) ∈ A` "iff `J_i` must be completed before `J_k` starts",
for an arbitrary acyclic digraph `G = (V, A)` (`prec`). The completion time `C_i` of job `i` is
that of its last operation.

Encoding. Machines are `Fin m`, stages `Fin r`, jobs `Fin n`. The machine sets are lists of
machine indices; "pairwise different" compares them as sets (`List.toFinset`). Operation
`(i, s)` gets a start time `σ i s` and a machine `a i s ∈ μ_s`, and occupies the half-open
interval `[σ i s, σ i s + p_is)`. The precedence relation is given by the list of its pairs
`(i, k)` with `i → k`, required to be a strict partial order (Mathlib's `IsStrictOrder`); since a
job completes after it starts, the constraints of an acyclic digraph and of its transitive
closure are satisfied by the same schedules, so giving the closure loses nothing. The jobs are
listed explicitly, one list `[p_i1, …, p_ir]` of processing times per job, each required to be
`1` (the convention of `PrecedenceConstrainedSchedulingWanted`, which lists unit task lengths), so
the input length grows with the number of jobs. Every stage machine set must be nonempty: an
operation "has to be processed by one machine in the set" (Brucker, Chapter 10). With integer
data, integer start times lose no generality. Binary encoding of all numbers (the problem is
NP-complete in the strong sense).

`StagesWellFormed`, `IsMPMFlowShopSchedule` and `completionTime` take arbitrary processing
times, and `Prec`, `PrecedenceWellFormed` and `IsPrecedenceSchedule` take the instance data as
arguments, so that the other MPM flow-shop problems of Brucker and Knust's class can state their
questions with them.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The MPM flow-shop machine environment with `m` machines and stage machine sets
`μ = [μ_1, …, μ_r]` (lists of machine indices) is well formed: there is at least one stage, every
machine set lists machines among `M_1, …, M_m` (indices `< m`), and different stages have
different machine sets. -/
def StagesWellFormed (m : ℕ) (μ : List (List ℕ)) : Prop :=
  μ ≠ [] ∧ (∀ M ∈ μ, ∀ k ∈ M, k < m) ∧ (μ.map List.toFinset).Nodup

/-- `σ` (start times) and `a` (machines) form an MPM flow-shop schedule of `n` jobs with
processing times `p i s` on `m` machines with stage machine sets `μ`: each operation `(i, s)` runs
on a machine of `μ_s`; operation `(i, s + 1)` starts no earlier than operation `(i, s)` is
completed; and two different operations on the same machine occupy disjoint time intervals
`[σ i s, σ i s + p i s)`. -/
def IsMPMFlowShopSchedule {n : ℕ} (m : ℕ) (μ : List (List ℕ)) (p : Fin n → Fin μ.length → ℕ)
    (σ : Fin n → Fin μ.length → ℕ) (a : Fin n → Fin μ.length → Fin m) : Prop :=
  (∀ i s, (a i s : ℕ) ∈ μ.get s) ∧
    (∀ i (s : Fin μ.length) (hs : s.1 + 1 < μ.length), σ i s + p i s ≤ σ i ⟨s.1 + 1, hs⟩) ∧
    ∀ i s i' s', (i, s) ≠ (i', s') → a i s = a i' s' →
      Disjoint (Finset.Ico (σ i s) (σ i s + p i s)) (Finset.Ico (σ i' s') (σ i' s' + p i' s'))

/-- The completion time `C_i` of job `i`: the latest completion time `σ i s + p i s` of its
operations (by the stage order, that of its last operation). -/
def completionTime {n r : ℕ} (p σ : Fin n → Fin r → ℕ) (i : Fin n) : ℕ :=
  Finset.univ.sup fun s => σ i s + p i s

/-- The precedence relation of the listed pairs: `i → k` when the pair `(i, k)` is listed. -/
def Prec (prs : List (ℕ × ℕ)) {n : ℕ} (i k : Fin n) : Prop :=
  ((i : ℕ), (k : ℕ)) ∈ prs

/-- The listed pairs describe a precedence relation on `n` jobs: every listed pair names two
jobs, and the listed pairs form a strict partial order. -/
def PrecedenceWellFormed (n : ℕ) (prs : List (ℕ × ℕ)) : Prop :=
  (∀ q ∈ prs, q.1 < n ∧ q.2 < n) ∧ IsStrictOrder (Fin n) (Prec prs)

/-- `σ` and `a` form an MPM flow-shop schedule of `n` unit-time jobs (`p_ij = 1`) on `m`
machines with stage machine sets `μ` that obeys the precedence constraints of the listed pairs:
if `i → k`, then no operation of `k` starts before `C_i`. -/
def IsPrecedenceSchedule {n : ℕ} (m : ℕ) (μ : List (List ℕ)) (prs : List (ℕ × ℕ))
    (σ : Fin n → Fin μ.length → ℕ) (a : Fin n → Fin μ.length → Fin m) : Prop :=
  IsMPMFlowShopSchedule m μ (fun _ _ => 1) σ a ∧
    ∀ i k, Prec prs i k → ∀ s, completionTime (fun _ _ => 1) σ i ≤ σ k s

/-- An instance: the number of machines `m`, the stage machine sets `[μ_1, …, μ_r]`, one list
`[p_i1, …, p_ir]` of processing times per job (all `1`), the pairs `(i, k)` with `i → k`, and the
bound `K`. -/
abbrev MultipurposeFlowShopPrecedenceMakespanInstance :=
  ℕ × List (List ℕ) × List (List ℕ) × List (ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed jobs. -/
abbrev Job (i : MultipurposeFlowShopPrecedenceMakespanInstance) : Type := Fin i.2.2.1.length

/-- The stages of the instance, `Fin r` for `r` machine sets. -/
abbrev Stage (i : MultipurposeFlowShopPrecedenceMakespanInstance) : Type := Fin i.2.1.length

/-- Well-formedness of an instance: the machine environment is well formed
(`StagesWellFormed`) and every stage machine set is nonempty, every job lists one processing time
per stage and all of them are `1`, and the listed pairs describe a precedence relation on the jobs
(`PrecedenceWellFormed`). -/
def WellFormed (i : MultipurposeFlowShopPrecedenceMakespanInstance) : Prop :=
  StagesWellFormed i.1 i.2.1 ∧ (∀ M ∈ i.2.1, M ≠ []) ∧
    (∀ job ∈ i.2.2.1, job.length = i.2.1.length ∧ ∀ p ∈ job, p = 1) ∧
    PrecedenceWellFormed i.2.2.1.length i.2.2.2.1

/-- Some MPM flow-shop schedule of the unit-time jobs obeys the precedence constraints and has
makespan at most `K`. -/
def MultipurposeFlowShopPrecedenceMakespanFeasible
    (i : MultipurposeFlowShopPrecedenceMakespanInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin i.1,
    IsPrecedenceSchedule i.1 i.2.1 i.2.2.2.1 σ a ∧
      ∀ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `FMPM|prec; p_ij = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeFlowShopPrecedenceMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopPrecedenceMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeFlowShopPrecedenceMakespanFeasible i)
  | none => false

/-- **`FMPM|prec; p_ij = 1|C_max` is NP-complete.** Source: Brucker (2007), Chapter 10 and
Table 5.3; Ullman (1975); Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted multipurposeFlowShopPrecedenceMakespan_npComplete :
    multipurposeFlowShopPrecedenceMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeFlowShopPrecedenceMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespan
