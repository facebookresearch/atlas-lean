/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE JOB SHOP JMPM2|n=3|Cmax is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM job shop
model, and the statement that the MPM job shop problem with two machines and three jobs is
NP-hard, attributed to W. Meyer, *Geometrische Methoden zur Lösung von Job-Shop Problemen und
deren Verallgemeinerungen*, PhD thesis, Universität Osnabrück (1992));
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `JMPM2|n=3|C_max`, minimal NP-hard in the ordinary sense and maximal pseudopolynomially
solvable, citing B. Jurisch, Discrete Applied Mathematics 58 (1995), 145-156,
doi:10.1016/0166-218X(93)E0124-H, and Meyer (1992)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobs

/-!
# MULTIPURPOSE-MACHINE JOB SHOP JMPM2|n=3|Cmax is NP-complete

INSTANCE: `m = 2` machines `M₁, M₂`; exactly `n = 3` jobs, each a chain of `n_j ≥ 1` operations
`O_{j1}, …, O_{jn_j}`, where each operation `O_{jk}` has a processing time `p_{jk} ∈ ℤ₀⁺` and a
nonempty set `μ_{jk} ⊆ {M₁, M₂}` of eligible machines and is processed on exactly one machine of
`μ_{jk}`; and a bound `K ∈ ℤ₀⁺`. Each machine processes at most one operation at a time, and
`O_{j,k+1}` cannot start before `O_{jk}` is completed. QUESTION: is there a schedule whose makespan,
the largest completion time of a job (of its last operation), is at most `K`?

This is the job shop with multi-purpose machines (MPM) of Brucker (2004), Chapter 10: in the
general shop with multi-purpose machines a machine set `μ_{ij}` is associated with each operation,
which is processed by one machine of that set, and the MPM job shop is the special case in which
the operations of each job form a chain. Brucker states that, contrary to the classical job shop
(where `J2|n=3|C_max` is polynomially solvable), the MPM job shop with two machines and three jobs
is NP-hard, citing Meyer (1992); Brucker and Knust's classification lists `JMPM2|n=3|C_max` as
minimal NP-hard in the ordinary sense and maximal pseudopolynomially solvable. The model puts no
condition on the machine sets of consecutive operations of a job: they may coincide, and two
consecutive operations, which never overlap in time, may use the same machine.

A schedule chooses a machine `a t ∈ μ_{jk}` and a start time `σ t ∈ ℤ₀⁺` for every operation `t`;
operation `t` occupies its machine during the half-open interval `[σ t, σ t + p_t)`, and two
different operations on the same machine do not overlap: if both have positive length, one ends
before the other starts; an operation of length `0` occupies no machine time. Start times are natural numbers: shifting every
operation of a feasible schedule as early as its machine and job predecessors allow makes every
start time `0` or the completion time of another operation, hence an integer, and completes no
operation later, so this does not change the answer. The number of machines is part of the
instance, and `WellFormed` fixes it to `2` and the number of jobs to `3`. Numbers use the binary
encoding (the problem is NP-hard in the ordinary sense only).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An MPM job shop instance: the number `m` of machines; the jobs, job `j` being the list of its
operations in order, each operation given as the pair `(p_{jk}, μ_{jk})` of its processing time and
the list of its eligible machines (numbered `1, …, m`); and the bound `K`. -/
abbrev MPMJobShopInstance := ℕ × List (List (ℕ × List ℕ)) × ℕ

/-- An operation `O_{jk}` of the instance: a job `j` and a position `k < n_j` (numbered from
`0`). -/
abbrev Operation (i : MPMJobShopInstance) : Type :=
  (j : Fin i.2.1.length) × Fin (i.2.1.get j).length

/-- The processing time `p_{jk}` of an operation. -/
def opLength (i : MPMJobShopInstance) (t : Operation i) : ℕ :=
  ((i.2.1.get t.1).get t.2).1

/-- The eligible machines `μ_{jk}` of an operation. -/
def eligible (i : MPMJobShopInstance) (t : Operation i) : List ℕ :=
  ((i.2.1.get t.1).get t.2).2

/-- `a` and `σ` form an MPM job shop schedule: operation `t` runs on machine `a t ∈ μ_t` during
`[σ t, σ t + p_t)`; two different operations of positive length on the same machine do not overlap
(an operation of length `0` occupies no machine time); and every operation of a job starts no earlier
than the previous operation of the job completes. -/
def IsMPMJobShopSchedule (i : MPMJobShopInstance) (a σ : Operation i → ℕ) : Prop :=
  (∀ t, a t ∈ eligible i t) ∧
    (∀ t t', t ≠ t' → a t = a t' → 0 < opLength i t → 0 < opLength i t' →
      σ t + opLength i t ≤ σ t' ∨ σ t' + opLength i t' ≤ σ t) ∧
    ∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k⟩ + opLength i ⟨j, k⟩ ≤ σ ⟨j, k'⟩

/-- Well-formedness of an MPM job shop instance with `m` machines: the instance has `m` machines,
every job has at least one operation, and every operation has a nonempty set of eligible machines,
all in `{1, …, m}`. -/
def MPMWellFormed (m : ℕ) (i : MPMJobShopInstance) : Prop :=
  i.1 = m ∧ (∀ job ∈ i.2.1, job ≠ []) ∧ (∀ job ∈ i.2.1, ∀ o ∈ job, o.2 ≠ []) ∧
    ∀ job ∈ i.2.1, ∀ o ∈ job, ∀ M ∈ o.2, 1 ≤ M ∧ M ≤ i.1

/-- Well-formedness of an instance: a well-formed MPM job shop instance with `m = 2` machines and
exactly three jobs. -/
def WellFormed (i : MPMJobShopInstance) : Prop :=
  MPMWellFormed 2 i ∧ i.2.1.length = 3

/-- Some MPM job shop schedule has makespan at most `K`: the last operation of every job, which
completes after the job's other operations, completes by `K`. -/
def MultiPurposeJobShopThreeJobsFeasible (i : MPMJobShopInstance) : Prop :=
  ∃ a σ : Operation i → ℕ, IsMPMJobShopSchedule i a σ ∧
    ∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
      σ ⟨j, k⟩ + opLength i ⟨j, k⟩ ≤ i.2.2

open Classical in
/-- MULTIPURPOSE-MACHINE JOB SHOP `JMPM2|n=3|C_max` as a decision problem over bitstrings. -/
noncomputable def multiPurposeJobShopThreeJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMJobShopInstance) x with
  | some i => decide (WellFormed i ∧ MultiPurposeJobShopThreeJobsFeasible i)
  | none => false

/-- **MULTIPURPOSE-MACHINE JOB SHOP `JMPM2|n=3|C_max` is NP-complete.** Source: Brucker (2004),
Chapter 10 (Meyer (1992)); Brucker and Knust, scheduling classification, class `mpm_shop`. -/
public theorem_wanted multiPurposeJobShopThreeJobs_npComplete :
    multiPurposeJobShopThreeJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiPurposeJobShopThreeJobsDec

end MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobs
