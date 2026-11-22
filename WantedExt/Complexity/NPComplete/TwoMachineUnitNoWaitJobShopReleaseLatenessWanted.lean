/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP WITH RELEASE DATES, MAXIMUM LATENESS, is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class table "Job-shop problems with nowait" (`J2|p_ij=1;r_i;no-wait|L_max`: minimal NP-hard,
in the strong sense, Timkovsky (1998)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopReleaseLateness

/-!
# TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP WITH RELEASE DATES, MAXIMUM LATENESS, is NP-complete

INSTANCE: a job shop with `m = 2` machines `M_1, M_2` and jobs `1, …, n`; job `j` is a chain of
`n_j` operations `O_j1, …, O_jn_j`, where `O_jk` is processed on machine `μ_jk` for
`p_jk = 1` time unit, consecutive operations of a job use different machines, and `O_j,k+1`
cannot start before `O_jk` is completed; each machine processes at most one operation at a
time; each job `j` has a release date `r_j ∈ ℤ₀⁺` and cannot start before `r_j`; no wait: each
operation of a job starts exactly when the preceding operation of the same job is completed;
each job `j` has a due date `d_j ∈ ℤ`; and a bound `K ∈ ℤ`.
QUESTION: is there a feasible schedule whose maximum lateness `max_j (C_j - d_j)` is at most
`K`, where `C_j` is the completion time of the last operation of job `j`?

In the Brucker-Knust notation this is `J2|p_ij=1;r_i;no-wait|L_max`. With two machines and
consecutive operations on different machines, the machines of a job alternate, so job `j` is given
by the machine `μ_j1 ∈ {1, 2}` of its first operation and its number `n_j ≥ 1` of operations; `n_j`
is a number of the input, written in binary like the release dates, the due dates and `K`. This is
the convention of the Brucker-Knust classification of unit-time job shops, which lists
`J2|p_ij=1;no-wait|C_max` both as pseudopolynomially solvable and as NP-hard in the ordinary sense;
with unit processing times this is possible only with the operation counts written in binary. Under
the no-wait condition a schedule is determined by the start times `S_j` of the jobs' first
operations, and two jobs use the same machine at the same time exactly when their intervals
`[S_j, S_j + n_j)` overlap and `μ_j1 + S_j` and `μ_j'1 + S_j'` have the same parity, so the problem
is in NP with this encoding.

Operations are numbered from `0`; operation `k` of job `j` is processed on `μ_j1` if `k` is even
and on the other machine if `k` is odd. An operation started at time `s` occupies its machine
during `[s, s + 1)`. The precedence condition `σ(O_j,k+1) ≥ σ(O_jk) + 1` is implied by the
no-wait equality `σ(O_j,k+1) = σ(O_jk) + 1` and is not stated separately. The release date
bounds the start of the first operation (the later ones start later). Due dates and `K` are
integers, each encoded as a pair of naturals `(positive part, negative part)` representing
their difference, as in `ZeroOneILPWanted`; `max_j (C_j - d_j) ≤ K` is stated as
`C_j - d_j ≤ K` for every job `j` (with no jobs every `K` is met).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs, job `j` given as `(μ_j1, n_j, r_j, d_j)` (the machine of its first
operation, its number of operations, its release date and its due date as a pair
`(d⁺, d⁻)` with `d_j = d⁺ - d⁻`), and the bound `K` as a pair `(K⁺, K⁻)` with
`K = K⁺ - K⁻`. -/
abbrev TwoMachineUnitNoWaitJobShopReleaseLatenessInstance :=
  List (ℕ × ℕ × ℕ × (ℕ × ℕ)) × (ℕ × ℕ)

/-- Well-formedness of an instance: the first machine of every job is `1` or `2`, and every job
has at least one operation. -/
def WellFormed (i : TwoMachineUnitNoWaitJobShopReleaseLatenessInstance) : Prop :=
  ∀ job ∈ i.1, (job.1 = 1 ∨ job.1 = 2) ∧ 0 < job.2.1

/-- An operation `O_jk` of the instance: a job `j` and a position `k < n_j`. -/
abbrev Operation (i : TwoMachineUnitNoWaitJobShopReleaseLatenessInstance) : Type :=
  (j : Fin i.1.length) × Fin (i.1.get j).2.1

/-- The machine `μ_jk` of an operation: the first machine of its job at even positions, the
other machine (`3 - μ_j1`) at odd positions. -/
def machine (i : TwoMachineUnitNoWaitJobShopReleaseLatenessInstance) (o : Operation i) :
    ℕ :=
  if o.2.1 % 2 = 0 then (i.1.get o.1).1 else 3 - (i.1.get o.1).1

/-- There is a feasible no-wait schedule with maximum lateness at most `K`: start times `σ`
such that two distinct operations on the same machine occupy disjoint unit intervals, each
operation of a job after the first starts exactly one time unit after the previous one, the
first operation of every job `j` starts no earlier than `r_j`, and the last operation of every
job `j` completes at a time `C_j` with `C_j - d_j ≤ K`. -/
def TwoMachineUnitNoWaitJobShopReleaseLatenessFeasible
    (i : TwoMachineUnitNoWaitJobShopReleaseLatenessInstance) : Prop :=
  ∃ σ : Operation i → ℕ,
    (∀ o o', o ≠ o' → machine i o = machine i o' → σ o + 1 ≤ σ o' ∨ σ o' + 1 ≤ σ o) ∧
    (∀ j (k k' : Fin (i.1.get j).2.1), k'.1 = k.1 + 1 → σ ⟨j, k'⟩ = σ ⟨j, k⟩ + 1) ∧
    (∀ j (k : Fin (i.1.get j).2.1), k.1 = 0 → (i.1.get j).2.2.1 ≤ σ ⟨j, k⟩) ∧
    ∀ j (k : Fin (i.1.get j).2.1), k.1 + 1 = (i.1.get j).2.1 →
      ((σ ⟨j, k⟩ + 1 : ℕ) : ℤ) - (((i.1.get j).2.2.2.1 : ℤ) - (i.1.get j).2.2.2.2) ≤
        (i.2.1 : ℤ) - i.2.2

open Classical in
/-- TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP WITH RELEASE DATES, MAXIMUM LATENESS, as a decision
problem over bitstrings. -/
noncomputable def twoMachineUnitNoWaitJobShopReleaseLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineUnitNoWaitJobShopReleaseLatenessInstance) x with
  | some i => decide (WellFormed i ∧ TwoMachineUnitNoWaitJobShopReleaseLatenessFeasible i)
  | none => false

/-- **TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP WITH RELEASE DATES, MAXIMUM LATENESS, is
NP-complete.** Source: Timkovsky (1998); Brucker and Knust, class table "Job-shop problems with
nowait". -/
public theorem_wanted twoMachineUnitNoWaitJobShopReleaseLateness_npComplete :
    twoMachineUnitNoWaitJobShopReleaseLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoMachineUnitNoWaitJobShopReleaseLatenessDec

end MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopReleaseLateness
