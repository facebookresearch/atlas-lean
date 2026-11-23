/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP WITH TRANSPORTATION DELAYS O|p_ij=1;t_kl=t_lk|Cmax is NP-complete

Source:
V. J. Rayward-Smith and D. Rebaine, "Open shop scheduling with delays", RAIRO Informatique
théorique et Applications 26 (1992), 439-447, doi:10.1051/ita/1992260504391, Section 2,
problem OmDU and Theorem 2 ("OmDU is NP-complete even if the delays are symmetric");
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Open-shop problems
with transportation delays" (University of Osnabrück,
http://www.mathematik.uni-osnabrueck.de/research/OR/class/), problem `O|p_ij=1;t_kl=t_lk|C_max`,
minimal strongly NP-hard, credited to Rayward-Smith and Rebaine (1992).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.OpenShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopSymmetricTransportationDelays

open MetaMathlibExt.Complexity.NPComplete.OpenShopScheduling (OpenShopSchedulingInstance)
open MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopScheduling
  (IsOpenShopSchedule taskLength)

/-!
# OPEN SHOP WITH TRANSPORTATION DELAYS O|p_ij=1;t_kl=t_lk|Cmax is NP-complete

INSTANCE: an open shop with `m` machines `M_1, …, M_m` (`m` part of the input) and jobs
`1, …, n`, each consisting of `m` operations of unit length, one on each machine, processed in
any order but no two at the same time; each machine processes at most one operation at a time;
a transportation delay `t_kl ∈ ℤ₀⁺` for each pair of distinct machines, symmetric
(`t_kl = t_lk`): if a job's operation on `M_l` starts no earlier than its operation on `M_k`,
it starts at least `t_kl` time units after that operation is completed; a bound `K ∈ ℤ⁺`.
QUESTION: is there a schedule whose makespan, the largest completion time of an operation, is
at most `K`?

Rayward-Smith and Rebaine define a valid open-shop schedule with delays by integer start times
`σ(i, j)` of the task of job `j` on machine `i` such that (1) a machine does not process two tasks
at once and (2') `0 ≤ σ(h, j) - σ(i, j) < l_ij + d_jih` implies `h = i`, where `d_jih` is the
delay for transferring job `j` from machine `i` to machine `h`. Their problem OmDU has unit
tasks, delays `d_jhi ∈ ℤ₀⁺` and a bound `L ∈ ℤ⁺` on the completion time; Theorem 2 proves it
NP-complete even for symmetric delays, by a transformation from HAMILTONIAN PATH whose instances
have a single job, so that the delays depend only on the pair of machines. This is Brucker and
Knust's `O|p_ij=1;t_kl=t_lk|C_max`, which they list as minimal strongly NP-hard.

The instance extends an OPEN-SHOP SCHEDULING instance of `OpenShopSchedulingWanted` (the number
`m` of machines, the jobs, each listed as the list of its `m` task lengths, and the deadline
`D = K`) by the delay matrix, a list of `m` rows of `m` entries. The schedule is
`NoWaitFlowShopScheduling.IsOpenShopSchedule`: each machine's start times are pairwise distinct
and a later task starts after an earlier one completes, the tasks of a job occupy disjoint
intervals, and every task completes by `K`, which is the makespan bound. `WellFormed` keeps the
parent's conditions (`m ≥ 1`, `m` tasks per job, `K ≥ 1`) and adds that every task has length
`1`, that the matrix is `m × m` and symmetric, and that its diagonal, which no condition reads,
is `0`. Binary encoding of all numbers. Membership in NP: the start times are a certificate,
each below `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: an OPEN-SHOP SCHEDULING instance (the number `m` of machines, the jobs as lists
of task lengths, the bound `K`) and the delay matrix, row `k` listing `t_k0, …, t_k(m-1)`. -/
abbrev UnitOpenShopSymmetricTransportationDelaysInstance :=
  OpenShopSchedulingInstance × List (List ℕ)

/-- The transportation delay `t_kl` from machine `k` to machine `l`. -/
def delay (i : UnitOpenShopSymmetricTransportationDelaysInstance) (k l : Fin i.1.1) : ℕ :=
  (i.2.getD k []).getD l 0

/-- Well-formedness of an instance: a well-formed OPEN-SHOP SCHEDULING instance (`m ≥ 1`, `m`
tasks per job, `K ≥ 1`) whose tasks all have length `1`, with an `m × m` symmetric delay matrix
whose diagonal is `0`. -/
def WellFormed (i : UnitOpenShopSymmetricTransportationDelaysInstance) : Prop :=
  NoWaitFlowShopScheduling.WellFormed i.1 ∧ (∀ job ∈ i.1.2.1, ∀ l ∈ job, l = 1) ∧
    i.2.length = i.1.1 ∧ (∀ row ∈ i.2, row.length = i.1.1) ∧
    (∀ k l, delay i k l = delay i l k) ∧ ∀ k, delay i k k = 0

/-- Some open-shop schedule meeting the makespan bound `K` respects the delays: if job `j`'s
task on machine `q ≠ p` starts no earlier than its task on machine `p`, it starts at least
`t_pq` after that task is completed. -/
def UnitOpenShopSymmetricTransportationDelaysFeasible
    (i : UnitOpenShopSymmetricTransportationDelaysInstance) : Prop :=
  ∃ σ : Fin i.1.1 → Fin i.1.2.1.length → ℕ, IsOpenShopSchedule i.1 σ ∧
    ∀ j p q, p ≠ q → σ p j ≤ σ q j → σ p j + taskLength i.1 p j + delay i p q ≤ σ q j

open Classical in
/-- OPEN SHOP WITH TRANSPORTATION DELAYS `O|p_ij=1;t_kl=t_lk|C_max` as a decision problem over
bitstrings. -/
noncomputable def unitOpenShopSymmetricTransportationDelaysDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitOpenShopSymmetricTransportationDelaysInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopSymmetricTransportationDelaysFeasible i)
  | none => false

/-- **OPEN SHOP WITH TRANSPORTATION DELAYS `O|p_ij=1;t_kl=t_lk|C_max` is NP-complete.** Source:
Rayward-Smith and Rebaine (1992), Theorem 2; Brucker and Knust, scheduling classification,
class `o_tra`. -/
public theorem_wanted unitOpenShopSymmetricTransportationDelays_npComplete :
    unitOpenShopSymmetricTransportationDelaysDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitOpenShopSymmetricTransportationDelaysDec

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopSymmetricTransportationDelays
