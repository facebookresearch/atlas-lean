/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP WITH THREE MACHINES (OMPM3||C_max) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING, comment: remains
NP-complete if `m = 3`; T. Gonzalez and S. Sahni, "Open shop scheduling to minimize finish time",
Journal of the ACM 23 (1976), 665-679, doi:10.1145/321978.321985; P. Brucker, *Scheduling
Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5, Chapter 10 (the MPM open-shop
model); P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `OMPM3||C_max` as minimal NP-hard (in the ordinary sense), citing Gonzalez
and Sahni (1976).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MPMFlowShopThreeMachinesWanted
public import WantedExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMOpenShopThreeMachines

open MPMFlowShopThreeMachines (MPMFlowShopInstance WellFormed)
open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)

/-!
# MPM OPEN SHOP WITH THREE MACHINES (OMPM3||C_max) is NP-complete

INSTANCE: machines `M_1, M_2, M_3`; an MPM open shop with `r ≥ 1` stages and nonempty machine sets
`μ_1, …, μ_r ⊆ {M_1, M_2, M_3}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij ∈ ℕ`, where `O_ij` is processed by one
machine of `μ_j`, and the operations of a job are processed in any order but no two of them at the
same time; and a bound `K`. Each machine processes at most one operation at a time. QUESTION: is
there a feasible schedule with makespan `max_i C_i ≤ K`, where `C_i` is the completion time of job
`i` (that of its last operation)?

The MPM open shop is Brucker's (*Scheduling Algorithms*, Chapter 10): MPM open-shop problems are
defined like MPM flow-shop problems (each job has exactly `r` operations, the `j`-th operation of
every job is processed by a machine of the same set `μ_j`, and the machine sets are different), but
with no precedence constraints between the operations of a job. The instance data and their
well-formedness are those of the three-machine MPM flow shop `FMPM3||C_max`
(`MPMFlowShopThreeMachinesWanted`): `MPMFlowShopThreeMachines.MPMFlowShopInstance` (the number `r`
of stages, one list of the `r` processing times per job, the bound `K`, and the machine sets as
lists of machine indices `0, 1, 2`), and `MPMFlowShopThreeMachines.WellFormed` (`0 < r`, every job
with `r` operations, `0 < K`, one nonempty machine set per stage within `{0, 1, 2}`, pairwise
different sets). The schedule predicate is the MPM open-shop schedule `IsMPMOpenShopSchedule` of
`MultipurposeOpenShopPrecedenceMakespanWanted` (each operation `(j, s)` gets a start time `σ j s`
and a machine `a j s ∈ μ_s`; operations of one job, and operations on one machine, occupy disjoint
intervals `[σ j s, σ j s + p_js)`), and `C_j` is
`MultipurposeFlowShopPrecedenceMakespan.completionTime`, the latest completion time of a job's
operations. With integer data, integer start times lose no generality.

The classical three-machine open shop `O3||C_max` is the special case `r = 3`, `μ_j = {M_j}`, which
Gonzalez and Sahni prove NP-hard (Garey and Johnson [SS14]: NP-complete for `m = 3`), and Brucker
and Knust list `OMPM3||C_max` as minimal NP-hard in the ordinary sense on that basis. Processing
times and the bound use the binary encoding. Membership in NP: the machines and start times are a
certificate; every start time is at most `C_j ≤ K`, so the certificate has polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some MPM open-shop schedule on the three machines (`σ` start times, `a` machines, operation
`(j, s)` of length `p_js`) completes every job by `K`. -/
def MPMOpenShopThreeMachinesFeasible (i : MPMFlowShopInstance) : Prop :=
  ∃ σ : Fin i.1.2.1.length → Fin i.2.length → ℕ, ∃ a : Fin i.1.2.1.length → Fin i.2.length → Fin 3,
    IsMPMOpenShopSchedule 3 i.2 (fun j s => (i.1.2.1.get j).getD s 0) σ a ∧
      ∀ j, completionTime (fun j s => (i.1.2.1.get j).getD s 0) σ j ≤ i.1.2.2

open Classical in
/-- `OMPM3||C_max` as a decision problem over bitstrings. -/
noncomputable def mpmOpenShopThreeMachinesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMFlowShopInstance) x with
  | some i => decide (WellFormed i ∧ MPMOpenShopThreeMachinesFeasible i)
  | none => false

/-- **MPM OPEN SHOP WITH THREE MACHINES (OMPM3||C_max) is NP-complete.** Source: Garey and Johnson
(1979), [SS14]; Gonzalez and Sahni (1976) (`O3||C_max`, the special case `μ_j = {M_j}`); Brucker
(2007), Chapter 10 (model); Brucker and Knust's classification. -/
public theorem_wanted mpmOpenShopThreeMachines_npComplete :
    mpmOpenShopThreeMachinesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mpmOpenShopThreeMachinesDec

end MetaMathlibExt.Complexity.NPComplete.MPMOpenShopThreeMachines
