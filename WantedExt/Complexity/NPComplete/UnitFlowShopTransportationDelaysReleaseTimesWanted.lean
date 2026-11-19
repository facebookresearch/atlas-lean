/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP WITH TRANSPORTATION DELAYS F2|p_ij=1;t_i;r_i|ΣC_i is NP-complete

Source:
P. Brucker, T. C. E. Cheng, S. Knust and N. V. Shakhlevich, "Complexity results for flow-shop
and open-shop scheduling problems with transportation delays", Annals of Operations Research
129 (2004), 81-106, doi:10.1023/B:ANOR.0000030683.64615.c8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_tra` (flow-shop problems with transportation delays), Universität Osnabrück (last
update 2006).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WantedExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysReleaseTimes

open UnitFlowShopTransportationDelays (IsUnitFlowShopSchedule)

/-!
# FLOW SHOP WITH TRANSPORTATION DELAYS F2|p_ij=1;t_i;r_i|ΣC_i is NP-complete

INSTANCE: `n` jobs, each consisting of two unit-time operations, the first on machine `M₁` and
the second on machine `M₂`; for each job `j` a release date `r_j ∈ ℤ₀⁺` and a transportation
delay `t_j ∈ ℤ₀⁺`; a bound `K`. Each machine processes at most one operation at a time; job `j`
cannot start before `r_j`; the second operation of job `j` cannot start until `t_j` time units
after the completion of its first operation (the delay uses no machine, and any number of jobs
can be in transit at once). QUESTION: is there a schedule whose total completion time
`∑_j C_j` is at most `K`, where `C_j` is the completion time of job `j`'s second operation?

In the three-field notation this is `F2|p_ij=1; t_i; r_i|∑ C_i`. Brucker and Knust's
classification lists it as minimal strongly NP-hard, citing Brucker, Cheng, Knust and
Shakhlevich (2004), whose survey of flow-shop and open-shop problems with transportation delays
derives new complexity results.

A schedule is the one of `UnitFlowShopTransportationDelaysWanted` (`F2|p_ij=1; t_i|C_max`):
`IsUnitFlowShopSchedule` with the job delays, i.e. each machine runs a one-processor schedule of
its unit operations and job `j`'s second operation starts at least `t_j` after its first
completes; here job `j`'s first operation also starts no earlier than `r_j`. Start times are
natural numbers: with integer data, shifting every operation of a feasible schedule as early as
its machine order and release dates allow gives an integral schedule with no later completion
times, so this does not change the answer. The jobs are `Fin n`, one per listed pair
`(r_j, t_j)`. Binary encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs, job `j` being the `j`-th pair `(r_j, t_j)` of release date and
delay, and the bound `K`. -/
abbrev UnitFlowShopTransportationDelaysReleaseTimesInstance := List (ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed pairs. -/
abbrev Job (i : UnitFlowShopTransportationDelaysReleaseTimesInstance) : Type :=
  Fin i.1.length

/-- The release date `r_j` of job `j`. -/
def releaseDate (i : UnitFlowShopTransportationDelaysReleaseTimesInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The delay `t_j` of job `j`. -/
def delay (i : UnitFlowShopTransportationDelaysReleaseTimesInstance) (j : Job i) : ℕ :=
  (i.1.get j).2

/-- Well-formedness of an instance: every list of pairs with a bound is an instance (release
dates and delays are non-negative integers, and the bound needs no condition). -/
def WellFormed (_i : UnitFlowShopTransportationDelaysReleaseTimesInstance) : Prop :=
  True

/-- Some schedule with the job delays starts every job no earlier than its release date and
has total completion time `∑_j C_j` at most `K`, where `C_j = σ 1 j + 1`. -/
def UnitFlowShopTransportationDelaysReleaseTimesFeasible
    (i : UnitFlowShopTransportationDelaysReleaseTimesInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, IsUnitFlowShopSchedule (delay i) σ ∧
    (∀ j, releaseDate i j ≤ σ 0 j) ∧
    ∑ j, (σ 1 j + 1) ≤ i.2

open Classical in
/-- FLOW SHOP WITH TRANSPORTATION DELAYS `F2|p_ij=1;t_i;r_i|∑ C_i` as a decision problem over
bitstrings. -/
noncomputable def unitFlowShopTransportationDelaysReleaseTimesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopTransportationDelaysReleaseTimesInstance) x with
  | some i => decide (WellFormed i ∧ UnitFlowShopTransportationDelaysReleaseTimesFeasible i)
  | none => false

/-- **FLOW SHOP WITH TRANSPORTATION DELAYS `F2|p_ij=1;t_i;r_i|∑ C_i` is NP-complete.** Source:
Brucker, Cheng, Knust and Shakhlevich (2004); Brucker and Knust, scheduling classification,
class `f_tra`. -/
public theorem_wanted unitFlowShopTransportationDelaysReleaseTimes_npComplete :
    unitFlowShopTransportationDelaysReleaseTimesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitFlowShopTransportationDelaysReleaseTimesDec

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysReleaseTimes
