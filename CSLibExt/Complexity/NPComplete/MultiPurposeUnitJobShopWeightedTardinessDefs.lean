/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE JOB SHOP JMPM2|p_ij=1|Σw_iT_i: definitions

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
recorded in P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `JMPM2|p_ij=1|Σw_iT_i`, minimal NP-hard in the strong sense, Timkovsky (1998));
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM job shop
model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiPurposeUnitJobShopWeightedTardiness

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule
  MPMWellFormed)

/-- An instance: an MPM job shop instance (the number `m` of machines, the jobs as lists of
operations `(p_{jk}, μ_{jk})`, and the bound `K` on the total weighted tardiness) and one pair
`(d_j, w_j)` (due date, weight) per job. -/
abbrev MultiPurposeUnitJobShopWeightedTardinessInstance := MPMJobShopInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed MPM job shop instance with `m = 2` machines
(every job nonempty, every operation with a nonempty set of eligible machines in `{1, 2}`), every
operation of length `1`, and one pair `(d_j, w_j)` per job. -/
def WellFormed (i : MultiPurposeUnitJobShopWeightedTardinessInstance) : Prop :=
  MPMWellFormed 2 i.1 ∧ (∀ job ∈ i.1.2.1, ∀ o ∈ job, o.1 = 1) ∧ i.2.length = i.1.2.1.length

/-- Some MPM job shop schedule has `Σ_j w_j max(0, C_j - d_j) ≤ K` (natural subtraction
`C j - d_j` is `max(0, C_j - d_j)`), where `C j` is the completion time of the last operation of
job `j`. -/
def MultiPurposeUnitJobShopWeightedTardinessFeasible
    (i : MultiPurposeUnitJobShopWeightedTardinessInstance) : Prop :=
  ∃ a σ : Operation i.1 → ℕ, IsMPMJobShopSchedule i.1 a σ ∧
    ∃ C : Fin i.1.2.1.length → ℕ,
      (∀ j (k : Fin (i.1.2.1.get j).length), k.1 + 1 = (i.1.2.1.get j).length →
        C j = σ ⟨j, k⟩ + opLength i.1 ⟨j, k⟩) ∧
      ∑ j : Fin i.1.2.1.length, (i.2.getD j (0, 0)).2 * (C j - (i.2.getD j (0, 0)).1) ≤ i.1.2.2

open Classical in
/-- MULTIPURPOSE-MACHINE JOB SHOP `JMPM2|p_ij=1|Σw_iT_i` as a decision problem over
bitstrings. -/
noncomputable def multiPurposeUnitJobShopWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiPurposeUnitJobShopWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ MultiPurposeUnitJobShopWeightedTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiPurposeUnitJobShopWeightedTardiness
