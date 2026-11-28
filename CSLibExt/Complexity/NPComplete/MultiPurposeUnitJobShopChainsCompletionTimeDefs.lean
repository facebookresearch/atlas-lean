/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE JOB SHOP JMPM2|chains;p_ij=1|ΣC_i: definitions

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
recorded in P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `JMPM2|chains;p_ij=1|ΣC_i`, minimal NP-hard in the strong sense, Timkovsky (1998));
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM job shop
model).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Logic.Relation
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiPurposeUnitJobShopChainsCompletionTime

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule
  MPMWellFormed)

/-- An instance: an MPM job shop instance (the number `m` of machines, the jobs as lists of
operations `(p_{jk}, μ_{jk})`, and the bound `K` on the total completion time) and the arcs
`(j, j')` of the chains, `j` the immediate predecessor of `j'`. -/
abbrev MultiPurposeUnitJobShopChainsCompletionTimeInstance := MPMJobShopInstance × List (ℕ × ℕ)

/-- The arc relation of the chains: `j` is the immediate predecessor of `j'` when the pair
`(j, j')` is listed. -/
def Arc (i : MultiPurposeUnitJobShopChainsCompletionTimeInstance)
    (j j' : Fin i.1.2.1.length) : Prop :=
  ((j : ℕ), (j' : ℕ)) ∈ i.2

/-- Well-formedness of an instance: a well-formed MPM job shop instance with `m = 2` machines
(every job nonempty, every operation with a nonempty set of eligible machines in `{1, 2}`), every
operation of length `1`, every arc names two jobs, no two distinct arcs share their tail (at most
one immediate successor) or their head (at most one immediate predecessor), and the arcs have no
cycle. -/
def WellFormed (i : MultiPurposeUnitJobShopChainsCompletionTimeInstance) : Prop :=
  MPMWellFormed 2 i.1 ∧ (∀ job ∈ i.1.2.1, ∀ o ∈ job, o.1 = 1) ∧
    (∀ a ∈ i.2, a.1 < i.1.2.1.length ∧ a.2 < i.1.2.1.length) ∧
    (∀ a ∈ i.2, ∀ b ∈ i.2, a.1 = b.1 → a = b) ∧
    (∀ a ∈ i.2, ∀ b ∈ i.2, a.2 = b.2 → a = b) ∧
    ∀ j, ¬ Relation.TransGen (Arc i) j j

/-- Some MPM job shop schedule meets the chains and has total completion time at most `K`: the
first operation of a job starts no earlier than the last operation of its immediate predecessor
completes, and the completion times `C j` (the completion times of the last operations) sum to at
most `K`. -/
def MultiPurposeUnitJobShopChainsCompletionTimeFeasible
    (i : MultiPurposeUnitJobShopChainsCompletionTimeInstance) : Prop :=
  ∃ a σ : Operation i.1 → ℕ, IsMPMJobShopSchedule i.1 a σ ∧
    (∀ j j', Arc i j j' → ∀ (k : Fin (i.1.2.1.get j).length)
      (k' : Fin (i.1.2.1.get j').length), k.1 + 1 = (i.1.2.1.get j).length → k'.1 = 0 →
        σ ⟨j, k⟩ + opLength i.1 ⟨j, k⟩ ≤ σ ⟨j', k'⟩) ∧
    ∃ C : Fin i.1.2.1.length → ℕ,
      (∀ j (k : Fin (i.1.2.1.get j).length), k.1 + 1 = (i.1.2.1.get j).length →
        C j = σ ⟨j, k⟩ + opLength i.1 ⟨j, k⟩) ∧
      ∑ j, C j ≤ i.1.2.2

open Classical in
/-- MULTIPURPOSE-MACHINE JOB SHOP `JMPM2|chains;p_ij=1|ΣC_i` as a decision problem over
bitstrings. -/
noncomputable def multiPurposeUnitJobShopChainsCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiPurposeUnitJobShopChainsCompletionTimeInstance) x with
  | some i => decide (WellFormed i ∧ MultiPurposeUnitJobShopChainsCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiPurposeUnitJobShopChainsCompletionTime
