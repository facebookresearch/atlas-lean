/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs

namespace MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobs

open MetaMathlibExt.BitstringEncoding

/-- A machine assignment or start times given by the job and position numbers of each
operation, for any instance. -/
private def byIndex {i : MPMJobShopInstance} (f : ℕ → ℕ → ℕ) : Operation i → ℕ :=
  fun t => f t.1 t.2

/-! ### Operations, lengths and eligible machines -/

/-- Three jobs on two machines with the bound `K`: job `0` runs `2` units on machine `1`, then
`1` unit on machine `2`; job `1` runs `1` unit on machine `2`; job `2` runs `3` units on either
machine. -/
private abbrev mixed (K : ℕ) : MPMJobShopInstance :=
  (2, [[(2, [1]), (1, [2])], [(1, [2])], [(3, [1, 2])]], K)

/-- An operation is a job and a position in it: `mixed K` has four, and the second operation of
job `0` has length `1` and the eligible machines `[2]`, while the operation of job `2` has length
`3` and may use either machine. -/
example :
    Fintype.card (Operation (mixed 5)) = 4 ∧
      opLength (mixed 5) ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ = 1 ∧
      eligible (mixed 5) ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ = [2] ∧
      opLength (mixed 5) ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩ = 3 ∧
      eligible (mixed 5) ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩ = [1, 2] := by
  decide

/-- Job `0` on machine `1` during `[0, 2)` and on machine `2` during `[2, 3)`, job `1` on
machine `2` during `[0, 1)`, job `2` on machine `1` during `[2, 5)`. -/
private def mixedMachine : Operation (mixed 5) → ℕ :=
  byIndex fun j k => if j = 0 ∧ k = 0 then 1 else if j = 2 then 1 else 2

private def mixedStart : Operation (mixed 5) → ℕ :=
  byIndex fun j k => if j = 0 ∧ k = 0 then 0 else if j = 1 then 0 else 2

private theorem mixed_wellFormed : WellFormed (mixed 5) := by
  unfold WellFormed MPMWellFormed; decide

private theorem mixed_schedule : IsMPMJobShopSchedule (mixed 5) mixedMachine mixedStart := by
  unfold IsMPMJobShopSchedule; decide

/-- The schedule has makespan `5`. -/
private theorem mixed_feasible : MultiPurposeJobShopThreeJobsFeasible (mixed 5) :=
  ⟨mixedMachine, mixedStart, mixed_schedule, by decide⟩

/-- The decision problem accepts the encoding of `mixed 5`. -/
example : multiPurposeJobShopThreeJobsDec (bitEncode (mixed 5)) = true := by
  simp [multiPurposeJobShopThreeJobsDec, mixed_wellFormed, mixed_feasible]

/-! ### Load on one machine -/

/-- Jobs of lengths `2` and `3` that must both use machine `1`, and a job of length `1` on
machine `2`, with the bound `K`. -/
private abbrev load (K : ℕ) : MPMJobShopInstance :=
  (2, [[(2, [1])], [(3, [1])], [(1, [2])]], K)

private theorem load_wellFormed : WellFormed (load 5) ∧ WellFormed (load 4) := by
  unfold WellFormed MPMWellFormed; decide

/-- Machine `1` processes job `0` during `[0, 2)` and job `1` during `[2, 5)`. -/
private theorem load_five_feasible : MultiPurposeJobShopThreeJobsFeasible (load 5) :=
  ⟨byIndex fun j _ => if j = 2 then 2 else 1, byIndex fun j _ => if j = 1 then 2 else 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩

/-- With the bound `4` the two jobs on machine `1` cannot both finish: they do not overlap, so
one ends at `5` or later. -/
private theorem load_four_infeasible : ¬ MultiPurposeJobShopThreeJobsFeasible (load 4) := by
  rintro ⟨a, σ, ⟨ha, hm, -⟩, hK⟩
  let t₀ : Operation (load 4) := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  let t₁ : Operation (load 4) := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  have h₀ : a t₀ ∈ [1] := ha t₀
  have h₁ : a t₁ ∈ [1] := ha t₁
  have ho : σ t₀ + 2 ≤ σ t₁ ∨ σ t₁ + 3 ≤ σ t₀ :=
    hm t₀ t₁ (by decide)
      ((List.mem_singleton.1 h₀).trans (List.mem_singleton.1 h₁).symm) (by decide) (by decide)
  have d₀ : σ t₀ + 2 ≤ 4 := hK ⟨0, by decide⟩ ⟨0, by decide⟩ rfl
  have d₁ : σ t₁ + 3 ≤ 4 := hK ⟨1, by decide⟩ ⟨0, by decide⟩ rfl
  omega

/-- The decision problem accepts the bound `5` and rejects the bound `4`, both instances being
well formed. -/
example :
    multiPurposeJobShopThreeJobsDec (bitEncode (load 5)) = true ∧
      multiPurposeJobShopThreeJobsDec (bitEncode (load 4)) = false := by
  simp [multiPurposeJobShopThreeJobsDec, load_wellFormed.1, load_wellFormed.2, load_five_feasible,
    load_four_infeasible]

/-! ### Job order -/

/-- Job `0` runs `2` units on machine `1`, then `3` units on machine `2`; jobs `1` and `2` are
single operations of length `0`; the bound is `K`. -/
private abbrev chain (K : ℕ) : MPMJobShopInstance :=
  (2, [[(2, [1]), (3, [2])], [(0, [1])], [(0, [2])]], K)

private theorem chain_wellFormed : WellFormed (chain 5) ∧ WellFormed (chain 4) := by
  unfold WellFormed MPMWellFormed; decide

/-- Each operation on an eligible machine: the two operations of job `0` on different machines. -/
private def chainMachine {i : MPMJobShopInstance} : Operation i → ℕ :=
  byIndex fun j k => if j = 1 ∨ (j = 0 ∧ k = 0) then 1 else 2

/-- Starting everything at time `0` meets each operation's eligibility and keeps operations of
positive length on one machine apart, but the second operation of job `0` starts before the
first completes, so it is no schedule. -/
example :
    (∀ t : Operation (chain 5), chainMachine t ∈ eligible (chain 5) t) ∧
      ∀ t t' : Operation (chain 5), t ≠ t' → chainMachine t = chainMachine t' →
        0 < opLength (chain 5) t → 0 < opLength (chain 5) t' →
          0 + opLength (chain 5) t ≤ 0 ∨ 0 + opLength (chain 5) t' ≤ 0 :=
  ⟨by decide, by decide⟩

example : ¬ IsMPMJobShopSchedule (chain 5) chainMachine (byIndex fun _ _ => 0) := by
  unfold IsMPMJobShopSchedule; decide

/-- Starting the second operation of job `0` at `2` makes it a schedule of makespan `5`. -/
private theorem chain_five_feasible : MultiPurposeJobShopThreeJobsFeasible (chain 5) :=
  ⟨chainMachine, byIndex fun j k => if j = 0 ∧ k = 1 then 2 else 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩

/-- With the bound `4` job `0` cannot finish: its operations of lengths `2` and `3` run one
after the other, although on different machines. -/
private theorem chain_four_infeasible : ¬ MultiPurposeJobShopThreeJobsFeasible (chain 4) := by
  rintro ⟨a, σ, ⟨-, -, hp⟩, hK⟩
  let t₀ : Operation (chain 4) := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  let t₁ : Operation (chain 4) := ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
  have hp₀ : σ t₀ + 2 ≤ σ t₁ := hp ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
  have d₁ : σ t₁ + 3 ≤ 4 := hK ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
  omega

/-- The decision problem accepts the bound `5` and rejects the bound `4`. -/
example :
    multiPurposeJobShopThreeJobsDec (bitEncode (chain 5)) = true ∧
      multiPurposeJobShopThreeJobsDec (bitEncode (chain 4)) = false := by
  simp [multiPurposeJobShopThreeJobsDec, chain_wellFormed.1, chain_wellFormed.2,
    chain_five_feasible, chain_four_infeasible]

/-- Two consecutive operations of one job may use the same machine, one after the other. -/
private abbrev twice : MPMJobShopInstance := (2, [[(1, [1]), (1, [1])], [(0, [2])], [(0, [2])]], 2)

private theorem twice_wellFormed : WellFormed twice := by
  unfold WellFormed MPMWellFormed; decide

private theorem twice_feasible : MultiPurposeJobShopThreeJobsFeasible twice :=
  ⟨byIndex fun j _ => if j = 0 then 1 else 2, byIndex fun j k => if j = 0 ∧ k = 1 then 1 else 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩

example : multiPurposeJobShopThreeJobsDec (bitEncode twice) = true := by
  simp [multiPurposeJobShopThreeJobsDec, twice_wellFormed, twice_feasible]

/-! ### Choosing machines -/

/-- Two jobs of length `2`, each eligible for both machines, and a job of length `0`, with the
bound `K`. -/
private abbrev flex (K : ℕ) : MPMJobShopInstance :=
  (2, [[(2, [1, 2])], [(2, [1, 2])], [(0, [1])]], K)

/-- The same jobs, each restricted to machine `1`. -/
private abbrev fixed (K : ℕ) : MPMJobShopInstance := (2, [[(2, [1])], [(2, [1])], [(0, [1])]], K)

private theorem flex_wellFormed : WellFormed (flex 2) := by
  unfold WellFormed MPMWellFormed; decide

private theorem fixed_wellFormed : WellFormed (fixed 2) := by
  unfold WellFormed MPMWellFormed; decide

/-- Running the two long jobs on different machines meets the bound `2`. -/
private theorem flex_feasible : MultiPurposeJobShopThreeJobsFeasible (flex 2) :=
  ⟨byIndex fun j _ => if j = 1 then 2 else 1, byIndex fun _ _ => 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩

/-- Every schedule of `flex 2` that meets the bound runs the two long jobs on different
machines: the choice of machine is part of the schedule. -/
example (a σ : Operation (flex 2) → ℕ) (hs : IsMPMJobShopSchedule (flex 2) a σ)
    (hK : ∀ j (k : Fin ((flex 2).2.1.get j).length), k.1 + 1 = ((flex 2).2.1.get j).length →
      σ ⟨j, k⟩ + opLength (flex 2) ⟨j, k⟩ ≤ (flex 2).2.2) :
    a ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ ≠ a ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩ := by
  intro h
  let t₀ : Operation (flex 2) := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  let t₁ : Operation (flex 2) := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  have ho : σ t₀ + 2 ≤ σ t₁ ∨ σ t₁ + 2 ≤ σ t₀ :=
    hs.2.1 t₀ t₁ (by decide) h (by decide) (by decide)
  have d₀ : σ t₀ + 2 ≤ 2 := hK ⟨0, by decide⟩ ⟨0, by decide⟩ rfl
  have d₁ : σ t₁ + 2 ≤ 2 := hK ⟨1, by decide⟩ ⟨0, by decide⟩ rfl
  omega

/-- Restricted to machine `1`, the two long jobs run one after the other and miss the bound. -/
private theorem fixed_infeasible : ¬ MultiPurposeJobShopThreeJobsFeasible (fixed 2) := by
  rintro ⟨a, σ, ⟨ha, hm, -⟩, hK⟩
  let t₀ : Operation (fixed 2) := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  let t₁ : Operation (fixed 2) := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  have h₀ : a t₀ ∈ [1] := ha t₀
  have h₁ : a t₁ ∈ [1] := ha t₁
  have ho : σ t₀ + 2 ≤ σ t₁ ∨ σ t₁ + 2 ≤ σ t₀ :=
    hm t₀ t₁ (by decide)
      ((List.mem_singleton.1 h₀).trans (List.mem_singleton.1 h₁).symm) (by decide) (by decide)
  have d₀ : σ t₀ + 2 ≤ 2 := hK ⟨0, by decide⟩ ⟨0, by decide⟩ rfl
  have d₁ : σ t₁ + 2 ≤ 2 := hK ⟨1, by decide⟩ ⟨0, by decide⟩ rfl
  omega

/-- The decision problem accepts the flexible instance and rejects the restricted one. -/
example :
    multiPurposeJobShopThreeJobsDec (bitEncode (flex 2)) = true ∧
      multiPurposeJobShopThreeJobsDec (bitEncode (fixed 2)) = false := by
  simp [multiPurposeJobShopThreeJobsDec, flex_wellFormed, flex_feasible, fixed_infeasible]

/-! ### Operations of length `0` -/

/-- A job of length `4` on machine `1` and two jobs of length `0` on machine `1`. -/
private abbrev inner : MPMJobShopInstance := (2, [[(4, [1])], [(0, [1])], [(0, [1])]], 4)

private theorem inner_wellFormed : WellFormed inner := by
  unfold WellFormed MPMWellFormed; decide

/-- Both operations of length `0` start at `2`, strictly inside `[0, 4)`, where job `0` runs on
the same machine, and share their start and machine with each other. -/
private def innerStart : Operation inner → ℕ := byIndex fun j _ => if j = 0 then 0 else 2

private theorem inner_feasible : MultiPurposeJobShopThreeJobsFeasible inner :=
  ⟨byIndex fun _ _ => 1, innerStart, by unfold IsMPMJobShopSchedule; decide, by decide⟩

/-- Without the positivity conditions the schedule would be rejected: the operation of job `1`
neither starts after job `0` completes nor completes before job `0` starts. -/
example :
    ¬ (innerStart ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ + opLength inner ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
        ≤ innerStart ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩ ∨
      innerStart ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩ + opLength inner ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
        ≤ innerStart ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩) := by
  decide

example : multiPurposeJobShopThreeJobsDec (bitEncode inner) = true := by
  simp [multiPurposeJobShopThreeJobsDec, inner_wellFormed, inner_feasible]

/-- Three jobs of operations of length `0`, the last with two operations, and the bound `0`. -/
private abbrev zeros (m : ℕ) : MPMJobShopInstance :=
  (m, [[(0, [1])], [(0, [2])], [(0, [1, 2]), (0, [2])]], 0)

private theorem zeros_wellFormed : WellFormed (zeros 2) := by
  unfold WellFormed MPMWellFormed; decide

/-- All operations start at `0`; the machine count does not matter. -/
private theorem zeros_feasible :
    MultiPurposeJobShopThreeJobsFeasible (zeros 2) ∧
      MultiPurposeJobShopThreeJobsFeasible (zeros 3) :=
  ⟨⟨byIndex fun j _ => if j = 0 then 1 else 2, byIndex fun _ _ => 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩,
    ⟨byIndex fun j _ => if j = 0 then 1 else 2, byIndex fun _ _ => 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩⟩

/-- The decision problem accepts the bound `0` when every operation has length `0`. -/
example : multiPurposeJobShopThreeJobsDec (bitEncode (zeros 2)) = true := by
  simp [multiPurposeJobShopThreeJobsDec, zeros_wellFormed, zeros_feasible.1]

/-- Job `0` runs `2` units on machine `1`, then an operation of length `0` on machine `2`; the
bound is `K`. -/
private abbrev late (K : ℕ) : MPMJobShopInstance :=
  (2, [[(2, [1]), (0, [2])], [(0, [1])], [(0, [2])]], K)

private theorem late_wellFormed : WellFormed (late 2) ∧ WellFormed (late 1) := by
  unfold WellFormed MPMWellFormed; decide

private theorem late_two_feasible : MultiPurposeJobShopThreeJobsFeasible (late 2) :=
  ⟨chainMachine, byIndex fun j k => if j = 0 ∧ k = 1 then 2 else 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩

/-- An operation of length `0` still waits for its job's previous operation, and still has to
complete by the bound: with the bound `1` it cannot. -/
private theorem late_one_infeasible : ¬ MultiPurposeJobShopThreeJobsFeasible (late 1) := by
  rintro ⟨a, σ, ⟨-, -, hp⟩, hK⟩
  let t₀ : Operation (late 1) := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  let t₁ : Operation (late 1) := ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
  have hp₀ : σ t₀ + 2 ≤ σ t₁ := hp ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
  have d₁ : σ t₁ + 0 ≤ 1 := hK ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
  omega

example :
    multiPurposeJobShopThreeJobsDec (bitEncode (late 2)) = true ∧
      multiPurposeJobShopThreeJobsDec (bitEncode (late 1)) = false := by
  simp [multiPurposeJobShopThreeJobsDec, late_wellFormed.1, late_wellFormed.2, late_two_feasible,
    late_one_infeasible]

/-! ### Malformed instances -/

/-- The machine count is checked against the one passed to `MPMWellFormed`, and machine labels
against the instance's machine count. -/
example :
    MPMWellFormed 3 ((3, [[(1, [3])]], 0) : MPMJobShopInstance) ∧
      ¬ MPMWellFormed 2 ((3, [[(1, [3])]], 0) : MPMJobShopInstance) := by
  unfold MPMWellFormed; decide

/-- Three machines: feasible, but malformed, so rejected. `zeros 2` is well formed. -/
example :
    MultiPurposeJobShopThreeJobsFeasible (zeros 3) ∧ ¬ WellFormed (zeros 3) ∧
      multiPurposeJobShopThreeJobsDec (bitEncode (zeros 3)) = false := by
  have hw : ¬ WellFormed (zeros 3) := by unfold WellFormed MPMWellFormed; decide
  exact ⟨zeros_feasible.2, hw, by simp [multiPurposeJobShopThreeJobsDec, hw]⟩

/-- Two jobs: feasible, but malformed, so rejected. -/
example :
    MultiPurposeJobShopThreeJobsFeasible ((2, [[(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) ∧
      multiPurposeJobShopThreeJobsDec
        (bitEncode ((2, [[(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance)) = false := by
  have hw : ¬ WellFormed ((2, [[(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) := by
    unfold WellFormed MPMWellFormed; decide
  refine ⟨⟨byIndex fun j _ => j + 1, byIndex fun _ _ => 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩, ?_⟩
  simp [multiPurposeJobShopThreeJobsDec, hw]

/-- Four jobs: feasible, but malformed, so rejected. -/
example :
    MultiPurposeJobShopThreeJobsFeasible
        ((2, [[(0, [1])], [(0, [2])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) ∧
      multiPurposeJobShopThreeJobsDec (bitEncode
        ((2, [[(0, [1])], [(0, [2])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance)) =
        false := by
  have hw : ¬ WellFormed
      ((2, [[(0, [1])], [(0, [2])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) := by
    unfold WellFormed MPMWellFormed; decide
  refine ⟨⟨byIndex fun j _ => if j % 2 = 0 then 1 else 2, byIndex fun _ _ => 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩, ?_⟩
  simp [multiPurposeJobShopThreeJobsDec, hw]

/-- A job with no operations: feasible, as the job has nothing to schedule, but malformed, so
rejected. -/
example :
    MultiPurposeJobShopThreeJobsFeasible
        ((2, [[], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) ∧
      multiPurposeJobShopThreeJobsDec
        (bitEncode ((2, [[], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance)) = false := by
  have hw : ¬ WellFormed ((2, [[], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) := by
    unfold WellFormed MPMWellFormed; decide
  refine ⟨⟨byIndex fun j _ => j, byIndex fun _ _ => 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩, ?_⟩
  simp [multiPurposeJobShopThreeJobsDec, hw]

/-- Machine label `0`: feasible on that label, but malformed, so rejected. -/
example :
    MultiPurposeJobShopThreeJobsFeasible
        ((2, [[(0, [0])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) ∧
      multiPurposeJobShopThreeJobsDec
        (bitEncode ((2, [[(0, [0])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance)) =
          false := by
  have hw : ¬ WellFormed ((2, [[(0, [0])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) := by
    unfold WellFormed MPMWellFormed; decide
  refine ⟨⟨byIndex fun j _ => j, byIndex fun _ _ => 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩, ?_⟩
  simp [multiPurposeJobShopThreeJobsDec, hw]

/-- Machine label `3` with two machines: feasible on that label, but malformed, so rejected. -/
example :
    MultiPurposeJobShopThreeJobsFeasible
        ((2, [[(0, [3])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) ∧
      multiPurposeJobShopThreeJobsDec
        (bitEncode ((2, [[(0, [3])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance)) =
          false := by
  have hw : ¬ WellFormed ((2, [[(0, [3])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) := by
    unfold WellFormed MPMWellFormed; decide
  refine ⟨⟨byIndex fun j _ => if j = 0 then 3 else j, byIndex fun _ _ => 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩, ?_⟩
  simp [multiPurposeJobShopThreeJobsDec, hw]

/-- An operation with no eligible machine: malformed, and also infeasible, as it has no machine
to run on; rejected. -/
example :
    ¬ WellFormed ((2, [[(0, [])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) ∧
      ¬ MultiPurposeJobShopThreeJobsFeasible
        ((2, [[(0, [])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) ∧
      multiPurposeJobShopThreeJobsDec
        (bitEncode ((2, [[(0, [])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance)) = false := by
  have hw : ¬ WellFormed ((2, [[(0, [])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) := by
    unfold WellFormed MPMWellFormed; decide
  have hf : ¬ MultiPurposeJobShopThreeJobsFeasible
      ((2, [[(0, [])], [(0, [1])], [(0, [2])]], 0) : MPMJobShopInstance) := by
    rintro ⟨a, σ, ⟨ha, -, -⟩, -⟩
    have h : a ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ ∈ ([] : List ℕ) := ha _
    simp at h
  exact ⟨hw, hf, by simp [multiPurposeJobShopThreeJobsDec, hw]⟩

/-- A machine listed twice in an eligible set is allowed. -/
private abbrev dup : MPMJobShopInstance := (2, [[(1, [1, 1])], [(0, [2])], [(0, [2, 1, 2])]], 1)

private theorem dup_wellFormed : WellFormed dup := by
  unfold WellFormed MPMWellFormed; decide

private theorem dup_feasible : MultiPurposeJobShopThreeJobsFeasible dup :=
  ⟨byIndex fun j _ => if j = 0 then 1 else 2, byIndex fun _ _ => 0,
    by unfold IsMPMJobShopSchedule; decide, by decide⟩

example : multiPurposeJobShopThreeJobsDec (bitEncode dup) = true := by
  simp [multiPurposeJobShopThreeJobsDec, dup_wellFormed, dup_feasible]

/-! ### Encoding -/

/-- Decoding an encoded instance gives it back. -/
example : bitDecode (bitEncode (mixed 5)) = some (mixed 5) := by simp

/-- The decision problem rejects the empty bitstring, which decodes to no instance. -/
example : multiPurposeJobShopThreeJobsDec [] = false := by
  have h : bitDecode (α := MPMJobShopInstance) [] = none := rfl
  simp [multiPurposeJobShopThreeJobsDec, h]

end MetaMathlibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobs
