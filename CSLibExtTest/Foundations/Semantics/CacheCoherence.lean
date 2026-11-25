/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Foundations.Semantics.CacheCoherence

/-! # Boundary fixtures for the single-location cache coherence model -/

namespace CSLibExt.CacheCoherence

private def exclusive : TokenAllocation 2 := ⟨fun c => if c = 0 then 2 else 0, 0⟩

private def writer (before after : ℕ) : Epoch 2 ℕ :=
  exclusive.epoch 2 before (fun _ => before) (fun _ => after)

private theorem exclusive_valid : exclusive.ValidBudget 2 := by
  unfold TokenAllocation.ValidBudget
  decide

-- Core 0 holds both tokens. It can read and write, while core 1 can do neither.
example : (writer 7 13).SWMR ∧
    (writer 7 13).canWrite 0 = true ∧ (writer 7 13).readValue 0 = some 7 ∧
    (writer 7 13).canWrite 1 = false ∧ (writer 7 13).readValue 1 = none :=
  ⟨TokenAllocation.swmr_of_validBudget exclusive_valid _ _ _, rfl, rfl, rfl, rfl⟩

private def split : TokenAllocation 2 := ⟨fun _ => 1, 0⟩

private theorem split_valid : split.ValidBudget 2 := by
  unfold TokenAllocation.ValidBudget
  decide

private def readers (first second : ℕ) : Epoch 2 ℕ :=
  split.epoch 2 first (fun c => if c = 0 then first else second) (fun h => False.elim (by
    obtain ⟨c, hc⟩ := h
    exact (by decide : (1 : ℕ) ≠ 2) hc))

-- The preceding read–write epoch ended with 13. Both cores now have one token and no
-- write permission. The logical start value is 13, but core 1's readable copy is 23.
example : split.ValidBudget 2 ∧ (readers 13 23).SWMR ∧
    (∀ c, (readers 13 23).canWrite c = false) ∧
    (readers 13 23).readValue 0 = some 13 ∧ (readers 13 23).readValue 1 = some 23 ∧
    (readers 13 23).DataValue 7 [writer 7 13] ∧ ¬ (readers 13 23).ReadAgreement := by
  refine ⟨split_valid, TokenAllocation.swmr_of_validBudget split_valid _ _ _,
    fun _ => rfl, rfl, rfl, rfl, ?_⟩
  intro h
  exact (by decide : (13 : ℕ) ≠ 23) (h (a := 0) (b := 1) rfl rfl)

private theorem readers_match (v : ℕ) : (readers v v).MatchesStart := by
  intro c x hx
  have hv : v = x := by simpa [readers, split, TokenAllocation.epoch] using hx
  exact hv.symm

-- All tokens can be unassigned. The start-value check is not vacuous when nobody can read.
example :
    let idle : TokenAllocation 2 := ⟨fun _ => 0, 2⟩
    let e := idle.epoch 2 13 (fun _ => 13) (fun _ => 13)
    e.SWMR ∧ (∀ c, e.readValue c = none) ∧ ¬ e.DataValue 7 [] := by
  intro idle e
  have h : idle.ValidBudget 2 := by
    unfold TokenAllocation.ValidBudget
    decide
  refine ⟨TokenAllocation.swmr_of_validBudget h _ _ _, fun _ => rfl, ?_⟩
  change (13 : ℕ) ≠ 7
  decide

-- With no earlier read–write epoch, even a nonempty history of readers uses the initial value.
example : (readers 7 7).DataValue 7 [] ∧ (readers 7 7).DataValue 7 [readers 7 7] ∧
    ¬ (readers 13 13).DataValue 7 [] ∧ (readers 7 7).ReadAgreement := by
  refine ⟨rfl, rfl, ?_, Epoch.readAgreement_of_matchesStart (readers_match 7)⟩
  change (13 : ℕ) ≠ 7
  decide

-- The most recent write epoch takes precedence over both the initial value and older writes.
private def past : List (Epoch 2 ℕ) :=
  [writer 7 13, readers 13 13, writer 13 19, readers 19 19]

example : (readers 19 19).DataValue 7 past ∧ 19 = Epoch.carriedValue 7 past := by
  have hData : (readers 19 19).DataValue 7 past := rfl
  have h := TokenAllocation.epoch_coherence split_valid 19 (fun c => if c = 0 then 19 else 19)
    (fun h => False.elim (by
      obtain ⟨c, hc⟩ := h
      exact (by decide : (1 : ℕ) ≠ 2) hc)) 7 past
  exact ⟨hData, (h.2 hData (readers_match 19)).2 1 19 rfl⟩

end CSLibExt.CacheCoherence
