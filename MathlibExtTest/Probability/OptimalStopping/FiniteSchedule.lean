/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.OptimalStopping.FiniteSchedule

/-! # Examples of stopping rules on finite schedules -/

open MeasureTheory MetaMathlibExt

private def informationAtTwo : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq t := if 2 ≤ t then ⊤ else ⊥
  mono' := by
    intro s t hst
    by_cases hs : 2 ≤ s
    · simp [hs, hs.trans hst]
    · simp [hs]
  le' _ := le_top

-- The schedule has unequal gaps, and the index depends on the revealed outcome.
example : ∃ τ : Bool → ℕ,
    IsStoppingTime informationAtTwo (fun ω => τ ω) ∧ τ false = 2 ∧ τ true = 9 := by
  let e : Fin 3 → ℕ := fun j => if j = 0 then 2 else if j = 1 then 5 else 9
  have he : StrictMono e := by
    change ∀ j k : Fin 3, j < k → e j < e k
    decide
  have he_min : ∀ j : Fin 3, 2 ≤ e j := by decide
  obtain ⟨E, hdate⟩ := finite_schedule_stopping_times informationAtTwo e he
  let i : Bool → Fin 3 := fun ω => if ω then 2 else 0
  have hi (k : ℕ) :
      MeasurableSet[informationAtTwo (e ⟨min k 2, Nat.lt_succ_of_le (min_le_right _ _)⟩)]
        {ω | (↑(i ω).val : WithTop ℕ) ≤ ↑k} := by
    let j : Fin 3 := ⟨min k 2, Nat.lt_succ_of_le (min_le_right _ _)⟩
    change MeasurableSet[if 2 ≤ e j then ⊤ else ⊥] {ω | (↑(i ω).val : WithTop ℕ) ≤ ↑k}
    rw [ite_eq_left (he_min j)]
    exact MeasurableSpace.measurableSet_top
  let τ := E ⟨i, hi⟩
  exact ⟨τ.val, τ.property.1, (hdate ⟨i, hi⟩ false).trans rfl, (hdate ⟨i, hi⟩ true).trans rfl⟩

-- On a singleton schedule the image of any sampled stopping index is the terminal date.
example {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι] (F : Filtration ι m) (T : ι) :
    ∃ τ : Ω → ι, IsStoppingTime F (fun ω => τ ω) ∧ ∀ ω, τ ω = T := by
  have he : StrictMono (fun _ : Fin 1 => T) := by
    intro i j hij
    exact (not_lt_of_ge (Subsingleton.elim j i).le hij).elim
  obtain ⟨E, hdate⟩ := finite_schedule_stopping_times F (fun _ : Fin 1 => T) he
  let τ := E ⟨fun _ => 0, fun _ => MeasurableSet.const _⟩
  exact ⟨τ.val, τ.property.1, hdate _⟩
