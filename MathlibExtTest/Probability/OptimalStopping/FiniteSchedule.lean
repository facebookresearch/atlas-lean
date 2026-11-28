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

private def nonuniformDates (j : Fin 3) : ℕ := if j = 0 then 1 else if j = 1 then 2 else 9

private theorem nonuniformDates_strictMono : StrictMono nonuniformDates := by
  change ∀ j k : Fin 3, j < k → nonuniformDates j < nonuniformDates k
  decide

-- The schedule starts before the outcome is revealed at its second date.
example :
    finiteScheduleFiltration informationAtTwo nonuniformDates nonuniformDates_strictMono.monotone
      0 = ⊥ ∧
    finiteScheduleFiltration informationAtTwo nonuniformDates nonuniformDates_strictMono.monotone
      1 = ⊤ :=
  ⟨(finiteScheduleFiltration_apply _ _ _ (0 : Fin 3)).trans rfl,
    (finiteScheduleFiltration_apply _ _ _ (1 : Fin 3)).trans rfl⟩

-- The original filtration reveals information only after the last sampled date.
private def informationAtTen : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq t := if 10 ≤ t then ⊤ else ⊥
  mono' := by
    intro s t hst
    by_cases hs : 10 ≤ s
    · simp [hs, hs.trans hst]
    · simp [hs]
  le' _ := le_top

-- The sampled filtration stays at the terminal algebra even when the original filtration grows.
example :
    finiteScheduleFiltration informationAtTen nonuniformDates nonuniformDates_strictMono.monotone
      2 = ⊥ ∧
    finiteScheduleFiltration informationAtTen nonuniformDates nonuniformDates_strictMono.monotone
      3 = ⊥ ∧
    (⊥ : MeasurableSpace Bool) < informationAtTen 10 := by
  refine ⟨rfl, rfl, ?_⟩
  change (⊥ : MeasurableSpace Bool) < ⊤
  apply lt_of_le_of_ne bot_le
  intro h
  have hMeas : MeasurableSet[(⊥ : MeasurableSpace Bool)] ({true} : Set Bool) :=
    h.symm ▸ MeasurableSpace.measurableSet_top
  rcases MeasurableSpace.measurableSet_bot_iff.mp hMeas with he | hu
  · have ht : true ∈ ({true} : Set Bool) := by simp
    have hn : true ∉ (∅ : Set Bool) := by simp
    exact hn (he ▸ ht)
  · have hf : false ∉ ({true} : Set Bool) := by simp
    exact hf (hu.symm ▸ Set.mem_univ false)

-- Start with a stopping date and check that the inverse recovers both indices.
example : ∃ i : Bool → Fin 3,
    IsStoppingTime
      (finiteScheduleFiltration informationAtTwo nonuniformDates nonuniformDates_strictMono.monotone)
      (fun ω => (i ω).val) ∧ i false = 1 ∧ i true = 2 := by
  let τ : Bool → ℕ := fun ω => if ω then 9 else 2
  have hτ : IsStoppingTime informationAtTwo (fun ω => τ ω) := by
    intro t
    change MeasurableSet[if 2 ≤ t then ⊤ else ⊥] {ω | (τ ω : WithTop ℕ) ≤ ↑t}
    by_cases ht : 2 ≤ t
    · rw [ite_eq_left ht]
      exact MeasurableSpace.measurableSet_top
    · rw [ite_eq_right ht]
      have hempty : {ω | (τ ω : WithTop ℕ) ≤ ↑t} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, Nat.cast_withTop, WithTop.coe_le_coe]
        cases ω <;> simp [τ] <;> omega
      rw [hempty]
      exact @MeasurableSet.empty Bool ⊥
  have hrange (ω : Bool) : τ ω ∈ Set.range nonuniformDates := by
    cases ω
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  let E := finiteScheduleStoppingEquiv informationAtTwo nonuniformDates nonuniformDates_strictMono
  let i := E.symm ⟨τ, hτ, hrange⟩
  have hdate (ω : Bool) : nonuniformDates (i.val ω) = τ ω := by
    calc
      nonuniformDates (i.val ω) = (E i).val ω :=
        (finiteScheduleStoppingEquiv_apply _ _ _ i ω).symm
      _ = τ ω := congrArg (fun s => s.val ω) (E.apply_symm_apply ⟨τ, hτ, hrange⟩)
  exact ⟨i.val, i.property, nonuniformDates_strictMono.injective ((hdate false).trans rfl),
    nonuniformDates_strictMono.injective ((hdate true).trans rfl)⟩

-- On a singleton schedule the image of any sampled stopping index is the terminal date.
example {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι] (F : Filtration ι m) (T : ι) :
    ∃ τ : Ω → ι, IsStoppingTime F (fun ω => τ ω) ∧ ∀ ω, τ ω = T := by
  have he : StrictMono (fun _ : Fin 1 => T) := by
    intro i j hij
    exact (not_lt_of_ge (Subsingleton.elim j i).le hij).elim
  obtain ⟨E, hdate⟩ := finite_schedule_stopping_times F (fun _ : Fin 1 => T) he
  let τ := E ⟨fun _ => 0, fun _ => MeasurableSet.const _⟩
  exact ⟨τ.val, τ.property.1, hdate _⟩
