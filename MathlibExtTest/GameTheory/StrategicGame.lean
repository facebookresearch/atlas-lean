/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.StrategicGame
import Mathlib.Tactic

/-! Examples for `MathlibExt.GameTheory.StrategicGame`: a pure Nash equilibrium of the
prisoner's dilemma, matching pennies without a pure equilibrium, a constant game in
which ties make every profile an equilibrium, and the nonempty-strategy requirement. -/

namespace MathlibExtTest.GameTheory.StrategicGame

section Examples

open MathlibExt.GameTheory

/-- Prisoner's dilemma with `true` = defect and `false` = cooperate. -/
def prisonersDilemma : StrategicGame (Fin 2) (fun _ => Bool) where
  payoff := fun i σ =>
    match σ 0, σ 1 with
    | false, false => 3
    | false, true => if i = 0 then 0 else 5
    | true, false => if i = 0 then 5 else 0
    | true, true => 1
  strategy_nonempty := fun _ => inferInstance

theorem prisonersDilemma_nash_defect :
    prisonersDilemma.IsNash (fun _ => true) := by
  rw [StrategicGame.isNash_iff_update_le]
  intro i t
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  fin_cases i <;> cases t <;> simp [prisonersDilemma, h01, h10]

theorem prisonersDilemma_not_nash_cooperate :
    ¬ prisonersDilemma.IsNash (fun _ => false) := by
  rw [StrategicGame.isNash_iff_update_le]
  intro h
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hcon := h 0 true
  simp [prisonersDilemma, h10] at hcon
  norm_num at hcon

/-- Matching pennies: player 0 wins on match, player 1 wins on mismatch. -/
def matchingPennies : StrategicGame (Fin 2) (fun _ => Bool) where
  payoff := fun i σ =>
    if i = 0 then (if σ 0 = σ 1 then 1 else -1) else (if σ 0 = σ 1 then -1 else 1)
  strategy_nonempty := fun _ => inferInstance

theorem matchingPennies_no_pure_nash : ∀ σ, ¬ matchingPennies.IsNash σ := by
  intro σ h
  rw [StrategicGame.isNash_iff_update_le] at h
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  cases s0 : σ 0 <;> cases s1 : σ 1
  · have hcon := h 1 true
    simp [matchingPennies, s0, s1, h01, h10] at hcon
    norm_num at hcon
  · have hcon := h 0 true
    simp [matchingPennies, s0, s1, h10] at hcon
    norm_num at hcon
  · have hcon := h 0 false
    simp [matchingPennies, s0, s1, h10] at hcon
    norm_num at hcon
  · have hcon := h 1 false
    simp [matchingPennies, s0, s1, h01, h10] at hcon
    norm_num at hcon

/-- Constant game: every profile is a Nash equilibrium. -/
def constantGame : StrategicGame (Fin 2) (fun _ => Bool) where
  payoff := fun _ _ => 0
  strategy_nonempty := fun _ => inferInstance

theorem constantGame_all_nash : ∀ σ, constantGame.IsNash σ := by
  intro σ
  rw [StrategicGame.isNash_iff_update_le]
  intro i t
  simp [constantGame]

/-- A player with no strategies does not give a strategic game. -/
theorem not_strategicGame_of_isEmpty_strategies :
    IsEmpty (StrategicGame (Fin 1) (fun _ => Empty)) :=
  ⟨fun G => (G.strategy_nonempty 0).elim Empty.elim⟩

/-- Every strategic game has a strategy profile. -/
theorem strategicGame_nonempty_profile {ι : Type*} {S : ι → Type*}
    (G : StrategicGame ι S) : Nonempty (∀ i, S i) :=
  ⟨fun i => (G.strategy_nonempty i).some⟩

end Examples

#print axioms MathlibExt.GameTheory.StrategicGame.isNash_iff_not_lt_update
#print axioms MathlibExt.GameTheory.StrategicGame.isNash_iff_update_le

end MathlibExtTest.GameTheory.StrategicGame
