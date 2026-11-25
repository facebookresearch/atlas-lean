/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.NormalForm
import Mathlib.Tactic.Linarith

@[expose] public section

set_option autoImplicit false

/-!
# Normal-form adapter tests

- T1 prisoner's dilemma: defection strictly dominant, all-defect unique Nash.
- T2 cost round trip on the constant game.
- T3 every action weakly dominant in the constant game.
- T4 single-peak game: action `false` weakly dominant, all-false Nash,
  all-true Nash.
-/

namespace MathlibExtTest.GameTheory.NormalForm

open MathlibExt.GameTheory

/-- Prisoner's dilemma with `true` = defect. -/
def prisonersDilemma : StrategicGame (Fin 2) (fun _ => Bool) where
  payoff := fun i σ =>
    match σ 0, σ 1 with
    | false, false => 3
    | false, true => if i = 0 then 0 else 5
    | true, false => if i = 0 then 5 else 0
    | true, true => 1
  strategy_nonempty := fun _ => inferInstance

/-- Constant game: payoff `0` everywhere. -/
def constantGame : StrategicGame (Fin 2) (fun _ => Bool) where
  payoff := fun _ _ => 0
  strategy_nonempty := fun _ => inferInstance

/-- Single-peak game: payoff `1` at all-`false`, else `0`. -/
def peakGame : StrategicGame (Fin 2) (fun _ => Bool) where
  payoff := fun _ σ =>
    match σ 0, σ 1 with
    | false, false => 1
    | _, _ => 0
  strategy_nonempty := fun _ => inferInstance

/-- T1: defection strictly dominant for player `0`. -/
theorem prisonersDilemma_true_isStrictlyDominant_zero :
    @DominantStrategy.IsStrictlyDominant (Fin 2) _ (fun _ => Bool)
      prisonersDilemma.strategy_nonempty prisonersDilemma.payoff 0 true := by
  intro τ t ht
  cases t
  · cases h : τ 1 <;> simp [prisonersDilemma, h]; linarith
  · exact absurd rfl ht

/-- T1: defection strictly dominant for player `1`. -/
theorem prisonersDilemma_true_isStrictlyDominant_one :
    @DominantStrategy.IsStrictlyDominant (Fin 2) _ (fun _ => Bool)
      prisonersDilemma.strategy_nonempty prisonersDilemma.payoff 1 true := by
  intro τ t ht
  cases t
  · cases h : τ 0 <;> simp [prisonersDilemma, h]; linarith
  · exact absurd rfl ht

/-- T1: defection strictly dominant for each player. -/
theorem prisonersDilemma_true_isStrictlyDominant_all (i : Fin 2) :
    @DominantStrategy.IsStrictlyDominant (Fin 2) _ (fun _ => Bool)
      prisonersDilemma.strategy_nonempty prisonersDilemma.payoff i true :=
  match i with
  | 0 => prisonersDilemma_true_isStrictlyDominant_zero
  | 1 => prisonersDilemma_true_isStrictlyDominant_one

/-- T1: all-defect is Nash, via C5. -/
theorem prisonersDilemma_allTrue_isNash :
    prisonersDilemma.IsNash (fun _ => true) :=
  StrategicGame.isNash_of_forall_isStrictlyDominant prisonersDilemma
    (fun _ => true) prisonersDilemma_true_isStrictlyDominant_all

/-- T1: all-defect is the unique Nash, via C5. -/
theorem prisonersDilemma_eq_allTrue_of_isNash (τ : ∀ _ : Fin 2, Bool)
    (hτ : prisonersDilemma.IsNash τ) : τ = fun _ => true :=
  StrategicGame.eq_of_isNash_of_forall_isStrictlyDominant prisonersDilemma
    (fun _ => true) τ prisonersDilemma_true_isStrictlyDominant_all hτ

/-- T2: cost round trip on the constant game, via C1. -/
theorem constantGame_ofCost_roundtrip :
    StrategicGame.ofCost constantGame.cost constantGame.strategy_nonempty =
      constantGame :=
  StrategicGame.ofCost_cost constantGame

/-- T3: every action weakly dominant in the constant game. -/
theorem constantGame_all_isWeaklyDominant (i : Fin 2) (a : Bool) :
    constantGame.IsWeaklyDominant i a := by
  intro τ t
  simp [constantGame]

/-- T4: action `false` weakly dominant for player `0`. -/
theorem peakGame_false_isWeaklyDominant_zero :
    peakGame.IsWeaklyDominant 0 false := by
  intro τ t
  cases t <;> cases h : τ 1 <;> simp [peakGame, h]

/-- T4: action `false` weakly dominant for player `1`. -/
theorem peakGame_false_isWeaklyDominant_one :
    peakGame.IsWeaklyDominant 1 false := by
  intro τ t
  cases t <;> cases h : τ 0 <;> simp [peakGame, h]

/-- T4: action `false` weakly dominant for each player. -/
theorem peakGame_false_isWeaklyDominant_all (i : Fin 2) :
    peakGame.IsWeaklyDominant i ((fun _ => false) i) :=
  match i with
  | 0 => peakGame_false_isWeaklyDominant_zero
  | 1 => peakGame_false_isWeaklyDominant_one

/-- T4: all-`false` is Nash, via C7. -/
theorem peakGame_allFalse_isNash : peakGame.IsNash (fun _ => false) :=
  StrategicGame.isNash_of_forall_isWeaklyDominant peakGame (fun _ => false)
    peakGame_false_isWeaklyDominant_all

/-- T4: all-`true` is also Nash. -/
theorem peakGame_allTrue_isNash : peakGame.IsNash (fun _ => true) := by
  rw [StrategicGame.isNash_iff_update_le peakGame (fun _ => true)]
  rw [Fin.forall_fin_two]
  constructor
  · intro t
    cases t <;> simp [peakGame]
  · intro t
    cases t <;> simp [peakGame]

end MathlibExtTest.GameTheory.NormalForm
