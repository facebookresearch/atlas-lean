/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Basic.ENNReal.Basic
public import CSLibExt.Algorithms.Lean.Online.CompetitiveFramework
import Mathlib.Tactic

@[expose] public section

namespace Cslib.Algorithms.Lean.Online.CompetitiveFrameworkTest

open Cslib.Algorithms.Lean.Online.CompetitiveFramework

/-- Tiny toy problem: boolean requests and answers, every sequence legal,
every trace feasible, cost is trace length. -/
def ToyP : OnlineProblem Bool Bool where
  legal := fun _ => True
  legal_nil := trivial
  legal_prefix := fun {_ _} _ => trivial
  feasible := fun _ => True
  feasible_nil := trivial
  feasible_prefix := fun {_ _} _ => trivial
  feasible_requests := fun {_} _ => trivial
  nonblocking := fun {_ _} _ _ => ⟨true, trivial⟩
  cost := fun τ => (τ.length : ℝ)
  cost_nonneg := fun _ => Nat.cast_nonneg _

theorem toy_cost (τ : List (Bool × Bool)) : ToyP.cost τ = (τ.length : ℝ) := rfl

/-- The always-`true` strategy. -/
def AlwaysTrue : Strategy Bool Bool := fun _ => true

theorem alwaysTrue_feasible : StrategyFeasible ToyP AlwaysTrue := by
  intro σ _
  trivial

example : run AlwaysTrue [true, false] = [(true, true), (false, true)] := rfl

example : optCost ToyP [true, false] ≤ ENNReal.ofReal 2 := by
  have h := optCost_le ToyP (σ := [true, false])
    (τ := [(true, true), (false, true)]) trivial rfl
  rw [toy_cost] at h
  simpa using h

theorem toy_optCost (σ : List Bool) :
    optCost ToyP σ = ENNReal.ofReal (σ.length : ℝ) := by
  apply le_antisymm
  · have h := optCost_le ToyP (σ := σ) (τ := run AlwaysTrue σ)
      (alwaysTrue_feasible σ trivial) (run_map_fst AlwaysTrue σ)
    have hlen : (run AlwaysTrue σ).length = σ.length :=
      runFrom_length AlwaysTrue [] σ
    rw [toy_cost, hlen] at h
    exact h
  · unfold optCost
    apply le_iInf₂
    intro τ hτ
    rw [toy_cost]
    have hlen : τ.length = σ.length := by rw [← hτ.2, List.length_map]
    rw [hlen]

theorem toy_competitive : Competitive ToyP AlwaysTrue 1 0 := by
  refine ⟨zero_le_one, le_rfl, alwaysTrue_feasible, fun σ _ => ?_⟩
  have hlen : (run AlwaysTrue σ).length = σ.length :=
    runFrom_length AlwaysTrue [] σ
  have halg : algCost ToyP AlwaysTrue σ = (σ.length : ℝ) :=
    (toy_cost _).trans (by rw [hlen])
  rw [halg, toy_optCost, ENNReal.ofReal_one, ENNReal.ofReal_zero, one_mul,
    add_zero]

example : Competitive ToyP AlwaysTrue 2 5 :=
  Competitive.mono ToyP AlwaysTrue toy_competitive (by norm_num) (by norm_num)

/-- Two-state toggle machine: answers the current state, negates the state
on a `true` request and keeps it otherwise. -/
def Toggle : StateMachine Bool Bool Bool where
  init := false
  step := fun s r => (s, if r then s.not else s)

example : run Toggle.toStrategy [true, true, false]
    = [(true, false), (true, true), (false, false)] := by
  rw [StateMachine.run_toStrategy]
  rfl

example (σ : List Bool) : ∃ τ : List (Bool × Bool), ToyP.feasible τ ∧
    τ.map Prod.fst = σ ∧ optCost ToyP σ = ENNReal.ofReal (ToyP.cost τ) :=
  exists_optimal_of_natCost ToyP (fun τ => ⟨τ.length, toy_cost τ⟩) trivial

example : Competitive ToyP ((Simulation.refl ToyP).F AlwaysTrue) 1 0 := by
  have h := Simulation.competitive_transfer (Simulation.refl ToyP) AlwaysTrue
    toy_competitive
  simpa [Simulation.refl] using h

#print axioms run_nil
#print axioms runFrom_length
#print axioms runFrom_map_fst
#print axioms run_map_fst
#print axioms runFrom_append
#print axioms run_prefix
#print axioms optCost_le
#print axioms exists_feasible_trace
#print axioms optCost_ne_top
#print axioms optCost_alg_le
#print axioms AdditiveCompetitive.of_strict
#print axioms Competitive.mono
#print axioms StrictLowerBound.of_additive
#print axioms not_strictCompetitive_of_strictLowerBound
#print axioms not_additiveCompetitive_of_additiveLowerBound

end Cslib.Algorithms.Lean.Online.CompetitiveFrameworkTest

end

public section
