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
#print axioms exists_strategyFeasible

example : ∃ A : Strategy Bool Bool, StrategyFeasible ToyP A :=
  exists_strategyFeasible ToyP

def ScaledToyP (k : ℝ) (hk : 0 ≤ k) : OnlineProblem Bool Bool where
  legal := fun _ => True
  legal_nil := trivial
  legal_prefix := fun {_ _} _ => trivial
  feasible := fun _ => True
  feasible_nil := trivial
  feasible_prefix := fun {_ _} _ => trivial
  feasible_requests := fun {_} _ => trivial
  nonblocking := fun {_ _} _ _ => ⟨true, trivial⟩
  cost := fun τ => k * (τ.length : ℝ)
  cost_nonneg := fun _ => mul_nonneg hk (Nat.cast_nonneg _)

def sim63 : Simulation (ScaledToyP 6 (by norm_num)) (ScaledToyP 3 (by norm_num)) where
  F := fun A h => !(A h)
  G := fun _ τ => τ.map (fun p => (p.1, !p.2))
  legal_mono := fun _ _ => trivial
  F_feasible := fun _ _ _ _ => trivial
  G_feasible := by
    intro σ τ _ hστ
    refine ⟨trivial, ?_⟩
    have hfun : (Prod.fst ∘ fun p : Bool × Bool => (p.1, !p.2)) = Prod.fst := by
      funext p
      rfl
    simpa [hfun] using hστ
  a := 2
  p := 1
  d := 1
  q := 4
  ha := by norm_num
  hp := by norm_num
  hd := by norm_num
  hq := by norm_num
  costF := by
    intro A σ _
    simp only [algCost, ScaledToyP]
    have hlenF : (run (fun h : List Bool => !(A h)) σ).length = σ.length :=
      runFrom_length _ [] σ
    have hlenA : (run A σ).length = σ.length := runFrom_length _ [] σ
    rw [hlenF, hlenA]
    have e : (6 : ℝ) * (σ.length : ℝ) = 2 * (3 * (σ.length : ℝ)) := by ring
    rw [e, ENNReal.ofReal_mul zero_le_two]
    apply le_add_of_nonneg_right
    positivity
  costG := by
    intro _ τ _ _
    simp only [ScaledToyP, List.length_map]
    have hn : (0 : ℝ) ≤ (τ.length : ℝ) := Nat.cast_nonneg _
    have hle : (3 : ℝ) * (τ.length : ℝ) ≤ 1 * (6 * (τ.length : ℝ)) + 4 := by
      linarith
    have hnn : (0 : ℝ) ≤ 1 * (6 * (τ.length : ℝ)) := by positivity
    calc ENNReal.ofReal ((3 : ℝ) * (τ.length : ℝ))
        ≤ ENNReal.ofReal (1 * (6 * (τ.length : ℝ)) + 4) :=
          ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal 1 * ENNReal.ofReal ((6 : ℝ) * (τ.length : ℝ)) +
          ENNReal.ofReal 4 := by
        rw [ENNReal.ofReal_add hnn (by norm_num : (0 : ℝ) ≤ 4),
          ENNReal.ofReal_mul zero_le_one]

def sim31 : Simulation (ScaledToyP 3 (by norm_num)) ToyP where
  F := fun A h => !(A h)
  G := fun _ τ => τ.map (fun p => (p.1, !p.2))
  legal_mono := fun _ _ => trivial
  F_feasible := fun _ _ _ _ => trivial
  G_feasible := by
    intro σ τ _ hστ
    refine ⟨trivial, ?_⟩
    have hfun : (Prod.fst ∘ fun p : Bool × Bool => (p.1, !p.2)) = Prod.fst := by
      funext p
      rfl
    simpa [hfun] using hστ
  a := 3
  p := 2
  d := 1
  q := 2
  ha := by norm_num
  hp := by norm_num
  hd := by norm_num
  hq := by norm_num
  costF := by
    intro A σ _
    simp only [algCost, ScaledToyP, ToyP]
    have hlenF : (run (fun h : List Bool => !(A h)) σ).length = σ.length :=
      runFrom_length _ [] σ
    have hlenA : (run A σ).length = σ.length := runFrom_length _ [] σ
    rw [hlenF, hlenA]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    apply le_add_of_nonneg_right
    positivity
  costG := by
    intro _ τ _ _
    simp only [ScaledToyP, ToyP, List.length_map]
    have hn : (0 : ℝ) ≤ (τ.length : ℝ) := Nat.cast_nonneg _
    have hle : (τ.length : ℝ) ≤ 1 * (3 * (τ.length : ℝ)) + 2 := by linarith
    have hnn : (0 : ℝ) ≤ 1 * (3 * (τ.length : ℝ)) := by positivity
    calc ENNReal.ofReal (τ.length : ℝ)
        ≤ ENNReal.ofReal (1 * (3 * (τ.length : ℝ)) + 2) :=
          ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal 1 * ENNReal.ofReal ((3 : ℝ) * (τ.length : ℝ)) +
          ENNReal.ofReal 2 := by
        rw [ENNReal.ofReal_add hnn (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul zero_le_one]

def sim61 := sim63.comp sim31

example : sim61.a = 6 := by norm_num [sim61, Simulation.comp, sim63, sim31]
example : sim61.p = 5 := by norm_num [sim61, Simulation.comp, sim63, sim31]
example : sim61.d = 1 := by norm_num [sim61, Simulation.comp, sim63, sim31]
example : sim61.q = 6 := by norm_num [sim61, Simulation.comp, sim63, sim31]
example : sim61.F AlwaysTrue = AlwaysTrue := rfl
example : sim61.G [true, false] [(true, true), (false, false)] =
    [(true, true), (false, false)] := rfl
example : run (sim61.F AlwaysTrue) [true, false] = [(true, true), (false, true)] :=
  rfl

example : Competitive (ScaledToyP 6 (by norm_num)) (sim61.F AlwaysTrue) 6 41 := by
  have h := Simulation.competitive_transfer sim61 AlwaysTrue toy_competitive
  have e1 : sim61.a * 1 * sim61.d = 6 := by
    norm_num [sim61, Simulation.comp, sim63, sim31]
  have e2 : sim61.a * 1 * sim61.q + sim61.a * 0 + sim61.p = 41 := by
    norm_num [sim61, Simulation.comp, sim63, sim31]
  rw [e1, e2] at h
  exact h

end Cslib.Algorithms.Lean.Online.CompetitiveFrameworkTest

end

public section
