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

example : RandCompetitive ToyP
    { μ := (⟨MeasureTheory.Measure.dirac true, by infer_instance⟩ :
        MeasureTheory.ProbabilityMeasure Bool),
      strat := fun _ => AlwaysTrue } 1 0 :=
  (randCompetitive_dirac_iff ToyP AlwaysTrue true 1 0).mpr toy_competitive

example : (2 : ENNReal)
    ≤ optProfit ToyP (fun τ => (τ.length : NNReal)) [true, false] := by
  have h := le_optProfit ToyP (fun τ => (τ.length : NNReal))
    (σ := [true, false]) (τ := [(true, true), (false, true)]) trivial rfl
  simpa [ENNReal.coe_natCast] using h

theorem toy_profit_opt (σ : List Bool) :
    optProfit ToyP (fun τ => (τ.length : NNReal)) σ
      = (σ.length : ENNReal) := by
  apply le_antisymm
  · unfold optProfit
    apply iSup₂_le
    intro τ hτ
    dsimp only
    have hlen : τ.length = σ.length := by rw [← hτ.2, List.length_map]
    rw [hlen, ENNReal.coe_natCast]
  · have h := le_optProfit ToyP (fun τ => (τ.length : NNReal)) (σ := σ)
      (τ := run AlwaysTrue σ) (alwaysTrue_feasible σ trivial)
      (run_map_fst AlwaysTrue σ)
    have hlen : (run AlwaysTrue σ).length = σ.length :=
      runFrom_length AlwaysTrue [] σ
    simpa [hlen, ENNReal.coe_natCast] using h

theorem toy_profitCompetitive : ProfitCompetitive ToyP
    (fun τ => (τ.length : NNReal)) AlwaysTrue 1 0 := by
  refine ⟨zero_le_one, le_rfl, le_rfl, alwaysTrue_feasible, fun σ _ => ?_⟩
  have hlen : (run AlwaysTrue σ).length = σ.length :=
    runFrom_length AlwaysTrue [] σ
  simp only [toy_profit_opt, hlen, ENNReal.coe_natCast, ENNReal.ofReal_one,
    one_mul, ENNReal.ofReal_zero, add_zero, le_refl]

example : ProfitCompetitive ToyP (fun τ => (τ.length : NNReal)) AlwaysTrue (1 / 2) 3 :=
  ProfitCompetitive.mono ToyP _ AlwaysTrue toy_profitCompetitive (by norm_num)
    (by norm_num) (by norm_num)

/-- The always-`false` strategy. -/
def AlwaysFalse : Strategy Bool Bool := fun _ => false

example : RandCompetitive ToyP
    { μ := (⟨MeasureTheory.Measure.dirac true, by infer_instance⟩ :
        MeasureTheory.ProbabilityMeasure Bool),
      strat := fun _ => (Simulation.refl ToyP).F AlwaysTrue } 1 0 := by
  have hdirac : RandCompetitive ToyP
      { μ := (⟨MeasureTheory.Measure.dirac true, by infer_instance⟩ :
          MeasureTheory.ProbabilityMeasure Bool),
        strat := fun _ => AlwaysTrue } 1 0 :=
    (randCompetitive_dirac_iff ToyP AlwaysTrue true 1 0).mpr toy_competitive
  have h := Simulation.randCompetitive_transfer (Simulation.refl ToyP) _
    hdirac (fun σ _ => by
      show Measurable (fun _ : Bool => ENNReal.ofReal
        (algCost ToyP ((Simulation.refl ToyP).F AlwaysTrue) σ))
      exact measurable_const)
  simpa [Simulation.refl] using h

example : RandProfitCompetitive ToyP (fun τ => (τ.length : NNReal))
    { μ := (⟨MeasureTheory.Measure.dirac true, by infer_instance⟩ :
        MeasureTheory.ProbabilityMeasure Bool),
      strat := fun _ => AlwaysTrue } 1 0 := by
  have hexp : ∀ σ : List Bool,
      (∫⁻ ω, ((((run ((fun _ : Bool => AlwaysTrue) ω) σ).length : ℕ) : NNReal) : ENNReal)
        ∂MeasureTheory.Measure.dirac true)
        = ((((run AlwaysTrue σ).length : ℕ) : NNReal) : ENNReal) := by
    intro σ
    change ∫⁻ _ : Bool, ((((run AlwaysTrue σ).length : ℕ) : NNReal) : ENNReal)
      ∂MeasureTheory.Measure.dirac true = _
    exact MeasureTheory.lintegral_dirac' true measurable_const
  obtain ⟨hρ0, hρ1, hb0, hA, hineq⟩ := toy_profitCompetitive
  refine ⟨hρ0, hρ1, hb0, fun _ => hA, fun σ hσ => ?_⟩
  refine ⟨?_, ?_⟩
  · show Measurable
      (fun _ : Bool => (((run AlwaysTrue σ).length : NNReal) : ENNReal))
    exact measurable_const
  · have h := hineq σ hσ
    simpa [hexp] using h

example : optProfit ToyP (fun _ => 0) [true, false] = 0 := by
  apply le_antisymm
  · unfold optProfit
    apply iSup₂_le
    intro τ _
    simp
  · exact zero_le

example : ProfitCompetitive ToyP (fun _ => 0) AlwaysTrue 1 0 := by
  refine ⟨zero_le_one, le_rfl, le_rfl, alwaysTrue_feasible, fun σ _ => ?_⟩
  have hopt : optProfit ToyP (fun _ => (0 : NNReal)) σ = 0 := by
    apply le_antisymm
    · unfold optProfit
      apply iSup₂_le
      intro τ _
      simp
    · exact zero_le
  rw [hopt]
  simp

example : ¬ ProfitCompetitive ToyP
    (fun τ => ((τ.countP (fun p => p.2)) : NNReal)) AlwaysFalse 1 0 := by
  intro h
  obtain ⟨-, -, -, -, hineq⟩ := h
  have hle := hineq [true] trivial
  have hrun : run AlwaysFalse [true] = [(true, false)] := rfl
  rw [hrun] at hle
  have hopt : (1 : ENNReal) ≤ optProfit ToyP
      (fun τ => ((τ.countP (fun p => p.2)) : NNReal)) [true] := by
    have h := le_optProfit ToyP (fun τ => ((τ.countP (fun p => p.2)) : NNReal))
      (σ := [true]) (τ := [(true, true)]) trivial rfl
    simpa [ENNReal.coe_natCast] using h
  simp only [ENNReal.ofReal_one, one_mul, ENNReal.ofReal_zero, add_zero] at hle
  have hcount : List.countP (fun p : Bool × Bool => p.2) [(true, false)] = 0 := rfl
  rw [hcount] at hle
  simp only [Nat.cast_zero] at hle
  have h10 : (1 : ENNReal) ≤ 0 := le_trans hopt hle
  simp at h10

/-- Fair coin over `Bool`: half-and-half mixture of the Dirac measures at
`true` and `false`, answering `true` on `true` and `false` on `false`. -/
noncomputable def twoSeed : RandStrategy Bool Bool Bool where
  μ := (⟨(2⁻¹ : ENNReal) • MeasureTheory.Measure.dirac true
      + (2⁻¹ : ENNReal) • MeasureTheory.Measure.dirac false,
    by
      refine ⟨?_⟩
      rw [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ true),
        MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ false),
        smul_eq_mul, mul_one]
      exact ENNReal.inv_two_add_inv_two⟩ :
    MeasureTheory.ProbabilityMeasure Bool)
  strat := fun ω => if ω then AlwaysTrue else AlwaysFalse

theorem twoSeed_coe : (twoSeed.μ : MeasureTheory.Measure Bool)
    = (2⁻¹ : ENNReal) • MeasureTheory.Measure.dirac true
      + (2⁻¹ : ENNReal) • MeasureTheory.Measure.dirac false := rfl

/-- Mismatch problem: every sequence legal, every trace feasible, cost is
the number of request/answer disagreements. -/
def MatchP : OnlineProblem Bool Bool where
  legal := fun _ => True
  legal_nil := trivial
  legal_prefix := fun {_ _} _ => trivial
  feasible := fun _ => True
  feasible_nil := trivial
  feasible_prefix := fun {_ _} _ => trivial
  feasible_requests := fun {_} _ => trivial
  nonblocking := fun {_ _} _ _ => ⟨true, trivial⟩
  cost := fun τ => ((τ.countP (fun p : Bool × Bool => p.1 != p.2)) : ℝ)
  cost_nonneg := fun _ => Nat.cast_nonneg _

example : expectedCost MatchP twoSeed [true] = 2⁻¹ := by
  have htrue : (∫⁻ ω, ENNReal.ofReal (algCost MatchP (twoSeed.strat ω) [true])
      ∂MeasureTheory.Measure.dirac true)
      = ENNReal.ofReal (algCost MatchP (twoSeed.strat true) [true]) :=
    MeasureTheory.lintegral_dirac' true (measurable_of_finite _)
  have hfalse : (∫⁻ ω, ENNReal.ofReal (algCost MatchP (twoSeed.strat ω) [true])
      ∂MeasureTheory.Measure.dirac false)
      = ENNReal.ofReal (algCost MatchP (twoSeed.strat false) [true]) :=
    MeasureTheory.lintegral_dirac' false (measurable_of_finite _)
  have hrun_true : run AlwaysTrue [true] = [(true, true)] := rfl
  have hrun_false : run AlwaysFalse [true] = [(true, false)] := rfl
  have hcount_true :
      ([(true, true)].countP (fun p : Bool × Bool => p.1 != p.2)) = 0 := rfl
  have hcount_false :
      ([(true, false)].countP (fun p : Bool × Bool => p.1 != p.2)) = 1 := rfl
  have hcost_true : algCost MatchP (twoSeed.strat true) [true] = 0 := by
    show MatchP.cost (run AlwaysTrue [true]) = 0
    rw [hrun_true]
    show ((([(true, true)].countP (fun p : Bool × Bool => p.1 != p.2)) : ℕ) : ℝ)
      = 0
    rw [hcount_true]
    norm_num
  have hcost_false : algCost MatchP (twoSeed.strat false) [true] = 1 := by
    show MatchP.cost (run AlwaysFalse [true]) = 1
    rw [hrun_false]
    show ((([(true, false)].countP (fun p : Bool × Bool => p.1 != p.2)) : ℕ) : ℝ)
      = 1
    rw [hcount_false]
    norm_num
  unfold expectedCost
  rw [twoSeed_coe, MeasureTheory.lintegral_add_measure,
    MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_smul_measure,
    htrue, hfalse, hcost_true, hcost_false]
  simp only [ENNReal.ofReal_zero, ENNReal.ofReal_one, smul_eq_mul, mul_zero,
    mul_one, zero_add]

theorem countP_run_true (σ : List Bool) :
    (run AlwaysTrue σ).countP (fun p : Bool × Bool => p.2) = σ.length := by
  have gen : ∀ (past σ : List Bool),
      (runFrom AlwaysTrue past σ).countP (fun p : Bool × Bool => p.2)
        = σ.length := by
    intro past σ
    induction σ generalizing past with
    | nil => rfl
    | cons r σ ih =>
      have hhead : (fun p : Bool × Bool => p.2) (r, AlwaysTrue (past ++ [r]))
          = true := rfl
      have hcons : runFrom AlwaysTrue past (r :: σ)
          = (r, AlwaysTrue (past ++ [r]))
            :: runFrom AlwaysTrue (past ++ [r]) σ := rfl
      rw [hcons, List.countP_cons_of_pos hhead, ih, List.length_cons]
  exact gen [] σ

theorem countP_run_false (σ : List Bool) :
    (run AlwaysFalse σ).countP (fun p : Bool × Bool => p.2) = 0 := by
  have gen : ∀ (past σ : List Bool),
      (runFrom AlwaysFalse past σ).countP (fun p : Bool × Bool => p.2) = 0 := by
    intro past σ
    induction σ generalizing past with
    | nil => rfl
    | cons r σ ih =>
      have hhead :
          ¬ (fun p : Bool × Bool => p.2) (r, AlwaysFalse (past ++ [r]))
            = true := by
        simp [AlwaysFalse]
      have hcons : runFrom AlwaysFalse past (r :: σ)
          = (r, AlwaysFalse (past ++ [r]))
            :: runFrom AlwaysFalse (past ++ [r]) σ := rfl
      rw [hcons, List.countP_cons_of_neg hhead, ih]
  exact gen [] σ

theorem count_profit_opt (σ : List Bool) :
    optProfit ToyP (fun τ => ((τ.countP (fun p => p.2)) : NNReal)) σ
      = (σ.length : ENNReal) := by
  apply le_antisymm
  · unfold optProfit
    apply iSup₂_le
    intro τ hτ
    dsimp only
    have hlen : τ.length = σ.length := by rw [← hτ.2, List.length_map]
    have hle : τ.countP (fun p : Bool × Bool => p.2) ≤ σ.length := by
      rw [← hlen]
      exact List.countP_le_length
    calc ((((τ.countP (fun p : Bool × Bool => p.2)) : NNReal)) : ENNReal)
        = ((τ.countP (fun p : Bool × Bool => p.2) : ℕ) : ENNReal) :=
          ENNReal.coe_natCast _
      _ ≤ ((σ.length : ℕ) : ENNReal) := Nat.cast_le.mpr hle
  · have h := le_optProfit ToyP (fun τ => ((τ.countP (fun p => p.2)) : NNReal))
      (σ := σ) (τ := run AlwaysTrue σ) (alwaysTrue_feasible σ trivial)
      (run_map_fst AlwaysTrue σ)
    simpa [countP_run_true, ENNReal.coe_natCast] using h

example : RandProfitCompetitive ToyP (fun τ => ((τ.countP (fun p => p.2)) : NNReal))
    twoSeed (1 / 2) 0 := by
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp
  have htrue : ∀ σ : List Bool,
      (∫⁻ ω, ((((run (twoSeed.strat ω) σ).countP (fun p => p.2)) : NNReal)
          : ENNReal)
        ∂MeasureTheory.Measure.dirac true)
        = ((((run (twoSeed.strat true) σ).countP (fun p => p.2)) : NNReal)
          : ENNReal) := by
    intro σ
    exact MeasureTheory.lintegral_dirac' true (measurable_of_finite _)
  have hfalse : ∀ σ : List Bool,
      (∫⁻ ω, ((((run (twoSeed.strat ω) σ).countP (fun p => p.2)) : NNReal)
          : ENNReal)
        ∂MeasureTheory.Measure.dirac false)
        = ((((run (twoSeed.strat false) σ).countP (fun p => p.2)) : NNReal)
          : ENNReal) := by
    intro σ
    exact MeasureTheory.lintegral_dirac' false (measurable_of_finite _)
  have hstrat_true : ∀ σ : List Bool,
      ((run (twoSeed.strat true) σ).countP (fun p => p.2)) = σ.length := by
    intro σ
    show (run AlwaysTrue σ).countP (fun p : Bool × Bool => p.2) = σ.length
    exact countP_run_true σ
  have hstrat_false : ∀ σ : List Bool,
      ((run (twoSeed.strat false) σ).countP (fun p => p.2)) = 0 := by
    intro σ
    show (run AlwaysFalse σ).countP (fun p : Bool × Bool => p.2) = 0
    exact countP_run_false σ
  refine ⟨by norm_num, by norm_num, le_rfl, fun ω => ?_, fun σ _ => ⟨?_, ?_⟩⟩
  · intro σ _
    trivial
  · exact measurable_of_finite _
  · rw [count_profit_opt]
    show ENNReal.ofReal (1 / 2) * (σ.length : ENNReal) ≤
      (∫⁻ ω, ((((run (twoSeed.strat ω) σ).countP (fun p => p.2)) : NNReal)
          : ENNReal)
        ∂↑twoSeed.μ) + ENNReal.ofReal 0
    rw [twoSeed_coe, MeasureTheory.lintegral_add_measure,
      MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_smul_measure,
      htrue σ, hfalse σ, hstrat_true σ, hstrat_false σ, hhalf,
      ENNReal.ofReal_zero]
    simp

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

example : RandCompetitive (ScaledToyP 6 (by norm_num))
    { μ := (⟨MeasureTheory.Measure.dirac true, by infer_instance⟩ :
        MeasureTheory.ProbabilityMeasure Bool),
      strat := fun _ => sim61.F AlwaysTrue } 6 41 := by
  have hdirac : RandCompetitive ToyP
      { μ := (⟨MeasureTheory.Measure.dirac true, by infer_instance⟩ :
          MeasureTheory.ProbabilityMeasure Bool),
        strat := fun _ => AlwaysTrue } 1 0 :=
    (randCompetitive_dirac_iff ToyP AlwaysTrue true 1 0).mpr toy_competitive
  have h := Simulation.randCompetitive_transfer sim61 _ hdirac
    (fun σ _ => by
      show Measurable (fun _ : Bool => ENNReal.ofReal
        (algCost (ScaledToyP 6 (by norm_num)) (sim61.F AlwaysTrue) σ))
      exact measurable_const)
  have e1 : sim61.a * 1 * sim61.d = 6 := by
    norm_num [sim61, Simulation.comp, sim63, sim31]
  have e2 : sim61.a * 1 * sim61.q + sim61.a * 0 + sim61.p = 41 := by
    norm_num [sim61, Simulation.comp, sim63, sim31]
  rw [e1, e2] at h
  exact h

end Cslib.Algorithms.Lean.Online.CompetitiveFrameworkTest

end

public section
