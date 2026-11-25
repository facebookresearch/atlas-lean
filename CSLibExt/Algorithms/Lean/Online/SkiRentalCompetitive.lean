/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Algorithms.Lean.Online.CompetitiveFramework
public import CSLibExt.Algorithms.Lean.Online.SkiRental
import Mathlib.Tactic

@[expose] public section

namespace Cslib.Algorithms.Lean.Online.CompetitiveFramework

open SkiRental

/-- First buy day (1-based) recorded by a trace, if any. -/
def firstBuyDay (τ : List (Unit × Bool)) : Option ℕ :=
  let idx := τ.findIdx (fun p => p.2)
  if idx < τ.length then some (idx + 1) else none

/-- Ski rental as an online problem: one unit request per day; the answer
records whether the skis are bought that day; feasible traces buy at most
once; cost is the native ski-rental cost of the recorded buy day. -/
def skiProblem (B : ℕ) : OnlineProblem Unit Bool where
  legal := fun _ => True
  legal_nil := trivial
  legal_prefix := fun _ => trivial
  feasible := fun τ => (τ.filter (fun p => p.2)).length ≤ 1
  feasible_nil := by simp
  feasible_prefix := by
    intro τ τ' h
    simp only [List.filter_append, List.length_append] at h ⊢
    omega
  feasible_requests := fun _ => trivial
  nonblocking := by
    intro τ r h _
    refine ⟨false, ?_⟩
    have hnil : ([(r, false)].filter (fun p => p.2)) = [] := by simp
    change ((τ ++ [(r, false)]).filter (fun p => p.2)).length ≤ 1
    rw [List.filter_append, hnil, List.append_nil]
    exact h
  cost := fun τ => (SkiRental.cost B (firstBuyDay τ) τ.length : ℝ)
  cost_nonneg := fun _ => by positivity

/-- The causal strategy that buys exactly according to a native ski-rental
strategy: buy when the season reaches the prescribed day. -/
def skiStrategy (s : SkiRental.Strategy) : Strategy Unit Bool :=
  fun σ => match s with
    | some t => σ.length == t
    | none => false

/-- Rewrite form of `firstBuyDay`. -/
private theorem firstBuyDay_eq (τ : List (Unit × Bool)) :
    firstBuyDay τ = if τ.findIdx (fun p => p.2) < τ.length
      then some (τ.findIdx (fun p => p.2) + 1) else none := rfl

/-- Rewrite form of the cost field of `skiProblem`. -/
private theorem cost_skiProblem (B : ℕ) (τ : List (Unit × Bool)) :
    (skiProblem B).cost τ
      = (SkiRental.cost B (firstBuyDay τ) τ.length : ℝ) := rfl

/-- Rewrite form of the feasibility predicate of `skiProblem`. -/
private theorem feasible_skiProblem (B : ℕ) (τ : List (Unit × Bool)) :
    (skiProblem B).feasible τ
      = ((τ.filter (fun p => p.2)).length ≤ 1) := rfl

/-- Rewrite form of `run`. -/
private theorem run_eq (A : Strategy Unit Bool) (σ : List Unit) :
    run A σ = runFrom A [] σ := rfl

/-- Runs preserve input length. -/
private theorem length_run (A : Strategy Unit Bool) (σ : List Unit) :
    (run A σ).length = σ.length := runFrom_length _ [] _

/-- Rewrite form of `algCost`. -/
private theorem algCost_eq (P : OnlineProblem Unit Bool)
    (A : Strategy Unit Bool) (σ : List Unit) :
    algCost P A σ = P.cost (run A σ) := rfl

/-- Rewrite form of `optCost`. -/
private theorem optCost_eq (P : OnlineProblem Unit Bool) (σ : List Unit) :
    optCost P σ = ⨅ τ ∈ {τ : List (Unit × Bool) |
        P.feasible τ ∧ τ.map Prod.fst = σ},
      ENNReal.ofReal (P.cost τ) := rfl

/-- The first buy day recorded by a `skiStrategy (some t)` run. -/
private theorem findIdx_runFrom_some (t : ℕ) (past σ : List Unit) :
    (runFrom (skiStrategy (some t)) past σ).findIdx (fun p => p.2)
      = if past.length + 1 ≤ t ∧ t ≤ past.length + σ.length
        then t - (past.length + 1) else σ.length := by
  induction σ generalizing past with
  | nil =>
      simp only [runFrom, List.findIdx_nil, List.length_nil]
      rw [ite_eq_right (by omega)]
  | cons r σ ih =>
      simp only [runFrom, List.findIdx_cons, skiStrategy]
      have hl : (past ++ [r]).length = past.length + 1 := by simp
      rw [hl]
      by_cases h : past.length + 1 = t
      · have hpos : (((past.length + 1) == t) = true) := by
          rw [h, beq_self_eq_true]
        rw [ite_eq_left hpos]
        have c2 : t ≤ past.length + (r :: σ).length := by
          simp only [List.length_cons]
          omega
        rw [ite_eq_left ⟨h.le, c2⟩]
        omega
      · have hneg : ¬ (((past.length + 1) == t) = true) := by
          rw [beq_iff_eq]
          exact h
        rw [ite_eq_right hneg, ih (past ++ [r])]
        simp only [hl, List.length_cons]
        split_ifs with h1 h2
        · omega
        · omega
        · omega
        · omega

/-- A `skiStrategy none` run never buys. -/
private theorem findIdx_runFrom_none (past σ : List Unit) :
    (runFrom (skiStrategy none) past σ).findIdx (fun p => p.2)
      = σ.length := by
  induction σ generalizing past with
  | nil => simp only [runFrom, List.findIdx_nil, List.length_nil]
  | cons r σ ih =>
      simp only [runFrom, List.findIdx_cons, skiStrategy]
      rw [ite_eq_right Bool.false_ne_true, ih (past ++ [r])]
      simp only [List.length_cons]

/-- Run form of `findIdx_runFrom_some`. -/
private theorem findIdx_run_some (t : ℕ) (σ : List Unit) :
    (run (skiStrategy (some t)) σ).findIdx (fun p => p.2)
      = if 1 ≤ t ∧ t ≤ σ.length then t - 1 else σ.length := by
  have h := findIdx_runFrom_some t [] σ
  change (runFrom (skiStrategy (some t)) [] σ).findIdx (fun p => p.2) = _
  rw [h]
  simp only [List.length_nil, Nat.zero_add]

/-- Run form of `findIdx_runFrom_none`. -/
private theorem findIdx_run_none (σ : List Unit) :
    (run (skiStrategy none) σ).findIdx (fun p => p.2) = σ.length := by
  change (runFrom (skiStrategy none) [] σ).findIdx (fun p => p.2) = _
  exact findIdx_runFrom_none [] σ

/-- A `skiStrategy (some t)` run buys at most once: no buy can follow
day `t`. -/
private theorem filter_runFrom_some_le (t : ℕ) (past σ : List Unit) :
    ((runFrom (skiStrategy (some t)) past σ).filter (fun p => p.2)).length
      ≤ (if t ≤ past.length then 0 else 1) := by
  induction σ generalizing past with
  | nil =>
      simp only [runFrom, List.filter_nil, List.length_nil]
      split_ifs <;> omega
  | cons r σ ih =>
      simp only [runFrom, List.filter_cons, skiStrategy]
      have hl : (past ++ [r]).length = past.length + 1 := by simp
      rw [hl]
      by_cases h : past.length + 1 = t
      · have hpos : (((past.length + 1) == t) = true) := by
          rw [h, beq_self_eq_true]
        rw [ite_eq_left hpos, List.length_cons]
        have hcond : ¬ (t ≤ past.length) := by omega
        rw [ite_eq_right hcond]
        have htail := ih (past ++ [r])
        rw [hl, ite_eq_left h.ge] at htail
        omega
      · have hneg : ¬ (((past.length + 1) == t) = true) := by
          rw [beq_iff_eq]
          exact h
        rw [ite_eq_right hneg]
        have htail := ih (past ++ [r])
        rw [hl] at htail
        have hcond : (t ≤ past.length + 1) ↔ (t ≤ past.length) := by omega
        simp only [hcond] at htail
        exact htail

/-- A `skiStrategy none` run buys never. -/
private theorem filter_runFrom_none (past σ : List Unit) :
    ((runFrom (skiStrategy none) past σ).filter (fun p => p.2)).length
      = 0 := by
  induction σ generalizing past with
  | nil => simp only [runFrom, List.filter_nil, List.length_nil]
  | cons r σ ih =>
      simp only [runFrom, List.filter_cons, skiStrategy]
      rw [ite_eq_right Bool.false_ne_true, ih (past ++ [r])]

theorem skiStrategy_feasible (B : ℕ) (s : SkiRental.Strategy) :
    StrategyFeasible (skiProblem B) (skiStrategy s) := by
  intro σ _
  cases s with
  | none =>
      rw [feasible_skiProblem, run_eq, filter_runFrom_none]
      exact zero_le_one
  | some t =>
      rw [feasible_skiProblem, run_eq]
      have h := filter_runFrom_some_le t [] σ
      simp only [List.length_nil] at h
      refine le_trans h ?_
      split_ifs <;> omega

theorem firstBuyDay_run_skiStrategy (s : SkiRental.Strategy)
    (σ : List Unit) :
    firstBuyDay (run (skiStrategy s) σ)
      = (match s with
        | some t => if t ≤ σ.length ∧ 1 ≤ t then some t else none
        | none => none) := by
  cases s with
  | none =>
      dsimp only
      rw [firstBuyDay_eq, findIdx_run_none, length_run]
      exact ite_eq_right (lt_irrefl _)
  | some t =>
      dsimp only
      by_cases hc : t ≤ σ.length ∧ 1 ≤ t
      · rw [ite_eq_left hc, firstBuyDay_eq, findIdx_run_some]
        have hc' : 1 ≤ t ∧ t ≤ σ.length := ⟨hc.2, hc.1⟩
        have hlt : t - 1 < σ.length := by omega
        rw [ite_eq_left hc', length_run, ite_eq_left hlt]
        congr 1
        omega
      · rw [ite_eq_right hc, firstBuyDay_eq, findIdx_run_some]
        have hc' : ¬ (1 ≤ t ∧ t ≤ σ.length) := fun h' => hc ⟨h'.2, h'.1⟩
        rw [ite_eq_right hc', length_run]
        exact ite_eq_right (lt_irrefl _)

theorem algCost_skiStrategy (B : ℕ) (s : SkiRental.Strategy)
    (σ : List Unit) :
    algCost (skiProblem B) (skiStrategy s) σ
      = (SkiRental.cost B s σ.length : ℝ) := by
  rw [algCost_eq, cost_skiProblem, firstBuyDay_run_skiStrategy, length_run]
  cases s with
  | none => rfl
  | some t =>
      dsimp only
      by_cases hc : t ≤ σ.length ∧ 1 ≤ t
      · rw [ite_eq_left hc]
      · rw [ite_eq_right hc]
        simp only [SkiRental.cost]
        have hc' : ¬ (1 ≤ t ∧ t ≤ σ.length) := fun h' => hc ⟨h'.2, h'.1⟩
        rw [ite_eq_right hc']

theorem ski_optCost (B : ℕ) (σ : List Unit) :
    optCost (skiProblem B) σ
      = ENNReal.ofReal (SkiRental.opt B σ.length : ℝ) := by
  apply le_antisymm
  · by_cases h : σ.length ≤ B
    · have h1 : algCost (skiProblem B) (skiStrategy none) σ
          = (SkiRental.opt B σ.length : ℝ) := by
        rw [algCost_skiStrategy]
        simp only [SkiRental.cost, SkiRental.opt, min_eq_left h]
      calc optCost (skiProblem B) σ
          ≤ ENNReal.ofReal
              (algCost (skiProblem B) (skiStrategy none) σ) :=
            optCost_alg_le _ _ (skiStrategy_feasible B none) trivial
        _ = ENNReal.ofReal (SkiRental.opt B σ.length : ℝ) := by rw [h1]
    · have hBlen : B ≤ σ.length := by omega
      have h1len : 1 ≤ σ.length := by omega
      have h1 : algCost (skiProblem B) (skiStrategy (some 1)) σ
          = (SkiRental.opt B σ.length : ℝ) := by
        rw [algCost_skiStrategy]
        simp only [SkiRental.cost, SkiRental.opt, min_eq_right hBlen]
        have hc' : 1 ≤ 1 ∧ 1 ≤ σ.length := ⟨le_refl 1, h1len⟩
        rw [ite_eq_left hc']
        congr 1
        omega
      calc optCost (skiProblem B) σ
          ≤ ENNReal.ofReal
              (algCost (skiProblem B) (skiStrategy (some 1)) σ) :=
            optCost_alg_le _ _ (skiStrategy_feasible B (some 1)) trivial
        _ = ENNReal.ofReal (SkiRental.opt B σ.length : ℝ) := by rw [h1]
  · rw [optCost_eq]
    apply le_iInf₂
    intro τ hτ
    obtain ⟨hfeas, hmap⟩ := hτ
    rw [cost_skiProblem]
    apply ENNReal.ofReal_le_ofReal
    have hlen : τ.length = σ.length := by rw [← hmap, List.length_map]
    rw [hlen]
    exact Nat.cast_le.mpr (SkiRental.opt_le_cost B (firstBuyDay τ) σ.length)

/-- Cast of the native competitive-ratio numerator. -/
private theorem cast_two_mul_sub_one (B : ℕ) (hB : 1 ≤ B) :
    ((2 * B - 1 : ℕ) : ℝ) = 2 * (B : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * B)]
  simp

theorem breakEven_competitive {B : ℕ} (hB : 1 ≤ B) :
    Competitive (skiProblem B) (skiStrategy (SkiRental.breakEven B))
      ((2 * B - 1 : ℝ) / B) 0 := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < (B : ℝ) := by linarith
  have hc0 : (0 : ℝ) ≤ (2 * (B : ℝ) - 1) / (B : ℝ) :=
    div_nonneg (by linarith) hBpos.le
  refine ⟨hc0, le_refl 0, skiStrategy_feasible B _, fun σ _ => ?_⟩
  rw [algCost_skiStrategy, ski_optCost, ENNReal.ofReal_zero, add_zero,
    ← ENNReal.ofReal_mul hc0]
  apply ENNReal.ofReal_le_ofReal
  have hnat := SkiRental.cost_breakEven_le hB σ.length
  have hcast : ((B * SkiRental.cost B (SkiRental.breakEven B) σ.length : ℕ) : ℝ)
      ≤ (((2 * B - 1) * SkiRental.opt B σ.length : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  rw [Nat.cast_mul, Nat.cast_mul, cast_two_mul_sub_one B hB] at hcast
  rw [div_mul_eq_mul_div, le_div_iff₀ hBpos]
  calc (SkiRental.cost B (SkiRental.breakEven B) σ.length : ℝ) * (B : ℝ)
      = (B : ℝ) * (SkiRental.cost B (SkiRental.breakEven B) σ.length : ℝ) :=
        mul_comm _ _
    _ ≤ (2 * (B : ℝ) - 1) * (SkiRental.opt B σ.length : ℝ) := hcast

theorem breakEven_competitive_two {B : ℕ} (hB : 1 ≤ B) :
    StrictCompetitive (skiProblem B) (skiStrategy (SkiRental.breakEven B)) 2 := by
  unfold StrictCompetitive
  refine ⟨by norm_num, le_refl 0, skiStrategy_feasible B _, fun σ _ => ?_⟩
  rw [algCost_skiStrategy, ski_optCost, ENNReal.ofReal_zero, add_zero,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply ENNReal.ofReal_le_ofReal
  have hnat := SkiRental.cost_breakEven_le_two_mul hB σ.length
  exact_mod_cast hnat

theorem breakEven_additive_zero {B : ℕ} (hB : 1 ≤ B) :
    Competitive (skiProblem B) (skiStrategy (SkiRental.breakEven B)) 0
      (2 * B - 1 : ℝ) := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hb0 : (0 : ℝ) ≤ 2 * (B : ℝ) - 1 := by linarith
  refine ⟨le_refl 0, hb0, skiStrategy_feasible B _, fun σ _ => ?_⟩
  rw [algCost_skiStrategy, ENNReal.ofReal_zero, zero_mul, zero_add]
  apply ENNReal.ofReal_le_ofReal
  have hnat : SkiRental.cost B (SkiRental.breakEven B) σ.length ≤ 2 * B - 1 := by
    simp only [SkiRental.cost, SkiRental.breakEven]
    split_ifs with h
    · omega
    · have hlt : σ.length < B := by
        by_contra hc
        exact h ⟨hB, le_of_not_gt hc⟩
      omega
  rw [← cast_two_mul_sub_one B hB]
  exact Nat.cast_le.mpr hnat

/-- Every `Unit` list is the replicate of its length. -/
private theorem eq_replicate_self (l : List Unit) :
    l = List.replicate l.length () := by
  induction l with
  | nil => exact List.replicate_zero.symm
  | cons r l ih =>
      cases r
      conv => lhs; rw [ih]
      exact List.replicate_succ.symm

/-- One `true` entry forces a nonempty buy filter. -/
private theorem filter_ge_one_of_true (τ : List (Unit × Bool)) (i : ℕ)
    (hi : i < τ.length) (h1 : (τ[i]'hi).2 = true) :
    1 ≤ (τ.filter (fun p => p.2)).length := by
  induction τ generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
      cases i with
      | zero =>
          simp only [List.getElem_cons_zero] at h1
          rw [List.filter_cons, ite_eq_left h1, List.length_cons]
          omega
      | succ i =>
          simp only [List.getElem_cons_succ] at h1
          have hi' : i < xs.length := by
            have hhi := hi
            simp only [List.length_cons] at hhi
            omega
          have hlen : (xs.filter (fun p => p.2)).length
              ≤ ((x :: xs).filter (fun p => p.2)).length := by
            rw [List.filter_cons]
            split_ifs with hc
            · rw [List.length_cons]
              exact Nat.le_succ _
            · exact le_rfl
          have hIH := ih i hi' h1
          omega

/-- Two `true` entries at distinct positions force two buys. -/
private theorem filter_ge_two_of_two_true (τ : List (Unit × Bool)) (i j : ℕ)
    (hi : i < τ.length) (hj : j < τ.length) (hne : i ≠ j)
    (h1 : (τ[i]'hi).2 = true) (h2 : (τ[j]'hj).2 = true) :
    2 ≤ (τ.filter (fun p => p.2)).length := by
  induction τ generalizing i j with
  | nil => simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd rfl hne
          | succ j =>
              simp only [List.getElem_cons_zero] at h1
              simp only [List.getElem_cons_succ] at h2
              rw [List.filter_cons, ite_eq_left h1, List.length_cons]
              have hj' : j < xs.length := by
                have hhj := hj
                simp only [List.length_cons] at hhj
                omega
              have hIH := filter_ge_one_of_true xs j hj' h2
              omega
      | succ i =>
          cases j with
          | zero =>
              simp only [List.getElem_cons_succ] at h1
              simp only [List.getElem_cons_zero] at h2
              rw [List.filter_cons, ite_eq_left h2, List.length_cons]
              have hi' : i < xs.length := by
                have hhi := hi
                simp only [List.length_cons] at hhi
                omega
              have hIH := filter_ge_one_of_true xs i hi' h1
              omega
          | succ j =>
              simp only [List.getElem_cons_succ] at h1 h2
              have hi' : i < xs.length := by
                have hhi := hi
                simp only [List.length_cons] at hhi
                omega
              have hj' : j < xs.length := by
                have hhj := hj
                simp only [List.length_cons] at hhj
                omega
              have hne' : i ≠ j := fun h => hne (by rw [h])
              have hlen : (xs.filter (fun p => p.2)).length
                  ≤ ((x :: xs).filter (fun p => p.2)).length := by
                rw [List.filter_cons]
                split_ifs with hc
                · rw [List.length_cons]
                  exact Nat.le_succ _
                · exact le_rfl
              have hIH := ih i j hi' hj' hne' h1 h2
              omega

/-- The answer recorded at position `j` of a run. -/
private theorem snd_runFrom (A : Strategy Unit Bool) (past σ : List Unit)
    (j : ℕ) (h : j < (runFrom A past σ).length) :
    ((runFrom A past σ)[j]'h).2 = A (past ++ σ.take (j + 1)) := by
  induction σ generalizing past j with
  | nil =>
      simp only [runFrom, List.length_nil] at h
      omega
  | cons r σ ih =>
      cases j with
      | zero =>
          simp only [runFrom, List.getElem_cons_zero]
          have ht1 : (r :: σ).take (0 + 1) = [r] := rfl
          rw [ht1]
      | succ j =>
          have hlen1 : (runFrom A past (r :: σ)).length
              = (runFrom A (past ++ [r]) σ).length + 1 := by
            simp only [runFrom_length, List.length_cons]
          have hj : j < (runFrom A (past ++ [r]) σ).length := by omega
          have hIH := ih (past ++ [r]) j hj
          have hstep : ((runFrom A past (r :: σ))[j + 1]'h).2
              = ((runFrom A (past ++ [r]) σ)[j]'hj).2 := rfl
          rw [hstep, hIH]
          have htake : (r :: σ).take (j + 1 + 1)
              = r :: σ.take (j + 1) := rfl
          have happ : (past ++ [r]) ++ σ.take (j + 1)
              = past ++ (r :: σ).take (j + 1 + 1) := by
            have h2 : [r] ++ σ.take (j + 1) = r :: σ.take (j + 1) := rfl
            rw [htake, ← h2, List.append_assoc]
          exact congrArg _ happ

/-- Runs agreeing answerwise on replicates agree everywhere. -/
private theorem runFrom_eq_of_behavior (A : Strategy Unit Bool)
    (s : SkiRental.Strategy)
    (hbehav : ∀ m : ℕ, 1 ≤ m →
      A (List.replicate m ()) = skiStrategy s (List.replicate m ()))
    (k : ℕ) (σ : List Unit) :
    runFrom A (List.replicate k ()) σ
      = runFrom (skiStrategy s) (List.replicate k ()) σ := by
  induction σ generalizing k with
  | nil => rfl
  | cons r σ ih =>
      have hrep : List.replicate k () ++ [r]
          = List.replicate (k + 1) () := by
        have h1 := eq_replicate_self (List.replicate k () ++ [r])
        have hlen : (List.replicate k () ++ [r]).length = k + 1 := by simp
        rw [hlen] at h1
        exact h1
      simp only [runFrom]
      rw [hrep, hbehav (k + 1) (by omega), ih (k + 1)]

/-- Every deterministic strategy's behavior on unit inputs is captured by
a native ski-rental strategy with the same costs. -/
theorem exists_native_strategy (B : ℕ) (A : Strategy Unit Bool)
    (hA : StrategyFeasible (skiProblem B) A) :
    ∃ s : SkiRental.Strategy, ∀ σ : List Unit,
      algCost (skiProblem B) A σ = (SkiRental.cost B s σ.length : ℝ) := by
  by_cases hEx : ∃ k : ℕ, 1 ≤ k ∧ A (List.replicate k ()) = true
  · refine ⟨some (Nat.find hEx), fun σ => ?_⟩
    have hspec := Nat.find_spec hEx
    have hsingle : ∀ m : ℕ, 1 ≤ m → m ≠ Nat.find hEx →
        A (List.replicate m ()) = false := by
      intro m hm hne
      by_contra hcon
      have htrue : A (List.replicate m ()) = true := by
        by_cases ht : A (List.replicate m ()) = true
        · exact ht
        · exact absurd (Bool.eq_false_iff.mpr ht) hcon
      have hle : Nat.find hEx ≤ m := Nat.find_min' hEx ⟨hm, htrue⟩
      have hlt : Nat.find hEx < m := lt_of_le_of_ne hle (Ne.symm hne)
      have hlenRF1 : Nat.find hEx - 1
          < (runFrom A [] (List.replicate m ())).length := by
        rw [runFrom_length, List.length_replicate]
        omega
      have hlenRF2 : m - 1
          < (runFrom A [] (List.replicate m ())).length := by
        rw [runFrom_length, List.length_replicate]
        omega
      have hpos1 := snd_runFrom A [] (List.replicate m ())
        (Nat.find hEx - 1) hlenRF1
      have hpos2 := snd_runFrom A [] (List.replicate m ()) (m - 1) hlenRF2
      have htake1 : (List.replicate m ()).take (Nat.find hEx)
          = List.replicate (Nat.find hEx) () := by
        have h1 := eq_replicate_self
          ((List.replicate m ()).take (Nat.find hEx))
        rw [List.length_take, List.length_replicate,
          min_eq_left hlt.le] at h1
        exact h1
      have htake2 : (List.replicate m ()).take m
          = List.replicate m () := by
        have h := List.take_length (l := List.replicate m ())
        rw [List.length_replicate] at h
        exact h
      have hsub1 : Nat.find hEx - 1 + 1 = Nat.find hEx := by omega
      have hsub2 : m - 1 + 1 = m := by omega
      have hT1 : ((runFrom A [] (List.replicate m ()))[Nat.find hEx - 1]'hlenRF1).2
          = true := by
        rw [hpos1, hsub1]
        change A ((List.replicate m ()).take (Nat.find hEx)) = true
        rw [htake1]
        exact hspec.2
      have hT2 : ((runFrom A [] (List.replicate m ()))[m - 1]'hlenRF2).2
          = true := by
        rw [hpos2, hsub2]
        change A ((List.replicate m ()).take m) = true
        rw [htake2]
        exact htrue
      have hne' : Nat.find hEx - 1 ≠ m - 1 := by omega
      have hge2 := filter_ge_two_of_two_true
        (runFrom A [] (List.replicate m ()))
        (Nat.find hEx - 1) (m - 1) hlenRF1 hlenRF2 hne' hT1 hT2
      have hfeas := hA (List.replicate m ()) trivial
      rw [feasible_skiProblem, run_eq] at hfeas
      omega
    have hbehav : ∀ m : ℕ, 1 ≤ m →
        A (List.replicate m ())
          = skiStrategy (some (Nat.find hEx)) (List.replicate m ()) := by
      intro m hm
      by_cases hmk : m = Nat.find hEx
      · subst hmk
        rw [hspec.2]
        simp only [skiStrategy, List.length_replicate, beq_self_eq_true]
      · have hfalse := hsingle m hm hmk
        simp only [skiStrategy, List.length_replicate]
        rw [hfalse, beq_eq_false_iff_ne.mpr hmk]
    have hrun : run A σ = run (skiStrategy (some (Nat.find hEx))) σ := by
      have h := runFrom_eq_of_behavior A (some (Nat.find hEx)) hbehav 0 σ
      rw [List.replicate_zero] at h
      exact h
    rw [algCost_eq, hrun]
    exact algCost_skiStrategy B (some (Nat.find hEx)) σ
  · refine ⟨none, fun σ => ?_⟩
    have hbehav : ∀ m : ℕ, 1 ≤ m →
        A (List.replicate m ()) = skiStrategy none (List.replicate m ()) := by
      intro m hm
      have hPm : ¬ (1 ≤ m ∧ A (List.replicate m ()) = true) :=
        fun h' => hEx ⟨m, h'⟩
      have hne : A (List.replicate m ()) ≠ true := fun ht => hPm ⟨hm, ht⟩
      have hfalse : A (List.replicate m ()) = false :=
        Bool.eq_false_iff.mpr hne
      have hrfl : skiStrategy none (List.replicate m ()) = false := rfl
      rw [hfalse, hrfl]
    have hrun : run A σ = run (skiStrategy none) σ := by
      have h := runFrom_eq_of_behavior A none hbehav 0 σ
      rw [List.replicate_zero] at h
      exact h
    rw [algCost_eq, hrun]
    exact algCost_skiStrategy B none σ

theorem ski_strictLowerBound {B : ℕ} (hB : 1 ≤ B) :
    StrictLowerBound (skiProblem B) ((2 * B - 1 : ℝ) / B) := by
  intro A hA c hc0 hc
  obtain ⟨s, hs⟩ := exists_native_strategy B A hA
  obtain ⟨d, hdpos, hnat⟩ := SkiRental.exists_pos_cost_ge hB s
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < (B : ℝ) := by linarith
  have hopt1 : 1 ≤ SkiRental.opt B d := by
    unfold SkiRental.opt
    omega
  have hoptpos : (0 : ℝ) < (SkiRental.opt B d : ℝ) := by
    have h : 0 < SkiRental.opt B d := by omega
    exact_mod_cast h
  have hcs : c * (SkiRental.opt B d : ℝ)
      < ((2 * (B : ℝ) - 1) / (B : ℝ)) * (SkiRental.opt B d : ℝ) :=
    mul_lt_mul_of_pos_right hc hoptpos
  have hnatR : ((2 * B - 1 : ℕ) : ℝ) * (SkiRental.opt B d : ℝ)
      ≤ (B : ℝ) * (SkiRental.cost B s d : ℝ) := by
    have h : ((((2 * B - 1) * SkiRental.opt B d : ℕ)) : ℝ)
        ≤ (((B * SkiRental.cost B s d : ℕ)) : ℝ) :=
      Nat.cast_le.mpr hnat
    rw [Nat.cast_mul, Nat.cast_mul] at h
    exact h
  rw [cast_two_mul_sub_one B hB] at hnatR
  have hle : ((2 * (B : ℝ) - 1) / (B : ℝ)) * (SkiRental.opt B d : ℝ)
      ≤ (SkiRental.cost B s d : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hBpos]
    calc (2 * (B : ℝ) - 1) * (SkiRental.opt B d : ℝ)
        ≤ (B : ℝ) * (SkiRental.cost B s d : ℝ) := hnatR
      _ = (SkiRental.cost B s d : ℝ) * (B : ℝ) := mul_comm _ _
  have hreal : c * (SkiRental.opt B d : ℝ)
      < (SkiRental.cost B s d : ℝ) :=
    lt_of_lt_of_le hcs hle
  have hoptnn : (0 : ℝ) ≤ (SkiRental.opt B d : ℝ) := by positivity
  have hnonneg : (0 : ℝ) ≤ c * (SkiRental.opt B d : ℝ) :=
    mul_nonneg hc0 hoptnn
  refine ⟨List.replicate d (), trivial, ?_⟩
  have hlen : (List.replicate d ()).length = d := List.length_replicate
  rw [ski_optCost, hs, hlen, ← ENNReal.ofReal_mul hc0]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnonneg).mpr hreal

/-- Rejecting control: buy-on-day-`B` is `(0, 2B - 1)`-competitive, so no
positive additive lower bound holds for ski rental even though the strict
lower bound above does. -/
theorem not_additiveLowerBound_ski {B : ℕ} (hB : 1 ≤ B) (cstar : ℝ)
    (hc : 0 < cstar) :
    ¬ AdditiveLowerBound (skiProblem B) cstar := by
  intro hLB
  obtain ⟨_, hb0, hA, hineq⟩ := breakEven_additive_zero hB
  obtain ⟨σ, hσ, hlt⟩ := hLB (skiStrategy (SkiRental.breakEven B)) hA 0
    (2 * (B : ℝ) - 1) le_rfl hc hb0
  exact absurd (hineq σ hσ) (not_le_of_gt hlt)

end Cslib.Algorithms.Lean.Online.CompetitiveFramework
