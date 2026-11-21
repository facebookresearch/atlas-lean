/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Basic.ENNReal.Basic
import Mathlib.Tactic

@[expose] public section

namespace Cslib.Algorithms.Lean.Online.CompetitiveFramework

/-- An online problem: requests arrive one at a time and must be answered
without knowledge of future requests. `legal` is the prefix-closed domain
of finite request sequences; `feasible` is the prefix-closed set of
request/answer traces, nonempty-extendable along legal inputs
(nonblocking); `cost` is finite and nonnegative on every trace. No
optimality or competitiveness assumption is part of the data. -/
structure OnlineProblem (Req Ans : Type*) where
  legal : List Req → Prop
  legal_nil : legal []
  legal_prefix : ∀ {σ τ : List Req}, legal (σ ++ τ) → legal σ
  feasible : List (Req × Ans) → Prop
  feasible_nil : feasible []
  feasible_prefix :
    ∀ {τ τ' : List (Req × Ans)}, feasible (τ ++ τ') → feasible τ
  feasible_requests :
    ∀ {τ : List (Req × Ans)}, feasible τ → legal (τ.map Prod.fst)
  nonblocking : ∀ {τ : List (Req × Ans)} {r : Req}, feasible τ →
    legal (τ.map Prod.fst ++ [r]) → ∃ a : Ans, feasible (τ ++ [(r, a)])
  cost : List (Req × Ans) → ℝ
  cost_nonneg : ∀ τ : List (Req × Ans), 0 ≤ cost τ

/-- A deterministic online strategy: the answer to the current request may
depend on the whole request prefix ending at that request, and on nothing
else. -/
def Strategy (Req Ans : Type*) : Type _ := List Req → Ans

/-- The trace produced by a strategy, threading the request history. -/
def runFrom {Req Ans : Type*} (A : Strategy Req Ans) :
    List Req → List Req → List (Req × Ans)
  | _, [] => []
  | past, r :: σ => (r, A (past ++ [r])) :: runFrom A (past ++ [r]) σ

/-- The run of a strategy on a request sequence. -/
def run {Req Ans : Type*} (A : Strategy Req Ans) (σ : List Req) :
    List (Req × Ans) :=
  runFrom A [] σ

theorem run_nil {Req Ans : Type*} (A : Strategy Req Ans) : run A [] = [] := by
  rfl

theorem runFrom_length {Req Ans : Type*} (A : Strategy Req Ans)
    (past σ : List Req) : (runFrom A past σ).length = σ.length := by
  induction σ generalizing past with
  | nil => rfl
  | cons r σ ih => simp [runFrom, ih]

theorem runFrom_map_fst {Req Ans : Type*} (A : Strategy Req Ans)
    (past σ : List Req) : (runFrom A past σ).map Prod.fst = σ := by
  induction σ generalizing past with
  | nil => rfl
  | cons r σ ih => simp [runFrom, ih]

theorem run_map_fst {Req Ans : Type*} (A : Strategy Req Ans) (σ : List Req) :
    (run A σ).map Prod.fst = σ := by
  exact runFrom_map_fst A [] σ

/-- Causality: the run on a request prefix is the corresponding prefix of
the run on any extension. -/
theorem runFrom_append {Req Ans : Type*} (A : Strategy Req Ans)
    (past σ τ : List Req) :
    runFrom A past (σ ++ τ)
      = runFrom A past σ ++ runFrom A (past ++ σ) τ := by
  induction σ generalizing past with
  | nil => simp [runFrom]
  | cons r σ ih => simp [runFrom, ih]

theorem run_prefix {Req Ans : Type*} (A : Strategy Req Ans) (σ τ : List Req) :
    (run A (σ ++ τ)).take σ.length = run A σ := by
  have h := runFrom_append A [] σ τ
  change (runFrom A [] (σ ++ τ)).take σ.length = runFrom A [] σ
  rw [h, ← runFrom_length A [] σ, List.take_left]

/-- A strategy is feasible for a problem when every legal input produces a
feasible trace. -/
def StrategyFeasible {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (A : Strategy Req Ans) : Prop :=
  ∀ σ : List Req, P.legal σ → P.feasible (run A σ)

/-- Cost of a strategy on a request sequence. -/
def algCost {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (A : Strategy Req Ans) (σ : List Req) : ℝ :=
  P.cost (run A σ)

/-- Offline optimum: infimum of feasible-trace costs for this request
sequence, as a nonnegative extended value (infinity when no feasible
trace exists). Attainment is not assumed. -/
noncomputable def optCost {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (σ : List Req) : ENNReal :=
  ⨅ τ ∈ {τ : List (Req × Ans) | P.feasible τ ∧ τ.map Prod.fst = σ},
    ENNReal.ofReal (P.cost τ)

theorem optCost_le {Req Ans : Type*} (P : OnlineProblem Req Ans)
    {σ : List Req} {τ : List (Req × Ans)} (hτ : P.feasible τ)
    (hστ : τ.map Prod.fst = σ) :
    optCost P σ ≤ ENNReal.ofReal (P.cost τ) := by
  unfold optCost
  exact biInf_le _ ⟨hτ, hστ⟩

theorem exists_feasible_trace {Req Ans : Type*} (P : OnlineProblem Req Ans)
    {σ : List Req} (hσ : P.legal σ) :
    ∃ τ : List (Req × Ans), P.feasible τ ∧ τ.map Prod.fst = σ := by
  have gen : ∀ (τ₀ : List (Req × Ans)) (σ : List Req), P.feasible τ₀ →
      P.legal (τ₀.map Prod.fst ++ σ) →
      ∃ τ₁ : List (Req × Ans),
        P.feasible (τ₀ ++ τ₁) ∧ τ₁.map Prod.fst = σ := by
    intro τ₀ σ
    induction σ generalizing τ₀ with
    | nil =>
      intro hfeas _
      exact ⟨[], by simpa using hfeas, rfl⟩
    | cons r σ ih =>
      intro hfeas hleg
      have hEq : (τ₀.map Prod.fst ++ [r]) ++ σ
          = τ₀.map Prod.fst ++ (r :: σ) := by simp
      have hpre : P.legal (τ₀.map Prod.fst ++ [r]) :=
        P.legal_prefix (hEq ▸ hleg)
      obtain ⟨a, ha⟩ := P.nonblocking hfeas hpre
      have hmap : (τ₀ ++ [(r, a)]).map Prod.fst
          = τ₀.map Prod.fst ++ [r] := by simp
      have hleg' : P.legal ((τ₀ ++ [(r, a)]).map Prod.fst ++ σ) := by
        rw [hmap, hEq]
        exact hleg
      obtain ⟨τ₁, hfeas1, hmap1⟩ := ih _ ha hleg'
      refine ⟨[(r, a)] ++ τ₁, ?_, ?_⟩
      · rwa [← List.append_assoc]
      · simp [hmap1]
  obtain ⟨τ₁, h1, h2⟩ := gen [] σ P.feasible_nil (by simpa using hσ)
  exact ⟨τ₁, by simpa using h1, h2⟩

theorem optCost_ne_top {Req Ans : Type*} (P : OnlineProblem Req Ans)
    {σ : List Req} (hσ : P.legal σ) : optCost P σ ≠ ⊤ := by
  obtain ⟨τ, hτ, hστ⟩ := exists_feasible_trace P hσ
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (optCost_le P hτ hστ)

theorem optCost_alg_le {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (A : Strategy Req Ans) (hA : StrategyFeasible P A) {σ : List Req}
    (hσ : P.legal σ) :
    optCost P σ ≤ ENNReal.ofReal (algCost P A σ) := by
  exact optCost_le P (hA σ hσ) (run_map_fst A σ)

/-- `(c, b)`-competitiveness: on every legal input the strategy cost is at
most `c` times the offline optimum plus the uniform additive constant `b`.
Stated with inequalities, never division, so the `OPT = 0` case is the
statement `ALG = 0` when `b = 0`. -/
def Competitive {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (A : Strategy Req Ans) (c b : ℝ) : Prop :=
  0 ≤ c ∧ 0 ≤ b ∧ StrategyFeasible P A ∧
    ∀ σ : List Req, P.legal σ →
      ENNReal.ofReal (algCost P A σ)
        ≤ ENNReal.ofReal c * optCost P σ + ENNReal.ofReal b

/-- Strict `c`-competitiveness: `(c, 0)`-competitiveness. -/
def StrictCompetitive {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (A : Strategy Req Ans) (c : ℝ) : Prop :=
  Competitive P A c 0

/-- Additive `c`-competitiveness: `(c, b)`-competitiveness for some uniform
additive constant `b`. -/
def AdditiveCompetitive {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (A : Strategy Req Ans) (c : ℝ) : Prop :=
  ∃ b : ℝ, Competitive P A c b

theorem AdditiveCompetitive.of_strict {Req Ans : Type*}
    (P : OnlineProblem Req Ans) (A : Strategy Req Ans) {c : ℝ}
    (h : StrictCompetitive P A c) : AdditiveCompetitive P A c := by
  exact ⟨0, h⟩

theorem Competitive.mono {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (A : Strategy Req Ans) {c b c' b' : ℝ} (h : Competitive P A c b)
    (hc : c ≤ c') (hb : b ≤ b') : Competitive P A c' b' := by
  obtain ⟨hc0, hb0, hA, hineq⟩ := h
  refine ⟨le_trans hc0 hc, le_trans hb0 hb, hA, fun σ hσ => ?_⟩
  have hcc : ENNReal.ofReal c ≤ ENNReal.ofReal c' :=
    ENNReal.ofReal_le_ofReal hc
  have hbb : ENNReal.ofReal b ≤ ENNReal.ofReal b' :=
    ENNReal.ofReal_le_ofReal hb
  have hmul := mul_le_mul_left hcc (optCost P σ)
  exact le_trans (hineq σ hσ) (add_le_add hmul hbb)

/-- Strict lower-bound predicate: no strategy beats the factor `cstar`
without an additive constant. -/
def StrictLowerBound {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (cstar : ℝ) : Prop :=
  ∀ (A : Strategy Req Ans), StrategyFeasible P A →
    ∀ c : ℝ, 0 ≤ c → c < cstar →
      ∃ σ : List Req, P.legal σ ∧
        ENNReal.ofReal c * optCost P σ < ENNReal.ofReal (algCost P A σ)

/-- Additive lower-bound predicate: no strategy beats the factor `cstar`
even with an arbitrary uniform additive constant. Distinct from the strict
predicate: a bounded-cost strategy refutes every positive additive lower
bound. -/
def AdditiveLowerBound {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (cstar : ℝ) : Prop :=
  ∀ (A : Strategy Req Ans), StrategyFeasible P A →
    ∀ c b : ℝ, 0 ≤ c → c < cstar → 0 ≤ b →
      ∃ σ : List Req, P.legal σ ∧
        ENNReal.ofReal c * optCost P σ + ENNReal.ofReal b
          < ENNReal.ofReal (algCost P A σ)

theorem StrictLowerBound.of_additive {Req Ans : Type*}
    (P : OnlineProblem Req Ans) {cstar : ℝ} (h : AdditiveLowerBound P cstar) :
    StrictLowerBound P cstar := by
  intro A hA c hc0 hc
  obtain ⟨σ, hσ, hlt⟩ := h A hA c 0 hc0 hc le_rfl
  rw [ENNReal.ofReal_zero, add_zero] at hlt
  exact ⟨σ, hσ, hlt⟩

theorem not_strictCompetitive_of_strictLowerBound {Req Ans : Type*}
    (P : OnlineProblem Req Ans) (A : Strategy Req Ans) {cstar c : ℝ}
    (h : StrictLowerBound P cstar) (hc : c < cstar) :
    ¬ StrictCompetitive P A c := by
  intro hcomp
  obtain ⟨hc0, -, hA, hineq⟩ := hcomp
  obtain ⟨σ, hσ, hlt⟩ := h A hA c hc0 hc
  have hle := hineq σ hσ
  rw [ENNReal.ofReal_zero, add_zero] at hle
  exact (not_le_of_gt hlt) hle

theorem not_additiveCompetitive_of_additiveLowerBound {Req Ans : Type*}
    (P : OnlineProblem Req Ans) (A : Strategy Req Ans) {cstar c : ℝ}
    (h : AdditiveLowerBound P cstar) (hc : c < cstar) :
    ¬ AdditiveCompetitive P A c := by
  intro hadd
  obtain ⟨b, hc0, hb0, hA, hineq⟩ := hadd
  obtain ⟨σ, hσ, hlt⟩ := h A hA c b hc0 hc hb0
  exact (not_le_of_gt hlt) (hineq σ hσ)

end Cslib.Algorithms.Lean.Online.CompetitiveFramework

end

public section
