/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.MeasureTheory.Measure.DiracProba

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
def StrictLowerBound {Req Ans : Type*} [Nonempty Ans] (P : OnlineProblem Req Ans)
    (cstar : ℝ) : Prop :=
  ∀ (A : Strategy Req Ans), StrategyFeasible P A →
    ∀ c : ℝ, 0 ≤ c → c < cstar →
      ∃ σ : List Req, P.legal σ ∧
        ENNReal.ofReal c * optCost P σ < ENNReal.ofReal (algCost P A σ)

/-- Additive lower-bound predicate: no strategy beats the factor `cstar`
even with an arbitrary uniform additive constant. Distinct from the strict
predicate: a bounded-cost strategy refutes every positive additive lower
bound. -/
def AdditiveLowerBound {Req Ans : Type*} [Nonempty Ans] (P : OnlineProblem Req Ans)
    (cstar : ℝ) : Prop :=
  ∀ (A : Strategy Req Ans), StrategyFeasible P A →
    ∀ c b : ℝ, 0 ≤ c → c < cstar → 0 ≤ b →
      ∃ σ : List Req, P.legal σ ∧
        ENNReal.ofReal c * optCost P σ + ENNReal.ofReal b
          < ENNReal.ofReal (algCost P A σ)

theorem StrictLowerBound.of_additive {Req Ans : Type*} [Nonempty Ans]
    (P : OnlineProblem Req Ans) {cstar : ℝ} (h : AdditiveLowerBound P cstar) :
    StrictLowerBound P cstar := by
  intro A hA c hc0 hc
  obtain ⟨σ, hσ, hlt⟩ := h A hA c 0 hc0 hc le_rfl
  rw [ENNReal.ofReal_zero, add_zero] at hlt
  exact ⟨σ, hσ, hlt⟩

theorem not_strictCompetitive_of_strictLowerBound {Req Ans : Type*}
    [Nonempty Ans]
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
    [Nonempty Ans]
    (P : OnlineProblem Req Ans) (A : Strategy Req Ans) {cstar c : ℝ}
    (h : AdditiveLowerBound P cstar) (hc : c < cstar) :
    ¬ AdditiveCompetitive P A c := by
  intro hadd
  obtain ⟨b, hc0, hb0, hA, hineq⟩ := hadd
  obtain ⟨σ, hσ, hlt⟩ := h A hA c b hc0 hc hb0
  exact (not_le_of_gt hlt) (hineq σ hσ)

theorem run_append_singleton {Req Ans : Type*} (A : Strategy Req Ans)
    (σ : List Req) (r : Req) :
    run A (σ ++ [r]) = run A σ ++ [(r, A (σ ++ [r]))] := by
  have h := runFrom_append A [] σ [r]
  simp only [List.nil_append] at h
  have h1 : runFrom A σ [r] = [(r, A (σ ++ [r]))] := rfl
  unfold run
  rw [h, h1]

open Classical in
private noncomputable def pickAnswer {Req Ans : Type*} [Nonempty Ans]
    (P : OnlineProblem Req Ans) (τ : List (Req × Ans)) (r : Req) : Ans :=
  if h : P.feasible τ ∧ P.legal (τ.map Prod.fst ++ [r]) then
    Classical.choose (P.nonblocking h.1 h.2)
  else Classical.choice inferInstance

private theorem pickAnswer_spec {Req Ans : Type*} [Nonempty Ans]
    (P : OnlineProblem Req Ans) (τ : List (Req × Ans)) (r : Req)
    (h : P.feasible τ ∧ P.legal (τ.map Prod.fst ++ [r])) :
    P.feasible (τ ++ [(r, pickAnswer P τ r)]) := by
  unfold pickAnswer
  rw [dite_eq_left h]
  exact Classical.choose_spec (P.nonblocking h.1 h.2)

private noncomputable def stratAux {Req Ans : Type*} [Nonempty Ans]
    (P : OnlineProblem Req Ans) : Nat → List Req → Ans
  | 0, _ => Classical.choice inferInstance
  | _ + 1, [] => Classical.choice inferInstance
  | n + 1, r :: rest =>
    pickAnswer P (run (stratAux P n) (r :: rest).dropLast)
      ((r :: rest).getLast (by simp))

private noncomputable def stratOf {Req Ans : Type*} [Nonempty Ans]
    (P : OnlineProblem Req Ans) : Strategy Req Ans :=
  fun σ => stratAux P σ.length σ

private theorem runFrom_strat_congr {Req Ans : Type*} {f g : Strategy Req Ans}
    (past : List Req) : ∀ (σ : List Req),
    (∀ ρ : List Req, ρ.length ≤ past.length + σ.length → f ρ = g ρ) →
    runFrom f past σ = runFrom g past σ := by
  intro σ
  induction σ generalizing past with
  | nil => intro _; rfl
  | cons r σ ih =>
    intro h
    have e1 : (past ++ [r]).length = past.length + 1 := by simp
    have e2 : (r :: σ).length = σ.length + 1 := by simp
    have hq : f (past ++ [r]) = g (past ++ [r]) := h _ (by omega)
    have ht : runFrom f (past ++ [r]) σ = runFrom g (past ++ [r]) σ :=
      ih _ (fun ρ hρ => h ρ (by omega))
    simp only [runFrom, hq, ht]

private theorem run_strat_congr {Req Ans : Type*} {f g : Strategy Req Ans}
    {σ : List Req} (h : ∀ ρ : List Req, ρ.length ≤ σ.length → f ρ = g ρ) :
    run f σ = run g σ := by
  unfold run
  exact runFrom_strat_congr _ _ (fun ρ hρ => h ρ (by simpa using hρ))

private theorem stratAux_coh {Req Ans : Type*} [Nonempty Ans]
    (P : OnlineProblem Req Ans) (n : Nat) : ∀ (m : Nat) (σ : List Req),
    σ.length ≤ n → σ.length ≤ m → stratAux P n σ = stratAux P m σ := by
  induction n with
  | zero =>
    intro m σ hn _
    have hσ : σ = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
    subst hσ
    cases m with
    | zero => rfl
    | succ m => simp only [stratAux]
  | succ n ih =>
    intro m σ hn hm
    cases m with
    | zero =>
      have hσ : σ = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hm)
      subst hσ
      simp only [stratAux]
    | succ m =>
      cases σ with
      | nil => simp only [stratAux]
      | cons r rest =>
        simp only [stratAux]
        have hlen : ((r :: rest).dropLast).length ≤ n
            ∧ ((r :: rest).dropLast).length ≤ m := by
          have e : ((r :: rest).dropLast).length = (r :: rest).length - 1 :=
            List.length_dropLast
          have e2 : (r :: rest).length = rest.length + 1 := by simp
          omega
        have hrun : run (stratAux P n) (r :: rest).dropLast
            = run (stratAux P m) (r :: rest).dropLast := by
          apply run_strat_congr
          intro ρ hρ
          exact ih m ρ (Nat.le_trans hρ hlen.1) (Nat.le_trans hρ hlen.2)
        rw [hrun]

private theorem stratOf_run_feasible {Req Ans : Type*} [Nonempty Ans]
    (P : OnlineProblem Req Ans) (n : Nat) : ∀ (σ : List Req),
    σ.length ≤ n → P.legal σ → P.feasible (run (stratOf P) σ) := by
  induction n with
  | zero =>
    intro σ hn _
    have hσ0 : σ = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
    subst hσ0
    rw [run_nil]
    exact P.feasible_nil
  | succ n ih =>
    intro σ hn hσ
    cases σ with
    | nil =>
      rw [run_nil]
      exact P.feasible_nil
    | cons r rest =>
      have hne : (r :: rest) ≠ [] := by simp
      have hEq : (r :: rest).dropLast ++ [(r :: rest).getLast hne]
          = r :: rest :=
        List.dropLast_append_getLast hne
      have hlen : ((r :: rest).dropLast).length < (r :: rest).length := by
        have e : ((r :: rest).dropLast).length = (r :: rest).length - 1 :=
          List.length_dropLast
        have e2 : (r :: rest).length = rest.length + 1 := by simp
        omega
      have hle : P.legal
          ((r :: rest).dropLast ++ [(r :: rest).getLast hne]) := by
        rwa [hEq]
      have hσ' : P.legal (r :: rest).dropLast := P.legal_prefix hle
      have hfeas : P.feasible (run (stratOf P) (r :: rest).dropLast) :=
        ih _ (by omega) hσ'
      have hleg : P.legal ((run (stratOf P) (r :: rest).dropLast).map Prod.fst
          ++ [(r :: rest).getLast hne]) := by
        have hmap : (run (stratOf P) (r :: rest).dropLast).map Prod.fst
            = (r :: rest).dropLast :=
          run_map_fst _ _
        rwa [hmap]
      have hpick := pickAnswer_spec P (run (stratOf P) (r :: rest).dropLast)
        ((r :: rest).getLast hne) ⟨hfeas, hleg⟩
      have hA : stratOf P (r :: rest)
          = pickAnswer P (run (stratOf P) (r :: rest).dropLast)
              ((r :: rest).getLast hne) := by
        have hL : (r :: rest).length = rest.length + 1 := by simp
        simp only [stratOf]
        rw [hL]
        simp only [stratAux]
        have hrun : run (stratAux P rest.length) (r :: rest).dropLast
            = run (stratOf P) (r :: rest).dropLast := by
          apply run_strat_congr
          intro ρ hρ
          have hρle : ρ.length ≤ rest.length := by omega
          simp only [stratOf]
          exact stratAux_coh P _ _ _ hρle le_rfl
        rw [hrun]
      have hrun2 : run (stratOf P) (r :: rest)
          = run (stratOf P) (r :: rest).dropLast
            ++ [((r :: rest).getLast hne, stratOf P (r :: rest))] := by
        have h := run_append_singleton (stratOf P) (r :: rest).dropLast
          ((r :: rest).getLast hne)
        rwa [hEq] at h
      rw [hrun2, hA]
      exact hpick

/-- A feasible strategy exists whenever answers exist: choose answers
inductively along request prefixes using `nonblocking`. This keeps the
lower-bound predicates from holding vacuously. -/
theorem exists_strategyFeasible {Req Ans : Type*} [Nonempty Ans]
    (P : OnlineProblem Req Ans) :
    ∃ A : Strategy Req Ans, StrategyFeasible P A := by
  exact ⟨stratOf P, fun σ hσ => stratOf_run_feasible P σ.length σ le_rfl hσ⟩

/-- A state machine answering requests online: from the current state and
request it produces an answer and a next state. -/
structure StateMachine (Req Ans State : Type*) where
  init : State
  step : State → Req → Ans × State

/-- State reached from `s` after consuming a request sequence. -/
def StateMachine.stateFrom {Req Ans State : Type*}
    (M : StateMachine Req Ans State) (s : State) : List Req → State
  | [] => s
  | r :: σ => M.stateFrom (M.step s r).2 σ

/-- Trace produced from state `s` on a request sequence. -/
def StateMachine.traceFrom {Req Ans State : Type*}
    (M : StateMachine Req Ans State) (s : State) : List Req → List (Req × Ans)
  | [] => []
  | r :: σ => (r, (M.step s r).1) :: M.traceFrom (M.step s r).2 σ

/-- State reached from the initial state. -/
def StateMachine.stateAfter {Req Ans State : Type*}
    (M : StateMachine Req Ans State) (σ : List Req) : State :=
  M.stateFrom M.init σ

/-- Trace produced from the initial state. -/
def StateMachine.trace {Req Ans State : Type*}
    (M : StateMachine Req Ans State) (σ : List Req) :
    List (Req × Ans) :=
  M.traceFrom M.init σ

/-- The causal strategy induced by a state machine: answer from the state
reached by the strict request prefix. On the empty history (never queried
by `run`) an arbitrary answer is chosen. -/
noncomputable def StateMachine.toStrategy {Req Ans State : Type*}
    [Nonempty Ans] (M : StateMachine Req Ans State) : Strategy Req Ans :=
  fun σ => match σ.reverse with
    | [] => Classical.choice inferInstance
    | r :: pastRev => (M.step (M.stateAfter pastRev.reverse) r).1

theorem StateMachine.run_toStrategy {Req Ans State : Type*} [Nonempty Ans]
    (M : StateMachine Req Ans State) (σ : List Req) :
    run M.toStrategy σ = M.trace σ := by
  have stapp : ∀ (s : State) (l₁ l₂ : List Req),
      M.stateFrom s (l₁ ++ l₂) = M.stateFrom (M.stateFrom s l₁) l₂ := by
    intro s l₁ l₂
    induction l₁ generalizing s with
    | nil => rfl
    | cons r l₁ ih => exact ih _
  have hstrat : ∀ (past : List Req) (r : Req),
      M.toStrategy (past ++ [r])
        = (M.step (M.stateFrom M.init past) r).1 := by
    intro past r
    have hrev : (past ++ [r]).reverse = r :: past.reverse := by simp
    simp only [StateMachine.toStrategy, hrev, List.reverse_reverse,
      StateMachine.stateAfter]
  have gen : ∀ (past σ : List Req),
      runFrom M.toStrategy past σ
        = M.traceFrom (M.stateFrom M.init past) σ := by
    intro past σ
    induction σ generalizing past with
    | nil => rfl
    | cons r σ ih =>
      have h2 : M.stateFrom M.init (past ++ [r])
          = (M.step (M.stateFrom M.init past) r).2 :=
        stapp M.init past [r]
      simp only [runFrom, StateMachine.traceFrom, hstrat, ih, h2]
  exact gen [] σ

theorem StateMachine.strategyFeasible_toStrategy {Req Ans State : Type*}
    [Nonempty Ans] (P : OnlineProblem Req Ans) (M : StateMachine Req Ans State)
    (hM : ∀ σ : List Req, P.legal σ → P.feasible (M.trace σ)) :
    StrategyFeasible P M.toStrategy := by
  intro σ hσ
  rw [StateMachine.run_toStrategy]
  exact hM σ hσ

theorem StateMachine.algCost_toStrategy {Req Ans State : Type*} [Nonempty Ans]
    (P : OnlineProblem Req Ans) (M : StateMachine Req Ans State)
    (σ : List Req) :
    algCost P M.toStrategy σ = P.cost (M.trace σ) := by
  exact congrArg P.cost (StateMachine.run_toStrategy M σ)

/-- Attainment for natural-number costs: on legal inputs some feasible
trace realizes the offline optimum. (For real costs this fails in
general: feasible costs `1 / (n + 1)` have infimum `0` and no minimum.) -/
theorem exists_optimal_of_natCost {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (hcost : ∀ τ : List (Req × Ans), ∃ n : ℕ, P.cost τ = n)
    {σ : List Req} (hσ : P.legal σ) :
    ∃ τ : List (Req × Ans), P.feasible τ ∧ τ.map Prod.fst = σ ∧
      optCost P σ = ENNReal.ofReal (P.cost τ) := by
  obtain ⟨τ₀, hτ₀, hσ₀⟩ := exists_feasible_trace P hσ
  obtain ⟨n₀, hn₀⟩ := hcost τ₀
  have hne : {n : ℕ | ∃ τ : List (Req × Ans),
      P.feasible τ ∧ τ.map Prod.fst = σ ∧ P.cost τ = ↑n}.Nonempty :=
    ⟨n₀, τ₀, hτ₀, hσ₀, hn₀⟩
  have hmem := Nat.sInf_mem hne
  obtain ⟨τm, hτm, hσm, hcostm⟩ := hmem
  refine ⟨τm, hτm, hσm, ?_⟩
  apply le_antisymm
  · exact optCost_le P hτm hσm
  · rw [hcostm]
    unfold optCost
    apply le_iInf₂
    intro τ hτ
    obtain ⟨hfeas, hmap⟩ := hτ
    obtain ⟨n, hn⟩ := hcost τ
    have hnmem : n ∈ {n : ℕ | ∃ τ : List (Req × Ans),
        P.feasible τ ∧ τ.map Prod.fst = σ ∧ P.cost τ = ↑n} :=
      ⟨τ, hfeas, hmap, hn⟩
    have hle : sInf {n : ℕ | ∃ τ : List (Req × Ans),
        P.feasible τ ∧ τ.map Prod.fst = σ ∧ P.cost τ = ↑n} ≤ n :=
      Nat.sInf_le hnmem
    rw [hn]
    exact ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hle)

/-- A request-preserving simulation of `X` by `Y`: the same request type
and sequence throughout. `F` turns `Y`-strategies into `X`-strategies;
`G` turns feasible `X`-traces into feasible `Y`-traces on the same input;
the two cost laws bound both translations. -/
structure Simulation {Req AnsX AnsY : Type*} (X : OnlineProblem Req AnsX)
    (Y : OnlineProblem Req AnsY) where
  F : Strategy Req AnsY → Strategy Req AnsX
  G : List Req → List (Req × AnsX) → List (Req × AnsY)
  legal_mono : ∀ σ : List Req, X.legal σ → Y.legal σ
  F_feasible : ∀ A : Strategy Req AnsY, StrategyFeasible Y A →
    StrategyFeasible X (F A)
  G_feasible : ∀ (σ : List Req) (τ : List (Req × AnsX)), X.feasible τ →
    τ.map Prod.fst = σ → Y.feasible (G σ τ) ∧ (G σ τ).map Prod.fst = σ
  a : ℝ
  p : ℝ
  d : ℝ
  q : ℝ
  ha : 0 ≤ a
  hp : 0 ≤ p
  hd : 0 ≤ d
  hq : 0 ≤ q
  costF : ∀ (A : Strategy Req AnsY) (σ : List Req), X.legal σ →
    ENNReal.ofReal (algCost X (F A) σ)
      ≤ ENNReal.ofReal a * ENNReal.ofReal (algCost Y A σ) + ENNReal.ofReal p
  costG : ∀ (σ : List Req) (τ : List (Req × AnsX)), X.feasible τ →
    τ.map Prod.fst = σ →
    ENNReal.ofReal (Y.cost (G σ τ))
      ≤ ENNReal.ofReal d * ENNReal.ofReal (X.cost τ) + ENNReal.ofReal q

/-- The offline comparison induced by a simulation. -/
theorem Simulation.optCost_le {Req AnsX AnsY : Type*}
    {X : OnlineProblem Req AnsX} {Y : OnlineProblem Req AnsY}
    (S : Simulation X Y) {σ : List Req} (hσ : X.legal σ) :
    optCost Y σ ≤ ENNReal.ofReal S.d * optCost X σ + ENNReal.ofReal S.q := by
  obtain ⟨τ₀, hτ₀, hσ₀⟩ := exists_feasible_trace X hσ
  have hinst : Nonempty (Subtype (· ∈ {τ : List (Req × AnsX) |
      X.feasible τ ∧ τ.map Prod.fst = σ})) := ⟨⟨τ₀, hτ₀, hσ₀⟩⟩
  have hconv : optCost X σ
      = ⨅ x : Subtype (· ∈ {τ : List (Req × AnsX) |
        X.feasible τ ∧ τ.map Prod.fst = σ}),
        ENNReal.ofReal (X.cost x.1) := by
    unfold optCost
    exact (iInf_subtype (f := fun x : Subtype (· ∈ {τ : List (Req × AnsX) |
      X.feasible τ ∧ τ.map Prod.fst = σ}) =>
      ENNReal.ofReal (X.cost x.1))).symm
  rw [hconv]
  rw [ENNReal.mul_iInf (fun hd _ => absurd hd ENNReal.ofReal_ne_top)]
  rw [add_comm, ENNReal.add_iInf]
  apply le_iInf
  intro x
  obtain ⟨h1, h2⟩ := S.G_feasible σ x.1 x.2.1 x.2.2
  have hle1 : optCost Y σ ≤ ENNReal.ofReal (Y.cost (S.G σ x.1)) :=
    _root_.Cslib.Algorithms.Lean.Online.CompetitiveFramework.optCost_le Y h1 h2
  have hle2 : ENNReal.ofReal (Y.cost (S.G σ x.1))
      ≤ ENNReal.ofReal S.q
        + ENNReal.ofReal S.d * ENNReal.ofReal (X.cost x.1) := by
    have hG := S.costG σ x.1 x.2.1 x.2.2
    rw [add_comm]
    exact hG
  exact le_trans hle1 hle2

/-- Transfer of competitiveness along a simulation:
`(c, b)` on `Y` gives `(a·c·d, a·c·q + a·b + p)` on `X`. -/
theorem Simulation.competitive_transfer {Req AnsX AnsY : Type*}
    {X : OnlineProblem Req AnsX} {Y : OnlineProblem Req AnsY}
    (S : Simulation X Y) (A : Strategy Req AnsY) {c b : ℝ}
    (hA : Competitive Y A c b) :
    Competitive X (S.F A) (S.a * c * S.d) (S.a * c * S.q + S.a * b + S.p) := by
  obtain ⟨hc0, hb0, hAY, hineq⟩ := hA
  refine ⟨mul_nonneg (mul_nonneg S.ha hc0) S.hd, ?_,
    S.F_feasible A hAY, ?_⟩
  · exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg S.ha hc0) S.hq)
      (mul_nonneg S.ha hb0)) S.hp
  · intro σ hσ
    have hY := hineq σ (S.legal_mono σ hσ)
    have hF := S.costF A σ hσ
    have hO := S.optCost_le hσ
    have hmul1 := mul_le_mul_right hY (ENNReal.ofReal S.a)
    have step1 : ENNReal.ofReal (algCost X (S.F A) σ)
        ≤ ENNReal.ofReal S.a * (ENNReal.ofReal c * optCost Y σ
          + ENNReal.ofReal b) + ENNReal.ofReal S.p :=
      le_trans hF (add_le_add_left hmul1 (ENNReal.ofReal S.p))
    have hmul2 := mul_le_mul_right hO (ENNReal.ofReal c)
    have hadd2 := add_le_add_left hmul2 (ENNReal.ofReal b)
    have hmul3 := mul_le_mul_right hadd2 (ENNReal.ofReal S.a)
    have hadd3 := add_le_add_left hmul3 (ENNReal.ofReal S.p)
    have step2 : ENNReal.ofReal (algCost X (S.F A) σ)
        ≤ ENNReal.ofReal S.a * (ENNReal.ofReal c *
          (ENNReal.ofReal S.d * optCost X σ + ENNReal.ofReal S.q)
          + ENNReal.ofReal b) + ENNReal.ofReal S.p :=
      le_trans step1 hadd3
    have e1 : ENNReal.ofReal (S.a * c * S.d)
        = ENNReal.ofReal S.a * ENNReal.ofReal c * ENNReal.ofReal S.d := by
      rw [ENNReal.ofReal_mul (mul_nonneg S.ha hc0), ENNReal.ofReal_mul S.ha]
    have e2 : ENNReal.ofReal (S.a * c * S.q + S.a * b + S.p)
        = ENNReal.ofReal S.a * ENNReal.ofReal c * ENNReal.ofReal S.q
          + ENNReal.ofReal S.a * ENNReal.ofReal b + ENNReal.ofReal S.p := by
      rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg (mul_nonneg S.ha hc0) S.hq)
        (mul_nonneg S.ha hb0)) S.hp]
      rw [ENNReal.ofReal_add (mul_nonneg (mul_nonneg S.ha hc0) S.hq)
        (mul_nonneg S.ha hb0)]
      rw [ENNReal.ofReal_mul (mul_nonneg S.ha hc0), ENNReal.ofReal_mul S.ha,
        ENNReal.ofReal_mul S.ha]
    have step3 : ENNReal.ofReal S.a * (ENNReal.ofReal c *
          (ENNReal.ofReal S.d * optCost X σ + ENNReal.ofReal S.q)
          + ENNReal.ofReal b) + ENNReal.ofReal S.p
        = ENNReal.ofReal (S.a * c * S.d) * optCost X σ
          + ENNReal.ofReal (S.a * c * S.q + S.a * b + S.p) := by
      rw [e1, e2]
      ring
    exact le_trans step2 (le_of_eq step3)

/-- The identity simulation. -/
def Simulation.refl {Req Ans : Type*} (X : OnlineProblem Req Ans) :
    Simulation X X where
  F := fun A => A
  G := fun _ τ => τ
  legal_mono := fun _ h => h
  F_feasible := fun _ h => h
  G_feasible := fun _ _ hτ hσ => ⟨hτ, hσ⟩
  a := 1
  p := 0
  d := 1
  q := 0
  ha := zero_le_one
  hp := le_refl 0
  hd := zero_le_one
  hq := le_refl 0
  costF := by
    intro A σ _
    simp
  costG := by
    intro σ τ _ _
    simp

/-- Composition of request-preserving simulations, with the coefficient
laws `(a₁a₂, a₁p₂ + p₁, d₁d₂, d₂q₁ + q₂)`. -/
def Simulation.comp {Req AnsX AnsY AnsZ : Type*}
    {X : OnlineProblem Req AnsX} {Y : OnlineProblem Req AnsY}
    {Z : OnlineProblem Req AnsZ} (S₁ : Simulation X Y) (S₂ : Simulation Y Z) :
    Simulation X Z where
  F := S₁.F ∘ S₂.F
  G := fun σ τ => S₂.G σ (S₁.G σ τ)
  legal_mono := fun σ h => S₂.legal_mono σ (S₁.legal_mono σ h)
  F_feasible := fun A hA => S₁.F_feasible _ (S₂.F_feasible _ hA)
  G_feasible := by
    intro σ τ hτ hσ
    obtain ⟨h1, h2⟩ := S₁.G_feasible σ τ hτ hσ
    exact S₂.G_feasible σ (S₁.G σ τ) h1 h2
  a := S₁.a * S₂.a
  p := S₁.a * S₂.p + S₁.p
  d := S₁.d * S₂.d
  q := S₂.d * S₁.q + S₂.q
  ha := by exact mul_nonneg S₁.ha S₂.ha
  hp := by exact add_nonneg (mul_nonneg S₁.ha S₂.hp) S₁.hp
  hd := by exact mul_nonneg S₁.hd S₂.hd
  hq := by exact add_nonneg (mul_nonneg S₂.hd S₁.hq) S₂.hq
  costF := by
    intro A σ hσ
    have h1 := S₁.costF (S₂.F A) σ hσ
    have h2 := S₂.costF A σ (S₁.legal_mono σ hσ)
    have hmul := mul_le_mul_right h2 (ENNReal.ofReal S₁.a)
    have hchain : ENNReal.ofReal (algCost X ((S₁.F ∘ S₂.F) A) σ)
        ≤ ENNReal.ofReal S₁.a * (ENNReal.ofReal S₂.a *
          ENNReal.ofReal (algCost Z A σ) + ENNReal.ofReal S₂.p)
          + ENNReal.ofReal S₁.p :=
      le_trans h1 (add_le_add_left hmul (ENNReal.ofReal S₁.p))
    have heq : ENNReal.ofReal S₁.a * (ENNReal.ofReal S₂.a *
          ENNReal.ofReal (algCost Z A σ) + ENNReal.ofReal S₂.p)
          + ENNReal.ofReal S₁.p
        = ENNReal.ofReal (S₁.a * S₂.a) * ENNReal.ofReal (algCost Z A σ)
          + ENNReal.ofReal (S₁.a * S₂.p + S₁.p) := by
      have m1 : ENNReal.ofReal (S₁.a * S₂.a)
          = ENNReal.ofReal S₁.a * ENNReal.ofReal S₂.a :=
        ENNReal.ofReal_mul S₁.ha
      have m2 : ENNReal.ofReal (S₁.a * S₂.p)
          = ENNReal.ofReal S₁.a * ENNReal.ofReal S₂.p :=
        ENNReal.ofReal_mul S₁.ha
      have a1 : ENNReal.ofReal (S₁.a * S₂.p + S₁.p)
          = ENNReal.ofReal (S₁.a * S₂.p) + ENNReal.ofReal S₁.p :=
        ENNReal.ofReal_add (mul_nonneg S₁.ha S₂.hp) S₁.hp
      rw [m1, a1, m2]
      ring
    exact le_trans hchain (le_of_eq heq)
  costG := by
    intro σ τ hτ hσ
    obtain ⟨g1, g2⟩ := S₁.G_feasible σ τ hτ hσ
    have h1 := S₁.costG σ τ hτ hσ
    have h2 := S₂.costG σ (S₁.G σ τ) g1 g2
    have hmul := mul_le_mul_right h1 (ENNReal.ofReal S₂.d)
    have hchain : ENNReal.ofReal (Z.cost (S₂.G σ (S₁.G σ τ)))
        ≤ ENNReal.ofReal S₂.d * (ENNReal.ofReal S₁.d *
          ENNReal.ofReal (X.cost τ) + ENNReal.ofReal S₁.q)
          + ENNReal.ofReal S₂.q :=
      le_trans h2 (add_le_add_left hmul (ENNReal.ofReal S₂.q))
    have heq : ENNReal.ofReal S₂.d * (ENNReal.ofReal S₁.d *
          ENNReal.ofReal (X.cost τ) + ENNReal.ofReal S₁.q)
          + ENNReal.ofReal S₂.q
        = ENNReal.ofReal (S₁.d * S₂.d) * ENNReal.ofReal (X.cost τ)
          + ENNReal.ofReal (S₂.d * S₁.q + S₂.q) := by
      have m1 : ENNReal.ofReal (S₁.d * S₂.d)
          = ENNReal.ofReal S₁.d * ENNReal.ofReal S₂.d :=
        ENNReal.ofReal_mul S₁.hd
      have m2 : ENNReal.ofReal (S₂.d * S₁.q)
          = ENNReal.ofReal S₂.d * ENNReal.ofReal S₁.q :=
        ENNReal.ofReal_mul S₂.hd
      have a1 : ENNReal.ofReal (S₂.d * S₁.q + S₂.q)
          = ENNReal.ofReal (S₂.d * S₁.q) + ENNReal.ofReal S₂.q :=
        ENNReal.ofReal_add (mul_nonneg S₂.hd S₁.hq) S₂.hq
      rw [m1, a1, m2]
      ring
    exact le_trans hchain (le_of_eq heq)


/-- A randomized strategy against an oblivious adversary: the request
sequence is fixed before the seed is drawn; each seed selects a causal
deterministic strategy. The structure itself imposes no feasibility;
seedwise feasibility for a problem is required by `RandCompetitive`
and `RandProfitCompetitive`. -/
structure RandStrategy (Req Ans Ω : Type*) [MeasurableSpace Ω] where
  μ : MeasureTheory.ProbabilityMeasure Ω
  strat : Ω → Strategy Req Ans

/-- Expected cost of a randomized strategy on a fixed input, as a
nonnegative extended value (divergent expectation is `⊤`). -/
noncomputable def expectedCost {Req Ans Ω : Type*} [MeasurableSpace Ω]
    (P : OnlineProblem Req Ans) (A : RandStrategy Req Ans Ω)
    (σ : List Req) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (algCost P (A.strat ω) σ) ∂(A.μ : MeasureTheory.Measure Ω)

/-- Randomized `(c, b)`-competitiveness against an oblivious adversary:
every seed is feasible, the run cost is measurable per input, and the
expected cost is at most `c • OPT + b` with constants outside the
expectation. -/
def RandCompetitive {Req Ans Ω : Type*} [MeasurableSpace Ω]
    (P : OnlineProblem Req Ans) (A : RandStrategy Req Ans Ω) (c b : ℝ) :
    Prop :=
  0 ≤ c ∧ 0 ≤ b ∧ (∀ ω, StrategyFeasible P (A.strat ω)) ∧
    ∀ σ : List Req, P.legal σ →
      Measurable (fun ω => ENNReal.ofReal (algCost P (A.strat ω) σ)) ∧
      expectedCost P A σ ≤ ENNReal.ofReal c * optCost P σ + ENNReal.ofReal b

/-- The constant (Dirac) randomized strategy at a fixed seed agrees with
deterministic competitiveness of the selected strategy. -/
theorem randCompetitive_dirac_iff {Req Ans Ω : Type*} [MeasurableSpace Ω]
    (P : OnlineProblem Req Ans) (A0 : Strategy Req Ans) (ω0 : Ω) (c b : ℝ) :
    RandCompetitive P
        { μ := (⟨MeasureTheory.Measure.dirac ω0, by infer_instance⟩ :
            MeasureTheory.ProbabilityMeasure Ω),
          strat := fun _ => A0 } c b
      ↔ Competitive P A0 c b := by
  have hexp : ∀ σ : List Req, expectedCost P
      { μ := (⟨MeasureTheory.Measure.dirac ω0, by infer_instance⟩ :
          MeasureTheory.ProbabilityMeasure Ω),
        strat := fun _ => A0 } σ
      = ENNReal.ofReal (algCost P A0 σ) := by
    intro σ
    change ∫⁻ _ : Ω, ENNReal.ofReal (algCost P A0 σ)
        ∂MeasureTheory.Measure.dirac ω0
      = ENNReal.ofReal (algCost P A0 σ)
    exact MeasureTheory.lintegral_dirac' ω0 measurable_const
  constructor
  · rintro ⟨hc0, hb0, hA, hineq⟩
    refine ⟨hc0, hb0, hA ω0, fun σ hσ => ?_⟩
    obtain ⟨-, hle⟩ := hineq σ hσ
    rw [hexp] at hle
    exact hle
  · rintro ⟨hc0, hb0, hA, hineq⟩
    refine ⟨hc0, hb0, fun _ => hA, fun σ hσ => ?_⟩
    refine ⟨?_, ?_⟩
    · change Measurable (fun _ : Ω => ENNReal.ofReal (algCost P A0 σ))
      exact measurable_const
    · rw [hexp]
      exact hineq σ hσ

/-- Seedwise transfer of randomized competitiveness along a simulation,
with the same coefficients as the deterministic transfer; measurability
of the transferred cost is part of the conclusion's hypothesis check. -/
theorem Simulation.randCompetitive_transfer {Req AnsX AnsY Ω : Type*}
    [MeasurableSpace Ω] {X : OnlineProblem Req AnsX}
    {Y : OnlineProblem Req AnsY} (S : Simulation X Y)
    (A : RandStrategy Req AnsY Ω) {c b : ℝ} (hA : RandCompetitive Y A c b)
    (hmeas : ∀ σ : List Req, X.legal σ →
      Measurable (fun ω => ENNReal.ofReal (algCost X (S.F (A.strat ω)) σ))) :
    RandCompetitive X
      { μ := A.μ, strat := fun ω => S.F (A.strat ω) }
      (S.a * c * S.d) (S.a * c * S.q + S.a * b + S.p) := by
  obtain ⟨hc0, hb0, hAY, hineq⟩ := hA
  refine ⟨mul_nonneg (mul_nonneg S.ha hc0) S.hd, ?_,
    fun ω => S.F_feasible _ (hAY ω), fun σ hσ => ⟨hmeas σ hσ, ?_⟩⟩
  · exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg S.ha hc0) S.hq)
      (mul_nonneg S.ha hb0)) S.hp
  · have hYmeas : Measurable
        (fun ω => ENNReal.ofReal (algCost Y (A.strat ω) σ)) :=
      (hineq σ (S.legal_mono σ hσ)).1
    have hY : expectedCost Y A σ
        ≤ ENNReal.ofReal c * optCost Y σ + ENNReal.ofReal b :=
      (hineq σ (S.legal_mono σ hσ)).2
    have hO := S.optCost_le hσ
    have hmul : Measurable (fun ω => ENNReal.ofReal S.a
        * ENNReal.ofReal (algCost Y (A.strat ω) σ)) :=
      hYmeas.const_mul _
    have hprob : (A.μ : MeasureTheory.Measure Ω) Set.univ = 1 :=
      MeasureTheory.measure_univ
    have step0 : expectedCost X
          { μ := A.μ, strat := fun ω => S.F (A.strat ω) }
          σ
          ≤ ∫⁻ ω, (ENNReal.ofReal S.a
            * ENNReal.ofReal (algCost Y (A.strat ω) σ) + ENNReal.ofReal S.p)
            ∂(A.μ : MeasureTheory.Measure Ω) := by
      unfold expectedCost
      exact MeasureTheory.lintegral_mono fun ω => S.costF (A.strat ω) σ hσ
    have stepE : (∫⁻ ω, (ENNReal.ofReal S.a
            * ENNReal.ofReal (algCost Y (A.strat ω) σ) + ENNReal.ofReal S.p)
            ∂(A.μ : MeasureTheory.Measure Ω))
        = ENNReal.ofReal S.a * expectedCost Y A σ + ENNReal.ofReal S.p := by
      unfold expectedCost
      rw [MeasureTheory.lintegral_add_left hmul _,
        MeasureTheory.lintegral_const_mul _ hYmeas,
        MeasureTheory.lintegral_const, hprob, mul_one]
    have hmul1 := mul_le_mul_right hY (ENNReal.ofReal S.a)
    have step1 : ENNReal.ofReal S.a * expectedCost Y A σ + ENNReal.ofReal S.p
        ≤ ENNReal.ofReal S.a * (ENNReal.ofReal c * optCost Y σ
          + ENNReal.ofReal b) + ENNReal.ofReal S.p :=
      add_le_add_left hmul1 (ENNReal.ofReal S.p)
    have hmul2 := mul_le_mul_right hO (ENNReal.ofReal c)
    have hadd2 := add_le_add_left hmul2 (ENNReal.ofReal b)
    have hmul3 := mul_le_mul_right hadd2 (ENNReal.ofReal S.a)
    have hadd3 := add_le_add_left hmul3 (ENNReal.ofReal S.p)
    have step2 : ENNReal.ofReal S.a * expectedCost Y A σ + ENNReal.ofReal S.p
        ≤ ENNReal.ofReal S.a * (ENNReal.ofReal c *
          (ENNReal.ofReal S.d * optCost X σ + ENNReal.ofReal S.q)
          + ENNReal.ofReal b) + ENNReal.ofReal S.p :=
      le_trans step1 hadd3
    have e1 : ENNReal.ofReal (S.a * c * S.d)
        = ENNReal.ofReal S.a * ENNReal.ofReal c * ENNReal.ofReal S.d := by
      rw [ENNReal.ofReal_mul (mul_nonneg S.ha hc0), ENNReal.ofReal_mul S.ha]
    have e2 : ENNReal.ofReal (S.a * c * S.q + S.a * b + S.p)
        = ENNReal.ofReal S.a * ENNReal.ofReal c * ENNReal.ofReal S.q
          + ENNReal.ofReal S.a * ENNReal.ofReal b + ENNReal.ofReal S.p := by
      rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg (mul_nonneg S.ha hc0) S.hq)
        (mul_nonneg S.ha hb0)) S.hp]
      rw [ENNReal.ofReal_add (mul_nonneg (mul_nonneg S.ha hc0) S.hq)
        (mul_nonneg S.ha hb0)]
      rw [ENNReal.ofReal_mul (mul_nonneg S.ha hc0), ENNReal.ofReal_mul S.ha,
        ENNReal.ofReal_mul S.ha]
    have step3 : ENNReal.ofReal S.a * (ENNReal.ofReal c *
          (ENNReal.ofReal S.d * optCost X σ + ENNReal.ofReal S.q)
          + ENNReal.ofReal b) + ENNReal.ofReal S.p
        = ENNReal.ofReal (S.a * c * S.d) * optCost X σ
          + ENNReal.ofReal (S.a * c * S.q + S.a * b + S.p) := by
      rw [e1, e2]
      ring
    calc expectedCost X
            { μ := A.μ,
              strat := fun ω => S.F (A.strat ω) } σ
        ≤ ∫⁻ ω, (ENNReal.ofReal S.a
            * ENNReal.ofReal (algCost Y (A.strat ω) σ) + ENNReal.ofReal S.p)
            ∂(A.μ : MeasureTheory.Measure Ω) := step0
      _ = ENNReal.ofReal S.a * expectedCost Y A σ + ENNReal.ofReal S.p :=
        stepE
      _ ≤ ENNReal.ofReal S.a * (ENNReal.ofReal c *
            (ENNReal.ofReal S.d * optCost X σ + ENNReal.ofReal S.q)
            + ENNReal.ofReal b) + ENNReal.ofReal S.p := step2
      _ = ENNReal.ofReal (S.a * c * S.d) * optCost X σ
            + ENNReal.ofReal (S.a * c * S.q + S.a * b + S.p) := step3

/-- Feasible-profit supremum for an explicitly given nonnegative profit
function on traces (maximization form; the profit counterpart of
`optCost`). Profit is nonnegative by type: the maximization ratio is
meaningful only on that domain, and negative values cannot be silently
truncated. -/
noncomputable def optProfit {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (profit : List (Req × Ans) → NNReal) (σ : List Req) : ENNReal :=
  ⨆ τ ∈ {τ : List (Req × Ans) | P.feasible τ ∧ τ.map Prod.fst = σ},
    (profit τ : ENNReal)

theorem le_optProfit {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (profit : List (Req × Ans) → NNReal) {σ : List Req} {τ : List (Req × Ans)}
    (hτ : P.feasible τ) (hστ : τ.map Prod.fst = σ) :
    (profit τ : ENNReal) ≤ optProfit P profit σ := by
  unfold optProfit
  exact le_biSup (fun τ => (profit τ : ENNReal)) ⟨hτ, hστ⟩

/-- Profit-form competitiveness for maximization consumers:
`ρ • OPT_profit ≤ ALG_profit + b` with `0 ≤ ρ ≤ 1`, for a nonnegative
profit function. This is a separate predicate from the cost form; the
two are not interchangeable. -/
def ProfitCompetitive {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (profit : List (Req × Ans) → NNReal) (A : Strategy Req Ans) (ρ b : ℝ) :
    Prop :=
  0 ≤ ρ ∧ ρ ≤ 1 ∧ 0 ≤ b ∧ StrategyFeasible P A ∧
    ∀ σ : List Req, P.legal σ →
      ENNReal.ofReal ρ * optProfit P profit σ
        ≤ (profit (run A σ) : ENNReal) + ENNReal.ofReal b

/-- Randomized profit-form competitiveness: expected profit replaces the
deterministic profit. -/
def RandProfitCompetitive {Req Ans Ω : Type*} [MeasurableSpace Ω]
    (P : OnlineProblem Req Ans) (profit : List (Req × Ans) → NNReal)
    (A : RandStrategy Req Ans Ω) (ρ b : ℝ) : Prop :=
  0 ≤ ρ ∧ ρ ≤ 1 ∧ 0 ≤ b ∧ (∀ ω, StrategyFeasible P (A.strat ω)) ∧
    ∀ σ : List Req, P.legal σ →
      Measurable (fun ω => (profit (run (A.strat ω) σ) : ENNReal)) ∧
      ENNReal.ofReal ρ * optProfit P profit σ
        ≤ (∫⁻ ω, (profit (run (A.strat ω) σ) : ENNReal)
            ∂(A.μ : MeasureTheory.Measure Ω))
          + ENNReal.ofReal b

theorem ProfitCompetitive.mono {Req Ans : Type*} (P : OnlineProblem Req Ans)
    (profit : List (Req × Ans) → NNReal) (A : Strategy Req Ans) {ρ b ρ' b' : ℝ}
    (h : ProfitCompetitive P profit A ρ b) (hρ : ρ' ≤ ρ) (hb : b ≤ b')
    (hρ'0 : 0 ≤ ρ') : ProfitCompetitive P profit A ρ' b' := by
  obtain ⟨hρ0, hρ1, hb0, hA, hineq⟩ := h
  refine ⟨hρ'0, le_trans hρ hρ1, le_trans hb0 hb, hA, fun σ hσ => ?_⟩
  have hrr : ENNReal.ofReal ρ' ≤ ENNReal.ofReal ρ :=
    ENNReal.ofReal_le_ofReal hρ
  have hbb : ENNReal.ofReal b ≤ ENNReal.ofReal b' :=
    ENNReal.ofReal_le_ofReal hb
  have hmul := mul_le_mul_left hrr (optProfit P profit σ)
  exact le_trans hmul (le_trans (hineq σ hσ) (add_le_add_right hbb _))


end Cslib.Algorithms.Lean.Online.CompetitiveFramework

end

public section
