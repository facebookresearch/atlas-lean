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


end Cslib.Algorithms.Lean.Online.CompetitiveFramework

end

public section
