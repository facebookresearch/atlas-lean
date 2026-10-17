/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Cslib.BusyBeaver

/-!
# Busy Beaver machines and the first undecidable value

Two-symbol Turing machines with `n` working states plus a halt state,
started on the blank tape. `busyBeaverSteps n` is Rado's shift function
`S(n)`: the largest halting time of an `n`-state machine. `busyBeaverOnes n`
is the score function `Σ(n)`: the largest number of ones left on the tape
by a halting `n`-state machine.

Catalogue constant 14a asks for the smallest `n` whose Busy Beaver value
is undecidable in ZFC. ZFC itself is not formalized in this repository, so
the constant is modelled relative to an abstract formal theory
(`FormalTheory`, a provability predicate on syntactic sentence codes in
`ℕ`, with halting, non-halting, false, and runtime-bound sentences given
explicit codes and meanings through separate soundness hypotheses):
`firstUndecidable T` is the least number of states at which `T` fails to
decide halting for every machine. A `ZFCPresentation` packages a theory
with an explicit proof checker and the verification properties used to
derive decidability through five states. The elementary backbone proved
here is `S(0) = 0`, `S(1) = 1`, `Σ(1) = 1`, monotonicity of both
functions, the bound `Σ(n) ≤ S(n)`, attainability of both maxima,
downward closure of theory-decidability under explicit proof-transport
hypotheses, and decidability through five states for any
`ZFCPresentation`. The numerical catalogue bounds are registered as
proof requests in the wanted file, with the model gap.

Source: Optimization Problems, constants/14a.md, frozen at
teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`.
-/

/-- Head movement direction. -/
inductive Move where
  | left
  | right
deriving DecidableEq

instance : Fintype Move where
  elems := {Move.left, Move.right}
  complete := by
    intro m
    cases m <;> simp

/-- The displacement of a head movement. -/
def Move.shift : Move → ℤ
  | .left => -1
  | .right => 1

/-- A Busy Beaver machine with `n` working states: for each state and read
symbol, the symbol to write, the head movement, and the next state, where
`none` is the halt state. The write and move of a halting transition are
still performed, and the halting step counts toward the runtime. -/
abbrev Machine (n : ℕ) :=
  Fin n → Fin 2 → Fin 2 × Move × Option (Fin n)

/-- A machine configuration: current state (`none` once halted), head
position, and tape contents. -/
structure Config (n : ℕ) where
  state : Option (Fin n)
  head : ℤ
  tape : ℤ → Fin 2

/-- One execution step. A halted configuration is fixed. -/
def step {n : ℕ} (M : Machine n) (c : Config n) : Config n :=
  match c.state with
  | none => c
  | some q =>
    let a := M q (c.tape c.head)
    ⟨a.2.2, c.head + a.2.1.shift, Function.update c.tape c.head a.1⟩

theorem step_of_state_none {n : ℕ} (M : Machine n) {c : Config n}
    (h : c.state = none) : step M c = c := by
  unfold step
  rw [h]

theorem step_of_state_some {n : ℕ} (M : Machine n) {c : Config n}
    {q : Fin n} (h : c.state = some q) :
    step M c = ⟨(M q (c.tape c.head)).2.2,
      c.head + (M q (c.tape c.head)).2.1.shift,
      Function.update c.tape c.head (M q (c.tape c.head)).1⟩ := by
  unfold step
  rw [h]

theorem step_state_of_some {n : ℕ} (M : Machine n) {c : Config n}
    {q : Fin n} (h : c.state = some q) :
    (step M c).state = (M q (c.tape c.head)).2.2 := by
  rw [step_of_state_some M h]

theorem step_head_of_some {n : ℕ} (M : Machine n) {c : Config n}
    {q : Fin n} (h : c.state = some q) :
    (step M c).head = c.head + (M q (c.tape c.head)).2.1.shift := by
  rw [step_of_state_some M h]

theorem step_tape_of_some {n : ℕ} (M : Machine n) {c : Config n}
    {q : Fin n} (h : c.state = some q) :
    (step M c).tape =
      Function.update c.tape c.head (M q (c.tape c.head)).1 := by
  rw [step_of_state_some M h]

/-- The initial state: state `0` if it exists, halted for `n = 0`. -/
def initialState (n : ℕ) : Option (Fin n) :=
  if h : 0 < n then some ⟨0, h⟩ else none

/-- The initial configuration on the blank tape. -/
def initial (n : ℕ) : Config n :=
  ⟨initialState n, 0, fun _ => 0⟩

/-- The configuration after `t` steps. -/
def run {n : ℕ} (M : Machine n) (t : ℕ) : Config n :=
  (step M)^[t] (initial n)

theorem run_zero {n : ℕ} (M : Machine n) : run M 0 = initial n := rfl

theorem run_succ {n : ℕ} (M : Machine n) (t : ℕ) :
    run M (t + 1) = step M (run M t) :=
  Function.iterate_succ_apply' (step M) t (initial n)

/-- The machine has halted within `t` steps. -/
def HaltsWithin {n : ℕ} (M : Machine n) (t : ℕ) : Prop :=
  (run M t).state = none

/-- The machine halts on the blank tape. -/
def Halts {n : ℕ} (M : Machine n) : Prop :=
  ∃ t, HaltsWithin M t

theorem haltsWithin_mono {n : ℕ} {M : Machine n} {s t : ℕ}
    (h : HaltsWithin M s) (hst : s ≤ t) : HaltsWithin M t := by
  have key : ∀ k : ℕ, HaltsWithin M (s + k) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have hs : (run M (s + k)).state = none := ih
      show (run M (s + (k + 1))).state = none
      rw [show s + (k + 1) = (s + k) + 1 by ring, run_succ,
        step_of_state_none M hs]
      exact hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  exact key k

/-- The halting time of a halting machine. -/
noncomputable def haltTime {n : ℕ} (M : Machine n) (h : Halts M) : ℕ :=
  @Nat.find _ (fun t => Classical.propDecidable _) h

theorem haltsWithin_haltTime {n : ℕ} (M : Machine n) (h : Halts M) :
    HaltsWithin M (haltTime M h) := by
  classical
  exact Nat.find_spec h

theorem haltTime_le {n : ℕ} (M : Machine n) (h : Halts M) {t : ℕ}
    (ht : HaltsWithin M t) : haltTime M h ≤ t := by
  classical
  exact Nat.find_le ht

/-- After `t` steps the head is within distance `t` of the origin. -/
theorem abs_head_le {n : ℕ} (M : Machine n) (t : ℕ) :
    |(run M t).head| ≤ t := by
  induction t with
  | zero => simp [run, initial]
  | succ t ih =>
    rw [run_succ]
    by_cases hs : (run M t).state = none
    · rw [step_of_state_none M hs]
      exact ih.trans (by exact_mod_cast Nat.le_succ t)
    · obtain ⟨q, hq⟩ : ∃ q, (run M t).state = some q := by
        cases h : (run M t).state with
        | none => exact absurd h hs
        | some q => exact ⟨q, rfl⟩
      rw [step_head_of_some M hq]
      have hshift : |(M q ((run M t).tape (run M t).head)).2.1.shift| = 1 := by
        cases (M q ((run M t).tape (run M t).head)).2.1 <;> rfl
      calc |(run M t).head + (M q ((run M t).tape (run M t).head)).2.1.shift|
          ≤ |(run M t).head| +
            |(M q ((run M t).tape (run M t).head)).2.1.shift| :=
            abs_add_le _ _
        _ ≤ t + 1 := by
            rw [hshift]
            have := ih
            push_cast at this ⊢
            linarith
        _ = ((t + 1 : ℕ) : ℤ) := by push_cast; ring

/-- After `t` steps every cell at distance greater than `t` is blank. -/
theorem tape_eq_zero_of_abs_gt {n : ℕ} (M : Machine n) (t : ℕ)
    {i : ℤ} (hi : t < |i|) : (run M t).tape i = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ]
    by_cases hs : (run M t).state = none
    · rw [step_of_state_none M hs]
      refine ih ?_
      have h1 : ((t : ℕ) : ℤ) < |i| := by
        have h2 : ((t + 1 : ℕ) : ℤ) < |i| := hi
        push_cast at h2 ⊢
        linarith
      exact_mod_cast h1
    · obtain ⟨q, hq⟩ : ∃ q, (run M t).state = some q := by
        cases h : (run M t).state with
        | none => exact absurd h hs
        | some q => exact ⟨q, rfl⟩
      rw [step_tape_of_some M hq]
      have hhead : |(run M t).head| ≤ t := abs_head_le M t
      have hne : i ≠ (run M t).head := by
        intro h
        rw [h] at hi
        have hle : |(run M t).head| ≤ ((t + 1 : ℕ) : ℤ) := by
          refine hhead.trans ?_
          exact_mod_cast Nat.le_succ t
        linarith
      rw [Function.update_of_ne hne]
      exact ih (by
        have h1 : ((t : ℕ) : ℤ) < |i| := by
          have h2 : ((t + 1 : ℕ) : ℤ) < |i| := hi
          push_cast at h2 ⊢
          linarith
        exact_mod_cast h1)

/-- The number of ones on the tape after `t` steps, counted on the finite
window that the head can have reached. -/
def onesAt {n : ℕ} (M : Machine n) (t : ℕ) : ℕ :=
  ((Finset.Icc (-(t : ℤ)) t).filter fun i => (run M t).tape i = 1).card

theorem onesAt_le {n : ℕ} (M : Machine n) (t : ℕ) :
    onesAt M t ≤ 2 * t + 1 := by
  refine (Finset.card_filter_le _ _).trans_eq ?_
  rw [Int.card_Icc]
  omega

/-- Every one on the tape after `t` steps lies in the counting window. -/
theorem mem_window_of_tape_eq_one {n : ℕ} (M : Machine n) (t : ℕ) {i : ℤ}
    (hi : (run M t).tape i = 1) : i ∈ Finset.Icc (-(t : ℤ)) t := by
  rw [Finset.mem_Icc, ← abs_le]
  by_contra hcon
  have habs : (t : ℤ) < |i| := lt_of_not_ge hcon
  have h0 : (run M t).tape i = 0 := tape_eq_zero_of_abs_gt M t habs
  rw [hi] at h0
  exact one_ne_zero h0

/-- A step writes at most one additional one. -/
theorem onesAt_succ_le {n : ℕ} (M : Machine n) (t : ℕ) :
    onesAt M (t + 1) ≤ onesAt M t + 1 := by
  by_cases hs : (run M t).state = none
  · have hstep : run M (t + 1) = run M t := by
      rw [run_succ, step_of_state_none M hs]
    have htape : (run M (t + 1)).tape = (run M t).tape := by rw [hstep]
    have hfilter : (Finset.Icc (-((t + 1 : ℕ) : ℤ)) ((t + 1 : ℕ) : ℤ)).filter
        (fun i => (run M (t + 1)).tape i = 1) =
        (Finset.Icc (-(t : ℤ)) t).filter (fun i => (run M t).tape i = 1) := by
      apply Finset.Subset.antisymm
      · intro i hi
        obtain ⟨_hiI, hi1⟩ := Finset.mem_filter.mp hi
        rw [htape] at hi1
        exact Finset.mem_filter.mpr
          ⟨mem_window_of_tape_eq_one M t hi1, hi1⟩
      · intro i hi
        obtain ⟨hiI, hi1⟩ := Finset.mem_filter.mp hi
        apply Finset.mem_filter.mpr
        constructor
        · rw [Finset.mem_Icc] at hiI ⊢
          push_cast
          omega
        · rwa [htape]
    show onesAt M (t + 1) ≤ onesAt M t + 1
    rw [onesAt, onesAt, hfilter]
    exact Nat.le_succ _
  · obtain ⟨q, hq⟩ : ∃ q, (run M t).state = some q := by
      cases h : (run M t).state with
      | none => exact absurd h hs
      | some q => exact ⟨q, rfl⟩
    set p := (run M t).head with hp
    have htape : (run M (t + 1)).tape =
        Function.update (run M t).tape p
          (M q ((run M t).tape p)).1 := by
      rw [run_succ]
      exact step_tape_of_some M hq
    have hsub : (Finset.Icc (-((t + 1 : ℕ) : ℤ)) ((t + 1 : ℕ) : ℤ)).filter
        (fun i => (run M (t + 1)).tape i = 1) ⊆
        insert p ((Finset.Icc (-(t : ℤ)) t).filter
          (fun i => (run M t).tape i = 1)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_Icc] at hi
      rw [htape] at hi
      by_cases hip : i = p
      · rw [Finset.mem_insert]
        exact Or.inl hip
      · rw [Function.update_of_ne hip] at hi
        rw [Finset.mem_insert]
        refine Or.inr ?_
        simp only [Finset.mem_filter]
        exact ⟨mem_window_of_tape_eq_one M t hi.2, hi.2⟩
    calc onesAt M (t + 1)
        ≤ (insert p ((Finset.Icc (-(t : ℤ)) t).filter
            (fun i => (run M t).tape i = 1))).card :=
          Finset.card_le_card hsub
      _ ≤ ((Finset.Icc (-(t : ℤ)) t).filter
            (fun i => (run M t).tape i = 1)).card + 1 :=
          Finset.card_insert_le _ _
      _ = onesAt M t + 1 := rfl

theorem onesAt_zero {n : ℕ} (M : Machine n) : onesAt M 0 = 0 := by
  rw [onesAt]
  simp [run_zero, initial]

/-- Ones are created one per step. -/
theorem onesAt_le_steps {n : ℕ} (M : Machine n) (t : ℕ) :
    onesAt M t ≤ t := by
  induction t with
  | zero => rw [onesAt_zero]
  | succ t ih =>
    exact (onesAt_succ_le M t).trans (Nat.add_le_add_right ih 1)

/-- The runtime contributed by a machine to the Busy Beaver maximum:
its halting time if it halts, and `0` otherwise. -/
noncomputable def stepsOf {n : ℕ} (M : Machine n) : ℕ :=
  @dite ℕ (Halts M) (Classical.propDecidable _) (fun h => haltTime M h)
    (fun _ => 0)

/-- The ones score contributed by a machine: the ones on its final tape
if it halts, and `0` otherwise. -/
noncomputable def scoreOf {n : ℕ} (M : Machine n) : ℕ :=
  @dite ℕ (Halts M) (Classical.propDecidable _)
    (fun h => onesAt M (haltTime M h)) (fun _ => 0)

/-- Rado's shift function `S(n)`: the largest halting time of an `n`-state
two-symbol machine started on the blank tape. -/
noncomputable def busyBeaverSteps (n : ℕ) : ℕ :=
  (Finset.univ : Finset (Machine n)).sup stepsOf

/-- Rado's score function `Σ(n)`: the largest number of ones left on the
tape by a halting `n`-state two-symbol machine. -/
noncomputable def busyBeaverOnes (n : ℕ) : ℕ :=
  (Finset.univ : Finset (Machine n)).sup scoreOf

theorem haltTime_le_busyBeaverSteps {n : ℕ} (M : Machine n) (h : Halts M) :
    haltTime M h ≤ busyBeaverSteps n := by
  have h1 : stepsOf M = haltTime M h := by
    rw [stepsOf, dif_pos h]
  rw [busyBeaverSteps, ← h1]
  exact Finset.le_sup (Finset.mem_univ M)

theorem scoreOf_le_busyBeaverOnes {n : ℕ} (M : Machine n) :
    scoreOf M ≤ busyBeaverOnes n := by
  rw [busyBeaverOnes]
  exact Finset.le_sup (Finset.mem_univ M)

theorem busyBeaverSteps_le_of_forall_le {n B : ℕ}
    (hB : ∀ M : Machine n, ∀ h : Halts M, haltTime M h ≤ B) :
    busyBeaverSteps n ≤ B := by
  rw [busyBeaverSteps]
  apply Finset.sup_le
  intro M _hM
  by_cases h : Halts M
  · have h1 : stepsOf M = haltTime M h := by rw [stepsOf, dif_pos h]
    rw [h1]
    exact hB M h
  · have h1 : stepsOf M = 0 := by rw [stepsOf, dif_neg h]
    rw [h1]
    exact Nat.zero_le B

theorem scoreOf_le_stepsOf {n : ℕ} (M : Machine n) :
    scoreOf M ≤ stepsOf M := by
  by_cases h : Halts M
  · rw [scoreOf, stepsOf, dif_pos h, dif_pos h]
    exact onesAt_le_steps M _
  · rw [scoreOf, stepsOf, dif_neg h, dif_neg h]

/-- The score never exceeds the runtime, at the level of the maxima. -/
theorem busyBeaverOnes_le_steps (n : ℕ) :
    busyBeaverOnes n ≤ busyBeaverSteps n := by
  rw [busyBeaverOnes, busyBeaverSteps]
  apply Finset.sup_le
  intro M _hM
  exact (scoreOf_le_stepsOf M).trans (Finset.le_sup (Finset.mem_univ M))

/-- The step maximum is attained by a halting machine (or is zero). -/
theorem exists_stepsOf_eq (n : ℕ) :
    ∃ M : Machine n, stepsOf M = busyBeaverSteps n := by
  obtain ⟨M, _hM, hM⟩ := Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Machine n)))
    (f := stepsOf) ⟨fun _ _ => (0, Move.left, none), Finset.mem_univ _⟩
  refine ⟨M, ?_⟩
  rw [busyBeaverSteps]
  exact hM.symm

/-- The score maximum is attained by a halting machine (or is zero). -/
theorem exists_scoreOf_eq (n : ℕ) :
    ∃ M : Machine n, scoreOf M = busyBeaverOnes n := by
  obtain ⟨M, _hM, hM⟩ := Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Machine n)))
    (f := scoreOf) ⟨fun _ _ => (0, Move.left, none), Finset.mem_univ _⟩
  refine ⟨M, ?_⟩
  rw [busyBeaverOnes]
  exact hM.symm

/-- Embed an `n`-state machine into `n + 1` states, leaving the new state
unreachable (it halts immediately if ever entered). -/
def embedMachine {n : ℕ} (M : Machine n) : Machine (n + 1) :=
  fun q s =>
    if h : q.val < n then
      let a := M ⟨q.val, h⟩ s
      (a.1, a.2.1, a.2.2.map Fin.castSucc)
    else (0, Move.left, none)

/-- Embed a configuration along `Fin.castSucc`. -/
def embedConfig {n : ℕ} (c : Config n) : Config (n + 1) :=
  ⟨c.state.map Fin.castSucc, c.head, c.tape⟩

@[simp]
theorem embedConfig_state {n : ℕ} (c : Config n) :
    (embedConfig c).state = c.state.map Fin.castSucc := rfl

@[simp]
theorem embedConfig_head {n : ℕ} (c : Config n) :
    (embedConfig c).head = c.head := rfl

@[simp]
theorem embedConfig_tape {n : ℕ} (c : Config n) :
    (embedConfig c).tape = c.tape := rfl

theorem embedMachine_castSucc {n : ℕ} (M : Machine n) (q : Fin n)
    (s : Fin 2) :
    embedMachine M (Fin.castSucc q) s =
      ((M q s).1, (M q s).2.1, (M q s).2.2.map Fin.castSucc) := by
  unfold embedMachine
  rw [dif_pos (show (Fin.castSucc q).val < n from q.isLt)]
  rfl

theorem embedConfig_step {n : ℕ} (M : Machine n) (c : Config n) :
    embedConfig (step M c) = step (embedMachine M) (embedConfig c) := by
  cases hs : c.state with
  | none =>
    have h1 : step M c = c := step_of_state_none M hs
    have hs2 : (embedConfig c).state = none := by
      rw [embedConfig_state, hs]
      rfl
    have h2 : step (embedMachine M) (embedConfig c) = embedConfig c :=
      step_of_state_none (embedMachine M) hs2
    rw [h1, h2]
  | some q =>
    have hs2 : (embedConfig c).state = some (Fin.castSucc q) := by
      rw [embedConfig_state, hs]
      rfl
    rw [step_of_state_some M hs, step_of_state_some (embedMachine M) hs2,
      embedConfig_tape, embedConfig_head, embedMachine_castSucc]
    rfl

theorem embedConfig_initial {n : ℕ} (hn : 0 < n) :
    embedConfig (initial n) = initial (n + 1) := by
  rw [embedConfig, initial, initial]
  congr 1
  rw [initialState, initialState, dif_pos hn, dif_pos (Nat.succ_pos n)]
  rfl

theorem embedConfig_run {n : ℕ} (hn : 0 < n) (M : Machine n) (t : ℕ) :
    embedConfig (run M t) = run (embedMachine M) t := by
  induction t with
  | zero => rw [run_zero, run_zero, embedConfig_initial hn]
  | succ t ih => rw [run_succ, run_succ, ← ih, embedConfig_step]

theorem state_eq_none_of_map_eq_none {n : ℕ} {o : Option (Fin n)}
    (h : o.map Fin.castSucc = none) : o = none := by
  cases o with
  | none => rfl
  | some q => simp at h

theorem halts_embed {n : ℕ} (hn : 0 < n) (M : Machine n) :
    Halts (embedMachine M) ↔ Halts M := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have ht' : (run (embedMachine M) t).state = none := ht
    rw [← embedConfig_run hn M t] at ht'
    have : (run M t).state = none := by
      have h := ht'
      rw [embedConfig_state] at h
      exact state_eq_none_of_map_eq_none h
    exact this
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    show (run (embedMachine M) t).state = none
    rw [← embedConfig_run hn M t]
    rw [embedConfig_state]
    have ht' : (run M t).state = none := ht
    rw [ht']
    rfl

theorem haltTime_embed {n : ℕ} (hn : 0 < n) (M : Machine n) (h : Halts M) :
    haltTime (embedMachine M) ((halts_embed hn M).mpr h) = haltTime M h := by
  have hto : ∀ t, HaltsWithin (embedMachine M) t ↔ HaltsWithin M t := by
    intro t
    constructor
    · intro ht
      have ht' : (run (embedMachine M) t).state = none := ht
      rw [← embedConfig_run hn M t] at ht'
      rw [embedConfig_state] at ht'
      exact state_eq_none_of_map_eq_none ht'
    · intro ht
      have ht' : (run M t).state = none := ht
      show (run (embedMachine M) t).state = none
      rw [← embedConfig_run hn M t, embedConfig_state, ht']
      rfl
  apply Nat.le_antisymm
  · exact haltTime_le (embedMachine M) ((halts_embed hn M).mpr h)
      ((hto _).mpr (haltsWithin_haltTime M h))
  · have hspec := haltsWithin_haltTime (embedMachine M)
      ((halts_embed hn M).mpr h)
    exact haltTime_le M h ((hto _).mp hspec)

theorem busyBeaverSteps_zero : busyBeaverSteps 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply busyBeaverSteps_le_of_forall_le
  intro M h
  have h0 : HaltsWithin M 0 := by
    simp [HaltsWithin, run_zero, initial, initialState]
  exact haltTime_le M h h0

theorem busyBeaverSteps_mono (n : ℕ) :
    busyBeaverSteps n ≤ busyBeaverSteps (n + 1) := by
  cases n with
  | zero => rw [busyBeaverSteps_zero]; exact Nat.zero_le _
  | succ n =>
    rw [busyBeaverSteps, busyBeaverSteps]
    apply Finset.sup_le
    intro M _hM
    by_cases h : Halts M
    · have hsteps : stepsOf M = haltTime M h := by rw [stepsOf, dif_pos h]
      have hembed : stepsOf (embedMachine M) = haltTime M h := by
        rw [stepsOf, dif_pos ((halts_embed (Nat.succ_pos n) M).mpr h)]
        exact haltTime_embed (Nat.succ_pos n) M h
      rw [hsteps, ← hembed]
      exact Finset.le_sup (Finset.mem_univ _)
    · have hsteps : stepsOf M = 0 := by rw [stepsOf, dif_neg h]
      rw [hsteps]
      exact Nat.zero_le _

theorem busyBeaverOnes_mono (n : ℕ) :
    busyBeaverOnes n ≤ busyBeaverOnes (n + 1) := by
  cases n with
  | zero =>
    have h0 : busyBeaverOnes 0 ≤ busyBeaverSteps 0 := busyBeaverOnes_le_steps 0
    rw [busyBeaverSteps_zero] at h0
    omega
  | succ n =>
    rw [busyBeaverOnes, busyBeaverOnes]
    apply Finset.sup_le
    intro M _hM
    by_cases h : Halts M
    · have hscore : scoreOf (embedMachine M) = scoreOf M := by
        rw [scoreOf, scoreOf,
          dif_pos ((halts_embed (Nat.succ_pos n) M).mpr h), dif_pos h,
          haltTime_embed (Nat.succ_pos n) M h]
        have hrun : run (embedMachine M) (haltTime M h) =
            embedConfig (run M (haltTime M h)) := by
          rw [embedConfig_run (Nat.succ_pos n)]
        rw [onesAt, onesAt, hrun]
        rfl
      rw [← hscore]
      exact Finset.le_sup (Finset.mem_univ _)
    · have hscore : scoreOf M = 0 := by rw [scoreOf, dif_neg h]
      rw [hscore]
      exact Nat.zero_le _

theorem initial_one_state : (initial 1).state = some (0 : Fin 1) := by
  simp [initial, initialState]

theorem run_one (M : Machine 1) :
    run M 1 = step M (initial 1) :=
  (run_succ M 0).trans (by rw [run_zero])

theorem run_one_state (M : Machine 1) :
    (run M 1).state = (M 0 0).2.2 := by
  rw [run_one]
  exact step_state_of_some M initial_one_state

theorem not_haltsWithin_zero_one (M : Machine 1) :
    ¬ HaltsWithin M 0 := by
  rw [HaltsWithin, run_zero, initial_one_state]
  simp

/-- A one-state machine whose blank transition returns to its only state
marches in one direction forever and never halts: at every step the head
is on a previously unvisited blank cell. -/
theorem not_halts_of_one_state_march (M : Machine 1)
    (hnext : (M 0 0).2.2 = some 0) : ¬ Halts M := by
  set s : ℤ := (M 0 0).2.1.shift with hs
  have hsabs : |s| = 1 := by
    rw [hs]
    cases (M 0 0).2.1 <;> rfl
  have key : ∀ t : ℕ, (run M t).state = some (0 : Fin 1) ∧
      (run M t).head = (t : ℤ) * s ∧ (run M t).tape ((t : ℤ) * s) = 0 := by
    intro t
    induction t with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · rw [run_zero]
        exact initial_one_state
      · simp [run_zero, initial]
      · simp [run_zero, initial]
    | succ t ih =>
      obtain ⟨hstate, hhead, htape⟩ := ih
      have hstepstate : (run M (t + 1)).state =
          (M 0 ((run M t).tape (run M t).head)).2.2 := by
        rw [run_succ]
        exact step_state_of_some M hstate
      have hstephead : (run M (t + 1)).head =
          (run M t).head + (M 0 ((run M t).tape (run M t).head)).2.1.shift := by
        rw [run_succ]
        exact step_head_of_some M hstate
      have hstepetape : (run M (t + 1)).tape =
          Function.update (run M t).tape (run M t).head
            (M 0 ((run M t).tape (run M t).head)).1 := by
        rw [run_succ]
        exact step_tape_of_some M hstate
      have hread : (run M t).tape (run M t).head = 0 := by
        rw [hhead]
        exact htape
      refine ⟨?_, ?_, ?_⟩
      · rw [hstepstate, hread, hnext]
      · rw [hstephead, hread, hhead]
        push_cast
        ring
      · have hnewhead : ((t + 1 : ℕ) : ℤ) * s = (t : ℤ) * s + s := by
          push_cast
          ring
        have hold : (run M t).tape (((t + 1 : ℕ) : ℤ) * s) = 0 := by
          refine tape_eq_zero_of_abs_gt M t ?_
          rw [hnewhead]
          have h1 : |((t : ℤ) * s + s)| = (t : ℤ) + 1 := by
            have hfact : (t : ℤ) * s + s = ((t : ℤ) + 1) * s := by ring
            rw [hfact, abs_mul, hsabs, mul_one,
              abs_of_nonneg (by positivity)]
          rw [h1]
          have h2 : ((t : ℕ) : ℤ) < (t : ℤ) + 1 := by
            push_cast
            linarith
          exact_mod_cast h2
        rw [hstepetape, hhead]
        rw [Function.update_of_ne]
        · exact hold
        · intro hcon
          have hsne : s ≠ 0 := by
            intro h0
            rw [h0] at hsabs
            simp at hsabs
          rw [hnewhead] at hcon
          have : (t : ℤ) * s + s = (t : ℤ) * s → s = 0 := by
            intro h
            linarith
          exact hsne (this hcon)
  rintro ⟨t, ht⟩
  have ht' : (run M t).state = none := ht
  rw [(key t).1] at ht'
  simp at ht'

/-- Every halting one-state machine halts within one step. -/
theorem haltsWithin_one_of_halts (M : Machine 1) (h : Halts M) :
    HaltsWithin M 1 := by
  by_contra hcon
  apply not_halts_of_one_state_march M _ h
  have hne : (run M 1).state ≠ none := hcon
  rw [run_one_state] at hne
  cases hnext : (M 0 0).2.2 with
  | none => exact absurd hnext hne
  | some q =>
    have : q = 0 := Fin.ext (Nat.lt_one_iff.mp q.isLt)
    rw [this]

theorem haltTime_one_of_halts {M : Machine 1} (h : Halts M) :
    haltTime M h = 1 := by
  have hle := haltTime_le M h (haltsWithin_one_of_halts M h)
  have hspec := haltsWithin_haltTime M h
  rcases Nat.eq_zero_or_pos (haltTime M h) with h0 | hpos
  · rw [h0] at hspec
    exact absurd hspec (not_haltsWithin_zero_one M)
  · omega

theorem busyBeaverSteps_one : busyBeaverSteps 1 = 1 := by
  apply Nat.le_antisymm
  · apply busyBeaverSteps_le_of_forall_le
    intro M h
    exact haltTime_le M h (haltsWithin_one_of_halts M h)
  · have hM : Halts (fun _ _ => (1, Move.right, none) : Machine 1) :=
      ⟨1, run_one_state _⟩
    have htime : haltTime (fun _ _ => (1, Move.right, none) : Machine 1) hM =
        1 := haltTime_one_of_halts hM
    have hle := haltTime_le_busyBeaverSteps
      (fun _ _ => (1, Move.right, none) : Machine 1) hM
    rw [htime] at hle
    exact hle

theorem busyBeaverOnes_one : busyBeaverOnes 1 = 1 := by
  apply Nat.le_antisymm
  · exact (busyBeaverOnes_le_steps 1).trans_eq busyBeaverSteps_one
  · have hM : Halts (fun _ _ => (1, Move.right, none) : Machine 1) :=
      ⟨1, run_one_state _⟩
    have htime : haltTime (fun _ _ => (1, Move.right, none) : Machine 1) hM =
        1 := haltTime_one_of_halts hM
    have hscore : scoreOf (fun _ _ => (1, Move.right, none) : Machine 1) = 1 := by
      rw [scoreOf, dif_pos hM, htime]
      have htape : (run (fun _ _ => (1, Move.right, none) : Machine 1) 1).tape
          (0 : ℤ) = 1 := by
        rw [run_one]
        have h2 := step_tape_of_some
          (fun _ _ => (1, Move.right, none) : Machine 1) initial_one_state
        rw [h2]
        rfl
      have hmem : (0 : ℤ) ∈ (Finset.Icc (-(1 : ℤ)) 1).filter
          (fun i => (run (fun _ _ => (1, Move.right, none) : Machine 1) 1).tape
            i = 1) := by
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by norm_num, by norm_num⟩, htape⟩
      have hcard : 0 < onesAt (fun _ _ => (1, Move.right, none) : Machine 1) 1 := by
        rw [onesAt]
        exact Finset.card_pos.mpr ⟨0, hmem⟩
      have hle : onesAt (fun _ _ => (1, Move.right, none) : Machine 1) 1 ≤ 1 :=
        onesAt_le_steps _ 1
      omega
    have hle := scoreOf_le_busyBeaverOnes
      (fun _ _ => (1, Move.right, none) : Machine 1)
    rw [hscore] at hle
    exact hle

/-- A code for a machine, as a natural number: the pair of its state
count and its index in an enumeration of all machines with that many
states. -/
noncomputable def machineCode {n : ℕ} (M : Machine n) : ℕ :=
  Nat.pair n (Fintype.equivFinOfCardEq (α := Machine n) rfl M).val

/-- A syntactic sentence code, by tag and payload: tag `0` says the
coded machine halts, tag `1` says it does not halt, tag `2` is the
false sentence, and tag `3` with payload `Nat.pair n B` says every
halting `n`-state machine halts within `B` steps. Sentences are natural
numbers, not Lean propositions, so provability does not collapse under
`propext`. -/
def sentenceCode (tag payload : ℕ) : ℕ :=
  4 * payload + tag

/-- The sentence "the machine halts on the blank tape". -/
noncomputable def haltsSentence {n : ℕ} (M : Machine n) : ℕ :=
  sentenceCode 0 (machineCode M)

/-- The sentence "the machine does not halt on the blank tape". -/
noncomputable def notHaltsSentence {n : ℕ} (M : Machine n) : ℕ :=
  sentenceCode 1 (machineCode M)

/-- The false sentence. -/
def falseSentence : ℕ :=
  sentenceCode 2 0

/-- The sentence "every halting `n`-state machine halts within `B`
steps". -/
def boundSentence (n B : ℕ) : ℕ :=
  sentenceCode 3 (Nat.pair n B)

theorem haltsSentence_ne_falseSentence {n : ℕ} (M : Machine n) :
    haltsSentence M ≠ falseSentence := by
  unfold haltsSentence falseSentence sentenceCode
  omega

theorem notHaltsSentence_ne_falseSentence {n : ℕ} (M : Machine n) :
    notHaltsSentence M ≠ falseSentence := by
  unfold notHaltsSentence falseSentence sentenceCode
  omega

theorem boundSentence_ne_falseSentence (n B : ℕ) :
    boundSentence n B ≠ falseSentence := by
  unfold boundSentence falseSentence sentenceCode
  omega

/-- An abstract formal theory, given by a provability predicate on
syntactic sentence codes (natural numbers). The theory is a
metatheoretic parameter: ZFC itself, including its syntax and proof
checker, is not formalized in this repository. Meaning is assigned to
specific families of codes (`haltsSentence`, `notHaltsSentence`,
`falseSentence`, `boundSentence`) through separate soundness
hypotheses; no meaning is assigned to other codes here. -/
structure FormalTheory where
  /-- Provability of a sentence code in the theory. -/
  Provable : ℕ → Prop

/-- The theory is consistent: it does not prove the false sentence. -/
def Consistent (T : FormalTheory) : Prop :=
  ¬ T.Provable falseSentence

/-- Soundness for halting sentences: a proof of a halting (resp.
non-halting) sentence implies the machine really halts (resp. does not
halt). -/
def SoundForHalting (T : FormalTheory) : Prop :=
  (∀ {n : ℕ} (M : Machine n), T.Provable (haltsSentence M) → Halts M) ∧
  (∀ {n : ℕ} (M : Machine n),
    T.Provable (notHaltsSentence M) → ¬ Halts M)

/-- The theory decides halting for every `n`-state machine: for each
machine it proves its halting sentence or its non-halting sentence. -/
def DecidesHalting (T : FormalTheory) (n : ℕ) : Prop :=
  ∀ M : Machine n,
    T.Provable (haltsSentence M) ∨ T.Provable (notHaltsSentence M)

/-- The first number of states at which the theory fails to decide
halting for all machines, or `0` when there is no such number of states.
For ZFC this is catalogue constant 14a; the `0` junk case corresponds to
a theory deciding halting at every size. -/
noncomputable def firstUndecidable (T : FormalTheory) : ℕ :=
  sInf {n | ¬ DecidesHalting T n}

theorem firstUndecidable_le_of_not_decides {T : FormalTheory} {n : ℕ}
    (h : ¬ DecidesHalting T n) : firstUndecidable T ≤ n :=
  Nat.sInf_le h

theorem not_decides_firstUndecidable {T : FormalTheory}
    (h : ∃ n, ¬ DecidesHalting T n) :
    ¬ DecidesHalting T (firstUndecidable T) :=
  Nat.sInf_mem h

/-- If a theory decides halting for all machines with at most five
states but fails somewhere, its first undecidable size is at least six.
This is the shape of the catalogue lower bound from the determination of
`BB(5)`. -/
theorem six_le_firstUndecidable_of_decides_le_five {T : FormalTheory}
    (h5 : ∀ n ≤ 5, DecidesHalting T n)
    (hex : ∃ n, ¬ DecidesHalting T n) :
    6 ≤ firstUndecidable T := by
  have hmem := not_decides_firstUndecidable hex
  by_contra hcon
  push Not at hcon
  exact hmem (h5 (firstUndecidable T) (by omega))

/-- A consistency-search machine blocks decidability at its size: if
`M` halts exactly when `T` proves the false sentence, `T` is consistent
and sound for the halting sentence of `M`, and `T` does not prove the
non-halting sentence of `M` (the Gödel second-incompleteness content
for ZFC), then `T` does not decide halting for all machines of that
size. -/
theorem not_decides_of_consistency_machine {T : FormalTheory} {n : ℕ}
    (M : Machine n) (hM : Halts M ↔ T.Provable falseSentence)
    (hsound : T.Provable (haltsSentence M) → Halts M)
    (hcons : Consistent T)
    (hnot : ¬ T.Provable (notHaltsSentence M)) :
    ¬ DecidesHalting T n := by
  intro hdec
  rcases hdec M with h1 | h1
  · exact hcons (hM.mp (hsound h1))
  · exact hnot h1

/-- Decidability propagates to fewer states when provability of
halting sentences transports along the state embedding: an `n`-state
machine embeds into `n + 1` states with the same halting behaviour.
The transport hypotheses are the point where a real theory would
rewrite a proof about the embedded machine into a proof about the
original machine; they are stated explicitly because provability of
one sentence code does not formally imply provability of another. -/
theorem decidesHalting_of_succ {T : FormalTheory}
    (htransport : ∀ {n : ℕ} (M : Machine n),
      (T.Provable (haltsSentence (embedMachine M)) →
        T.Provable (haltsSentence M)) ∧
      (T.Provable (notHaltsSentence (embedMachine M)) →
        T.Provable (notHaltsSentence M)))
    {n : ℕ} (h : DecidesHalting T (n + 1)) :
    DecidesHalting T n := by
  intro M
  rcases h (embedMachine M) with h1 | h1
  · exact Or.inl ((htransport M).1 h1)
  · exact Or.inr ((htransport M).2 h1)

/-- A presentation of a ZFC-like theory by an explicit proof checker:
`check p s` says `p` is a proof of the sentence coded by `s`. The
bundle records exactly the properties used in this file: provability
is existence of a checked proof, soundness for halting and bound
sentences, verification of finite halting computations and of the
computed Busy Beaver bounds through five states, and derivation of
non-halting sentences from a proved bound plus a finite non-halting
run. No concrete ZFC syntax or checker is supplied, and no instance
of this bundle for ZFC is constructed; the intended reading is ZFC with
its standard proof checker. Formalizing that checker is the gap behind
the catalogue's numerical state counts for consistency-search machines,
which are therefore not asserted for arbitrary presentations: the
counts in the literature are properties of specific checker
implementations, not of every theory satisfying this bundle. -/
structure ZFCPresentation where
  /-- The presented theory. -/
  theory : FormalTheory
  /-- The proof checker: `check p s` says `p` proves sentence `s`. -/
  check : ℕ → ℕ → Bool
  /-- Provability is existence of a checked proof. -/
  provable_iff : ∀ s : ℕ,
    theory.Provable s ↔ ∃ p : ℕ, check p s = true
  /-- Soundness for halting sentences. -/
  soundForHalting : SoundForHalting theory
  /-- Finite halting computations are verifiable. -/
  verifies_halting : ∀ {n : ℕ} (M : Machine n) (t : ℕ),
    HaltsWithin M t → theory.Provable (haltsSentence M)
  /-- The computed Busy Beaver bounds through five states are
  provable. -/
  verifies_bounds : ∀ n ≤ 5,
    theory.Provable (boundSentence n (busyBeaverSteps n))
  /-- A proved runtime bound applies to the machines it quantifies
  over. -/
  sound_bounds : ∀ (n B : ℕ),
    theory.Provable (boundSentence n B) →
      ∀ M : Machine n, Halts M → HaltsWithin M B
  /-- A proved runtime bound together with a finite non-halting run
  yields a proof of the non-halting sentence. This packages finite
  run verification and modus ponens inside the theory. -/
  notHalts_of_bound : ∀ {n : ℕ} (M : Machine n) (B : ℕ),
    theory.Provable (boundSentence n B) → ¬ HaltsWithin M B →
      theory.Provable (notHaltsSentence M)

/-- A ZFC-like presentation decides halting for machines with at most
five states: run each machine for the proved Busy Beaver bound; if it
has halted, the computation verifies, and if it has not, the bound
derives its non-halting sentence. -/
theorem ZFCPresentation.decidesHalting_le_five (Z : ZFCPresentation) :
    ∀ n ≤ 5, DecidesHalting Z.theory n := by
  intro n hn M
  by_cases h : HaltsWithin M (busyBeaverSteps n)
  · exact Or.inl (Z.verifies_halting M _ h)
  · exact Or.inr
      (Z.notHalts_of_bound M _ (Z.verifies_bounds n hn) h)

end Cslib.BusyBeaver
