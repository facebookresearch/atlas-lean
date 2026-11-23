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

/-- **Head movement.** A head movement is one of exactly two directions: left or right. -/
inductive Move where
  | left
  | right
deriving DecidableEq

instance : Fintype Move where
  elems := {Move.left, Move.right}
  complete := by
    intro m
    cases m <;> simp

/-- **Head displacement.** The displacement of a head movement is $-1$ for a move to the left
and $1$ for a move to the right. -/
def Move.shift : Move → ℤ
  | .left => -1
  | .right => 1

/-- **Busy Beaver machine.** A Busy Beaver machine with $n$ working states is a transition table
that assigns to each of the $n$ working states and each read symbol in $\{0, 1\}$ a symbol in
$\{0, 1\}$ to write, a head movement (left or right), and a next state, which is either one of
the $n$ working states or the halt state.

The write and move of a halting transition are still performed, and the halting step counts
toward the runtime. -/
abbrev Machine (n : ℕ) :=
  Fin n → Fin 2 → Fin 2 × Move × Option (Fin n)

/-- **Busy Beaver machine configuration.** A configuration of an $n$-state machine consists of a
current state, which is either one of the $n$ working states or the halt state, an integer head
position, and a tape assigning a symbol in $\{0, 1\}$ to every integer cell. -/
structure Config (n : ℕ) where
  state : Option (Fin n)
  head : ℤ
  tape : ℤ → Fin 2

/-- **One step of a Busy Beaver machine.** Let $M$ be a machine with $n$ working states and let
$c$ be a configuration with head position $h$. If $c$ is halted, the step leaves $c$ unchanged.
Otherwise let $q$ be the current state, let $a$ be the symbol in cell $h$, and let
$M(q, a) = (b, d, q')$. The step writes $b$ in cell $h$, leaving every other cell unchanged, moves
the head to $h - 1$ if $d$ is left and to $h + 1$ if $d$ is right, and passes to the state $q'$,
which may be the halt state. -/
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

/-- **Initial state.** For a machine with $n$ working states, the initial state is state $0$ when
$n > 0$, and the halt state when $n = 0$. -/
def initialState (n : ℕ) : Option (Fin n) :=
  if h : 0 < n then some ⟨0, h⟩ else none

/-- **Initial configuration of a Busy Beaver machine.** The initial configuration of a machine
with $n$ working states is in the initial state (state $0$, or the halt state when $n = 0$), with
the head at position $0$ and every tape cell blank, that is, holding the symbol $0$. -/
def initial (n : ℕ) : Config n :=
  ⟨initialState n, 0, fun _ => 0⟩

/-- **Configuration after $t$ steps.** For a Busy Beaver machine $M$ and $t \in \mathbb{N}$,
the configuration of $M$ after $t$ steps is the result of applying the one-step map of $M$
$t$ times to the initial configuration on the blank tape. -/
def run {n : ℕ} (M : Machine n) (t : ℕ) : Config n :=
  (step M)^[t] (initial n)

theorem run_zero {n : ℕ} (M : Machine n) : run M 0 = initial n := rfl

theorem run_succ {n : ℕ} (M : Machine n) (t : ℕ) :
    run M (t + 1) = step M (run M t) :=
  Function.iterate_succ_apply' (step M) t (initial n)

/-- **Halting within $t$ steps.** A Busy Beaver machine $M$ with $n$ working states halts within
$t$ steps when the configuration reached after running $M$ for $t$ steps from the initial
blank-tape configuration is in the halt state. -/
def HaltsWithin {n : ℕ} (M : Machine n) (t : ℕ) : Prop :=
  (run M t).state = none

/-- **Halting on the blank tape.** A Busy Beaver machine $M$ halts when there is a number of steps
$t$ such that $M$ halts within $t$ steps, that is, when $M$ started from the initial
blank-tape configuration eventually reaches the halt state. -/
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

/-- **Halting time.** For an $n$-state machine $M$ that halts on the blank tape, its
halting time is the least $t$ such that $M$, started on the blank tape, is in the halt
state after $t$ steps. -/
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

/-- **Head displacement bound.** For every $n$-state Busy Beaver machine $M$ and every
$t \in \mathbb{N}$, if $h \in \mathbb{Z}$ is the head position after $M$ has run for $t$ steps
from the initial configuration on the blank tape, then $|h| \le t$. -/
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

/-- **Cells far from the origin stay blank.** Let $M$ be a machine with $n$ working states,
started in cell $0$ on the blank tape. For every $t \in \mathbb{N}$ and every cell
$i \in \mathbb{Z}$ with $|i| > t$, the symbol in cell $i$ after $t$ steps is $0$. -/
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

/-- **Number of ones after $t$ steps.** For a Busy Beaver machine $M$ and $t \in \mathbb{N}$,
the number of ones of $M$ after $t$ steps is the number of cells $i \in \mathbb{Z}$ with
$-t \le i \le t$ that hold the symbol $1$ in the configuration of $M$ after $t$ steps, started
on the blank tape.

Every one on the tape after $t$ steps lies in this window, since the head moves at most one
cell per step. -/
def onesAt {n : ℕ} (M : Machine n) (t : ℕ) : ℕ :=
  ((Finset.Icc (-(t : ℤ)) t).filter fun i => (run M t).tape i = 1).card

theorem onesAt_le {n : ℕ} (M : Machine n) (t : ℕ) :
    onesAt M t ≤ 2 * t + 1 := by
  refine (Finset.card_filter_le _ _).trans_eq ?_
  rw [Int.card_Icc]
  omega

/-- **After $t$ steps, every one lies within distance $t$ of the origin.** For every Busy Beaver
machine $M$, every $t \in \mathbb{N}$ and every cell $i \in \mathbb{Z}$, if cell $i$ holds the
symbol $1$ after $M$ runs for $t$ steps from the initial blank-tape configuration, then
$-t \le i \le t$. -/
theorem mem_window_of_tape_eq_one {n : ℕ} (M : Machine n) (t : ℕ) {i : ℤ}
    (hi : (run M t).tape i = 1) : i ∈ Finset.Icc (-(t : ℤ)) t := by
  rw [Finset.mem_Icc, ← abs_le]
  by_contra hcon
  have habs : (t : ℤ) < |i| := lt_of_not_ge hcon
  have h0 : (run M t).tape i = 0 := tape_eq_zero_of_abs_gt M t habs
  rw [hi] at h0
  exact one_ne_zero h0

/-- **The number of ones grows by at most one per step.** For every Busy Beaver machine $M$
and every $t \in \mathbb{N}$, the number of ones of $M$ after $t + 1$ steps is at most the
number of ones of $M$ after $t$ steps plus $1$. -/
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

/-- **At most $t$ ones after $t$ steps.** For every Busy Beaver machine $M$ and every
$t \in \mathbb{N}$, the number of ones of $M$ after $t$ steps is at most $t$. -/
theorem onesAt_le_steps {n : ℕ} (M : Machine n) (t : ℕ) :
    onesAt M t ≤ t := by
  induction t with
  | zero => rw [onesAt_zero]
  | succ t ih =>
    exact (onesAt_succ_le M t).trans (Nat.add_le_add_right ih 1)

/-- **Runtime of a Busy Beaver machine.** For a machine $M$ with $n$ working states, the runtime
of $M$ is its halting time on the blank tape if $M$ halts, and $0$ if $M$ does not halt. This is
the quantity whose maximum over all $n$-state machines is the shift function $S(n)$. -/
noncomputable def stepsOf {n : ℕ} (M : Machine n) : ℕ :=
  @dite ℕ (Halts M) (Classical.propDecidable _) (fun h => haltTime M h)
    (fun _ => 0)

/-- **Score of a machine.** For a Busy Beaver machine $M$: if $M$ halts on the blank tape,
with halting time $T$, its score is the number of ones of $M$ after $T$ steps; if $M$ does not
halt, its score is $0$. -/
noncomputable def scoreOf {n : ℕ} (M : Machine n) : ℕ :=
  @dite ℕ (Halts M) (Classical.propDecidable _)
    (fun h => onesAt M (haltTime M h)) (fun _ => 0)

/-- **Busy Beaver shift function.** For $n \in \mathbb{N}$, Rado's shift function $S(n)$ is the
largest halting time of an $n$-state two-symbol machine that halts when started on the blank
tape; machines that do not halt contribute $0$. -/
noncomputable def busyBeaverSteps (n : ℕ) : ℕ :=
  (Finset.univ : Finset (Machine n)).sup stepsOf

/-- **Busy Beaver score function.** For $n \in \mathbb{N}$, Rado's score function $\Sigma(n)$ is
the largest number of ones left on the tape, at its halting time, by an $n$-state two-symbol
machine that halts when started on the blank tape; machines that do not halt contribute $0$. -/
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

/-- **The Busy Beaver score is at most the shift.** For every $n \in \mathbb{N}$, Rado's score
function $\Sigma$ and Rado's shift function $S$ satisfy $\Sigma(n) \le S(n)$: the largest number
of ones left on the tape by a halting $n$-state two-symbol machine started on the blank tape is
at most the largest halting time of such a machine. -/
theorem busyBeaverOnes_le_steps (n : ℕ) :
    busyBeaverOnes n ≤ busyBeaverSteps n := by
  rw [busyBeaverOnes, busyBeaverSteps]
  apply Finset.sup_le
  intro M _hM
  exact (scoreOf_le_stepsOf M).trans (Finset.le_sup (Finset.mem_univ M))

/-- **The shift function is attained.** Let $S(n)$ be Rado's shift function, the largest
runtime of an $n$-state machine, where the runtime of a machine is its halting time on the
blank tape if it halts and $0$ otherwise. For every $n$, some $n$-state machine $M$ has
runtime equal to $S(n)$. Thus $S(n)$ is the halting time of a halting $n$-state machine,
or $S(n) = 0$. -/
theorem exists_stepsOf_eq (n : ℕ) :
    ∃ M : Machine n, stepsOf M = busyBeaverSteps n := by
  obtain ⟨M, _hM, hM⟩ := Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Machine n)))
    (f := stepsOf) ⟨fun _ _ => (0, Move.left, none), Finset.mem_univ _⟩
  refine ⟨M, ?_⟩
  rw [busyBeaverSteps]
  exact hM.symm

/-- **The score function is attained.** Let $\Sigma(n)$ be the busy beaver score function,
the largest score of an $n$-state machine, where the score of a machine is the number of
ones on its final tape if it halts on the blank tape and $0$ otherwise. For every $n$, some
$n$-state machine $M$ has score equal to $\Sigma(n)$. Thus $\Sigma(n)$ is the number of
ones left by a halting $n$-state machine, or $\Sigma(n) = 0$. -/
theorem exists_scoreOf_eq (n : ℕ) :
    ∃ M : Machine n, scoreOf M = busyBeaverOnes n := by
  obtain ⟨M, _hM, hM⟩ := Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Machine n)))
    (f := scoreOf) ⟨fun _ _ => (0, Move.left, none), Finset.mem_univ _⟩
  refine ⟨M, ?_⟩
  rw [busyBeaverOnes]
  exact hM.symm

/-- **Embedding a machine into one more state.** An $n$-state machine $M$ is embedded
into $n + 1$ states as follows. In a working state $q < n$ reading a symbol $s$, the new
machine writes the symbol, makes the move and enters the next state that $M$ prescribes
in state $q$ on $s$, halting when $M$ halts. In the new state $n$ it writes $0$, moves
left and halts, whatever it reads.

No transition enters state $n$. So for $n \ge 1$, where the machine starts in state
$0 < n$, the new state is never reached; for $n = 0$ the new state is the start state. -/
def embedMachine {n : ℕ} (M : Machine n) : Machine (n + 1) :=
  fun q s =>
    if h : q.val < n then
      let a := M ⟨q.val, h⟩ s
      (a.1, a.2.1, a.2.2.map Fin.castSucc)
    else (0, Move.left, none)

/-- **Embedding a configuration into one more state.** For a configuration $c$ of an
$n$-state machine, its embedding is the configuration for $n + 1$ states with the same
head position and the same tape as $c$. Its state is the state of $c$, where a working
state $q \in \{0, \dots, n - 1\}$ stays $q$ and the halt state stays the halt state. -/
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

/-- **A one-state machine that stays in its state on a blank never halts.** Let $M$ be a Busy Beaver
machine with a single working state $0$. If the transition of $M$ from state $0$ on reading the
blank symbol $0$ has next state $0$, then $M$ does not halt.

Such a machine marches in one direction forever: at every step the head is on a previously
unvisited blank cell. -/
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

/-- **Machine code.** The code of a machine $M$ with $n$ working states is the natural number that
encodes the pair $(n, i)$ under a fixed pairing bijection
$\mathbb{N} \times \mathbb{N} \to \mathbb{N}$, where $i$ is the index of $M$ in a fixed enumeration
of the finitely many machines with $n$ working states. -/
noncomputable def machineCode {n : ℕ} (M : Machine n) : ℕ :=
  Nat.pair n (Fintype.equivFinOfCardEq (α := Machine n) rfl M).val

/-- **Sentence codes.** The sentence code with tag $a$ and payload $p$ is the natural number
$4p + a$. The tags in use are $0$ (the coded machine halts), $1$ (the coded machine does not
halt), $2$ (the false sentence), and $3$ with payload the pairing code of $n$ and $B$ (every
halting $n$-state machine halts within $B$ steps).

Sentences are natural numbers rather than propositions, so provability does not collapse under
propositional extensionality. -/
def sentenceCode (tag payload : ℕ) : ℕ :=
  4 * payload + tag

/-- **Halting sentence of a machine.** For an $n$-state machine $M$, the halting sentence
of $M$ is the sentence code with tag $0$ and payload the code of $M$. It stands for
"$M$ halts on the blank tape"; this meaning comes from soundness hypotheses on a
theory, not from the code itself. -/
noncomputable def haltsSentence {n : ℕ} (M : Machine n) : ℕ :=
  sentenceCode 0 (machineCode M)

/-- **Non-halting sentence of a machine.** For a Busy Beaver machine $M$, the non-halting
sentence of $M$ is the sentence code with tag $1$ whose payload is the code of $M$; it stands
for "$M$ does not halt on the blank tape". -/
noncomputable def notHaltsSentence {n : ℕ} (M : Machine n) : ℕ :=
  sentenceCode 1 (machineCode M)

/-- **The false sentence.** The false sentence is the sentence code with tag $2$ and
payload $0$, that is, the natural number $2$. -/
def falseSentence : ℕ :=
  sentenceCode 2 0

/-- **Runtime-bound sentence.** For natural numbers $n$ and $B$, the runtime-bound sentence is
the sentence code with tag $3$ and payload $\langle n, B \rangle$, the pairing of $n$ and $B$;
as a number it equals $4 \langle n, B \rangle + 3$.

Its intended reading is "every halting $n$-state machine halts within $B$ steps"; this meaning
is assigned only through separate soundness hypotheses. -/
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

/-- **Formal theory.** A formal theory is given by a provability predicate on sentence
codes, which are natural numbers: for each natural number it specifies whether that
sentence code is provable in the theory.

The theory is an abstract parameter, with ZFC as the intended instance. No meaning is
attached to sentence codes here; the halting, non-halting, false and runtime-bound
sentences receive their meaning through separate soundness hypotheses. -/
structure FormalTheory where
  /-- Provability of a sentence code in the theory. -/
  Provable : ℕ → Prop

/-- **Consistent formal theory.** A formal theory $T$ is consistent when $T$ does not prove the
false sentence. -/
def Consistent (T : FormalTheory) : Prop :=
  ¬ T.Provable falseSentence

/-- **Soundness for halting sentences.** A formal theory $T$ is sound for halting sentences
when, for every $n$ and every Busy Beaver machine $M$ with $n$ states, if $T$ proves the
halting sentence of $M$ then $M$ halts on the blank tape, and if $T$ proves the non-halting
sentence of $M$ then $M$ does not halt on the blank tape. -/
def SoundForHalting (T : FormalTheory) : Prop :=
  (∀ {n : ℕ} (M : Machine n), T.Provable (haltsSentence M) → Halts M) ∧
  (∀ {n : ℕ} (M : Machine n),
    T.Provable (notHaltsSentence M) → ¬ Halts M)

/-- **Theories deciding halting at a state count.** A formal theory $T$ decides halting for
$n$-state machines when, for every $n$-state machine $M$, $T$ proves the halting sentence of $M$
or $T$ proves the non-halting sentence of $M$. -/
def DecidesHalting (T : FormalTheory) (n : ℕ) : Prop :=
  ∀ M : Machine n,
    T.Provable (haltsSentence M) ∨ T.Provable (notHaltsSentence M)

/-- **First undecidable number of states.** For a formal theory $T$, the first
undecidable number of states is the least $n$ such that $T$ does not decide halting for
all $n$-state machines, that is, there is an $n$-state machine $M$ for which $T$ proves
neither the halting sentence nor the non-halting sentence of $M$. It is $0$ when there
is no such $n$.

For ZFC this is catalogue constant 14a; the junk value $0$ covers a theory that decides
halting at every number of states. -/
noncomputable def firstUndecidable (T : FormalTheory) : ℕ :=
  sInf {n | ¬ DecidesHalting T n}

theorem firstUndecidable_le_of_not_decides {T : FormalTheory} {n : ℕ}
    (h : ¬ DecidesHalting T n) : firstUndecidable T ≤ n :=
  Nat.sInf_le h

theorem not_decides_firstUndecidable {T : FormalTheory}
    (h : ∃ n, ¬ DecidesHalting T n) :
    ¬ DecidesHalting T (firstUndecidable T) :=
  Nat.sInf_mem h

/-- **Decidability through five states and the first undecidable size.** If a formal theory
$T$ decides halting for $n$-state machines for every $n \le 5$, and fails to decide halting for
$n$-state machines for some $n$, then the first undecidable size of $T$ is at least $6$.

This is the shape of the catalogue lower bound from the determination of the five-state Busy
Beaver value. -/
theorem six_le_firstUndecidable_of_decides_le_five {T : FormalTheory}
    (h5 : ∀ n ≤ 5, DecidesHalting T n)
    (hex : ∃ n, ¬ DecidesHalting T n) :
    6 ≤ firstUndecidable T := by
  have hmem := not_decides_firstUndecidable hex
  by_contra hcon
  push Not at hcon
  exact hmem (h5 (firstUndecidable T) (by omega))

/-- **A consistency-search machine blocks decidability at its size.** Let $T$ be a formal theory
and $M$ a Busy Beaver machine with $n$ working states. Suppose that $M$ halts if and only if $T$
proves the false sentence, that $M$ halts whenever $T$ proves the halting sentence of $M$, that
$T$ is consistent, and that $T$ does not prove the non-halting sentence of $M$. Then $T$ does not
decide halting for all machines with $n$ working states.

The last hypothesis is the Gödel second-incompleteness content when $T$ is ZFC. -/
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

/-- **Decidability of halting passes to fewer states.** Let $T$ be a formal theory such that, for
every $m$ and every Busy Beaver machine $M$ with $m$ working states, if $T$ proves the halting
sentence of the embedding of $M$ into $m + 1$ states then $T$ proves the halting sentence of $M$,
and if $T$ proves the non-halting sentence of the embedding of $M$ into $m + 1$ states then $T$
proves the non-halting sentence of $M$. Then for every $n$, if $T$ decides halting for machines
with $n + 1$ working states, it decides halting for machines with $n$ working states.

The transport hypotheses are where a real theory would rewrite a proof about the embedded machine
into a proof about the original machine; they are stated explicitly because provability of one
sentence code does not formally imply provability of another. -/
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

/-- **Proof-checker presentation of a ZFC-like theory.** A ZFC-like presentation consists of a
formal theory $T$, given by a provability predicate on sentence codes in $\mathbb{N}$, together
with a Boolean proof checker $\mathrm{check}(p, s)$ on pairs of natural numbers, such that the
following hold. A sentence code $s$ is provable in $T$ if and only if $\mathrm{check}(p, s)$ is true
for some $p \in \mathbb{N}$. $T$ is sound for halting: for every machine $M$, if $T$ proves the
halting sentence of $M$ then $M$ halts on the blank tape, and if $T$ proves the non-halting
sentence of $M$ then $M$ does not halt. For every machine $M$, if $M$ has halted within $t$ steps
for some $t$, then $T$ proves the halting sentence of $M$. Write $S(n)$ for the Busy Beaver shift
function, the largest halting time of a halting machine with $n$ working states, and call the
bound sentence for $n$ and $B$ the sentence code saying that every halting machine with $n$
working states halts within $B$ steps. For every $n \le 5$, $T$ proves the bound sentence for $n$
and $S(n)$. Whenever $T$ proves the bound sentence for $n$ and $B$, every halting machine with $n$
working states halts within $B$ steps. Whenever $T$ proves the bound sentence for $n$ and $B$ and a
machine $M$ with $n$ working states has not halted within $B$ steps, $T$ proves the non-halting
sentence of $M$.

No concrete syntax or proof checker for ZFC is given, and no presentation of ZFC is constructed;
the intended instance is ZFC with its standard proof checker. The state counts for
consistency-search machines in the literature depend on specific checker implementations and are
not asserted for arbitrary presentations. -/
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

/-- **ZFC-like theories decide halting through five states.** For every ZFC-like presentation
$Z$ and every $n \le 5$, the theory presented by $Z$ decides halting for $n$-state machines: for
every $n$-state machine it proves the machine's halting sentence or its non-halting sentence.

Proof idea: let $S$ be Rado's shift function; $Z$ proves the runtime bound $S(n)$ for
halting $n$-state machines. Run each machine for $S(n)$ steps; if it has halted, the
computation verifies, and if it has not, the bound derives its non-halting sentence. -/
theorem ZFCPresentation.decidesHalting_le_five (Z : ZFCPresentation) :
    ∀ n ≤ 5, DecidesHalting Z.theory n := by
  intro n hn M
  by_cases h : HaltsWithin M (busyBeaverSteps n)
  · exact Or.inl (Z.verifies_halting M _ h)
  · exact Or.inr
      (Z.notHalts_of_bound M _ (Z.verifies_bounds n hn) h)

end Cslib.BusyBeaver
