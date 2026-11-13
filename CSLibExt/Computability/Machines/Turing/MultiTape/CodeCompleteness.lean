/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.Code
public import CSLibExt.Computability.Machines.Turing.MultiTape.Relabel
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-!
# Codes are complete for finite-state binary machines

Codes (`Code k`, MT1) and binary multi-tape machines with finitely many states describe the same
computations:

- **Codes give finite-state machines.** The machine of a code, `Code.toTM c`, has states in `ℕ`,
  but only the finitely many states `c.states` occur (`Code.state_runFrom_mem_states`). Restricting
  it to `Fin c.stateBound` gives `Code.toFinTM c`, a machine of CSLib's model with finitely many
  states, which `c.toTM` simulates up to the relabelling `Fin.val`
  (`Code.isRelabelling_toFinTM`). So every resource bound met by a code is met by a machine of the
  kind `MultiTapeTM.ComputableInTimeAndSpace` and `MultiTapeTM.DecidableInTimeAndSpace` quantify
  over (`Code.computableInTimeAndSpace`, `Code.decidableInTimeAndSpace`).
- **Every finite-state machine has a code.** For a machine `tm : MultiTapeTM k Bool State` with
  finitely many states and an injective numbering `e` of its states sending the initial state to
  `0`, the code `Code.ofTM tm e` tabulates the transition function of `tm`, and its machine
  simulates `tm` up to the relabelling `e` (`Code.isRelabelling_ofTM`); such a numbering always
  exists (`Code.exists_code_isRelabelling`).

Relabelling preserves outputs, time and space (`IsRelabelling.computes_iff` and its siblings), so
the classes of CSLib's model, and `DTIME`/`DSPACE`, can be stated equivalently over codes
(`computableInTimeAndSpace_iff_exists_code`, `decidableInTimeAndSpace_iff_exists_code`,
`mem_DTIME_iff_exists_code`, `mem_DSPACE_iff_exists_code`). This is what a diagonal argument
over codes needs; the universal machine that runs codes is future work.

## Main definitions

- `Cslib.Turing.MultiTapeTM.Code.stateBound`, `Code.toFinTM`: the finite-state machine of a code.
- `Cslib.Turing.MultiTapeTM.encodeMove`, `encodeAction`: actions as coded actions.
- `Cslib.Turing.MultiTapeTM.Code.ofTM`: the code of a finite-state binary machine.

## Main results

- `Code.isRelabelling_toFinTM`: a code's machine simulates its finite-state machine.
- `Code.isRelabelling_ofTM`, `Code.exists_code_isRelabelling`: every finite-state binary machine is
  simulated by the machine of a code, up to an injective state relabelling.
- `Code.computableInTimeAndSpace`, `Code.decidableInTimeAndSpace`: codes land in CSLib's classes.
- `computableInTimeAndSpace_iff_exists_code`, `decidableInTimeAndSpace_iff_exists_code`,
  `mem_DTIME_iff_exists_code`, `mem_DSPACE_iff_exists_code`: the classes over codes.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Turing.MultiTapeTM

open _root_.Turing

variable {k : ℕ}

/-! ### Coding actions -/

/-- **Coding head moves.** A head move is coded as a natural number: left is $0$, stay is $1$
and right is $2$. Decoding a move code recovers the move. -/
def encodeMove : SignType → ℕ
  | .neg => 0
  | .zero => 1
  | .pos => 2

@[simp]
theorem decodeMove_encodeMove (m : SignType) : decodeMove (encodeMove m) = m := by
  cases m <;> rfl

/-- **Coding an action.** Let $e : Q \to \mathbb{N}$ number the states $Q$ of a binary multi-tape
machine with $k$ work tapes. The coded action of an action $a$ of the machine under $e$ records as
its input-head move the code of the input-head move of $a$ (left $0$, stay $1$, right $2$); for
each work tape it records what $a$ writes there and the code of the head move of $a$ there; it
records the output bit of $a$, if any; and its next state is $e(q)$ when $a$ enters the state $q$,
and it halts when $a$ halts. -/
def encodeAction {State : Type*} (e : State → ℕ) (a : Action k Bool State) : CodeAction k where
  inputMove := encodeMove a.inputTape
  work i := ((a.workTapes i).1, encodeMove (a.workTapes i).2)
  out := a.output
  next := a.state.map e

/-- **Decoding the coding of an action.** Let $Q$ be a type, $e : Q \to \mathbb{N}$ a map and $a$
an action of a binary machine with $k$ work tapes and states in $Q$. The action that the coded
action of $a$, with its successor state numbered by $e$, stands for is $a$ with its successor
state relabelled by $e$. -/
theorem toAction_encodeAction {State : Type*} (e : State → ℕ) (a : Action k Bool State) :
    (encodeAction e a).toAction = relabelAction e a := by
  cases a
  simp [encodeAction, CodeAction.toAction, relabelAction]

namespace Code

/-! ### The finite-state machine of a code -/

/-- **State bound of a code.** The states of a code $c$ are the initial state $0$ and every
successor state named in its table. The state bound of $c$ is one more than the largest of them;
it is a strict upper bound on the states of $c$. -/
def stateBound (c : Code k) : ℕ := c.states.sup id + 1

theorem lt_stateBound (c : Code k) {q : ℕ} (h : q ∈ c.states) : q < c.stateBound :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) h)

theorem zero_lt_stateBound (c : Code k) : 0 < c.stateBound := Nat.succ_pos _

/-- **A number as a bounded state.** For natural numbers $N$ and $q$, this is $q$ as an element
of $\{0, \dots, N - 1\}$ if $q < N$, and no value otherwise. -/
def finState (N q : ℕ) : Option (Fin N) := if h : q < N then some ⟨q, h⟩ else none

/-- **Transition function of a code on bounded states.** Let $c$ be a code with $k$ work tapes
and let $N$ be its state bound. For a state $q < N$, a symbol $a$ under the input head and
symbols $w$ under the $k$ work heads (each a bit or blank), this is the action of $c$ at
$(q, a, w)$ with the same input-head move, work-tape writes and moves, and output, and with its
successor state read as a state below $N$; a successor state that is not below $N$ is replaced
by halting. -/
def finTr (c : Code k) (q : Fin c.stateBound) (a : Option Bool) (w : Fin k → Option Bool) :
    Action k Bool (Fin c.stateBound) :=
  ⟨(c.tr q a w).inputTape, (c.tr q a w).workTapes, (c.tr q a w).output,
    (c.tr q a w).state.bind (finState c.stateBound)⟩

/-- **The finite-state machine of a code.** For a code $c$ with $k$ work tapes and state bound
$N$, this is the binary machine with $k$ work tapes and states $0, 1, \dots, N - 1$ that starts
in state $0$ and, in a state $q < N$ reading $a$ under the input head and $w$ under the work
heads, takes the action of $c$ at $(q, a, w)$, with a successor state not below $N$ replaced by
halting. Since every state the machine of $c$ can enter is below $N$, it is the machine of $c$
with its states restricted to those below $N$. -/
noncomputable def toFinTM (c : Code k) : MultiTapeTM k Bool (Fin c.stateBound) :=
  MultiTapeTM.ofTr ⟨0, c.zero_lt_stateBound⟩ c.finTr

/-- **A code's machine simulates its finite-state machine.** For every code $c$, the machine of
$c$ simulates the finite-state machine of $c$ up to the relabelling that sends each state
$q < N$, where $N$ is the state bound of $c$, to the natural number $q$. -/
theorem isRelabelling_toFinTM (c : Code k) : IsRelabelling Fin.val c.toFinTM c.toTM where
  q₀ := rfl
  tr q a w := by
    rw [toTM, MultiTapeTM.tr_ofTr, toFinTM, MultiTapeTM.tr_ofTr]
    have hs : ((c.tr q a w).state.bind (finState c.stateBound)).map Fin.val =
        (c.tr q a w).state := by
      cases hq : (c.tr q a w).state with
      | none => rfl
      | some q' =>
        have hq' : q' ∈ c.states := c.next_act_mem_states hq
        simp [finState, c.lt_stateBound hq']
    simp only [finTr, relabelAction, hs]

/-- **Computation by a code is finite-state computation.** Let $c$ be a code with $k$ work tapes,
let $g : \alpha \to \beta$ be a function, let inputs in $\alpha$ and outputs in $\beta$ be encoded
by injective maps into binary words, and let $t, s : \alpha \to \mathbb{N}$. If the machine of $c$,
started on the encoding of any input $x$, halts with the encoding of $g(x)$ as output, halts
within $t(x)$ steps, and visits at most $s(x)$ work-tape cells, then some binary multi-tape
machine with finitely many states computes $g$ within the same bounds in the same sense. -/
theorem computableInTimeAndSpace {α β : Type*} {g : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {t s : α → ℕ} (c : Code k)
    (h : c.toTM.ComputesFunInTimeAndSpace encIn encOut g t s) :
    MultiTapeTM.ComputableInTimeAndSpace g encIn encOut t s :=
  ⟨k, Fin c.stateBound, inferInstance, c.toFinTM,
    c.isRelabelling_toFinTM.computesFunInTimeAndSpace_iff.mp h⟩

/-- **Deciding by a code is finite-state decidability.** Let $c$ be a code with $k$ work tapes,
let $L$ be a set of binary words, and let $t$ and $s$ map binary words to natural numbers. If
the machine of $c$ decides $L$, that is, started on any binary word $w$ it halts with the one-bit
output $\mathrm{true}$ if $w \in L$ and $\mathrm{false}$ otherwise, and if on every binary word
$w$ it halts within $t(w)$ steps and visits at most $s(w)$ work-tape cells, then some binary
multi-tape machine with finitely many states decides $L$ within the same bounds. -/
theorem decidableInTimeAndSpace {L : Set (List Bool)} {t s : List Bool → ℕ} (c : Code k)
    (hd : Decides c.toTM L) (ht : ∀ w, c.toTM.RunsInTime w (t w))
    (hs : ∀ w, c.toTM.RunsInSpace w (s w)) :
    MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _) t s :=
  decidableInTimeAndSpace_iff.mpr ⟨k, Fin c.stateBound, inferInstance, c.toFinTM,
    c.isRelabelling_toFinTM.decides_iff.mp hd,
    fun w ↦ c.isRelabelling_toFinTM.runsInTime_iff.mp (ht w),
    fun w ↦ c.isRelabelling_toFinTM.runsInSpace_iff.mp (hs w)⟩

/-! ### The code of a finite-state machine -/

private theorem lookup_map_of_injective {ι κ β : Type*} [DecidableEq κ] {g : ι → κ}
    (hg : Function.Injective g) (v : ι → β) :
    ∀ {l : List ι} {x : ι}, x ∈ l →
      (l.map fun y ↦ (g y, v y)).lookup (g x) = some (v x)
  | [], _, hx => absurd hx List.not_mem_nil
  | y :: l, x, hx => by
    by_cases hxy : x = y
    · subst hxy
      simp
    · have hne : (g x == g y) = false := by simpa using hg.ne hxy
      rw [List.map_cons, List.lookup, hne]
      exact lookup_map_of_injective hg v (List.mem_of_ne_of_mem hxy hx)

/-- **The code of a finite-state binary machine.** Let $M$ be a machine over the binary alphabet
with $k$ work tapes and a finite set of states $Q$, and let $e : Q \to \mathbb{N}$. The code of
$M$ with states numbered by $e$ has one table entry for each state $q \in Q$, symbol $a$ under
the input head and symbols $w$ under the $k$ work heads (each a bit or blank): its key is
$(e(q), a, w)$ and its value is the coded action of $M$ in state $q$ reading $a$ and $w$, with
the successor state numbered by $e$. The entries are listed in an unspecified order.

When $e$ is injective and sends the initial state of $M$ to $0$, the machine of this code
simulates $M$ up to the relabelling $e$. -/
noncomputable def ofTM {State : Type*} [Fintype State] (tm : MultiTapeTM k Bool State)
    (e : State → ℕ) : Code k :=
  ⟨(Finset.univ : Finset (State × Option Bool × (Fin k → Option Bool))).toList.map
    fun x ↦ ((e x.1, x.2.1, x.2.2), encodeAction e (tm.tr x.1 x.2.1 x.2.2))⟩

/-- **The code of a machine takes its coded actions.** Let $M$ be a binary multi-tape machine
with $k$ work tapes and a finite set of states $Q$, and let $e : Q \to \mathbb{N}$ be injective.
For every state $q \in Q$, every symbol $a$ under the input head and every tuple $w$ of symbols
under the $k$ work heads (each a bit or blank), the coded action of the code of $M$ under $e$ at
state $e(q)$ and symbols $a$, $w$ is the coding, with successor states numbered by $e$, of the
action of $M$ in state $q$ on $a$ and $w$. -/
theorem act_ofTM {State : Type*} [Fintype State] (tm : MultiTapeTM k Bool State) {e : State → ℕ}
    (he : Function.Injective e) (q : State) (a : Option Bool) (w : Fin k → Option Bool) :
    (ofTM tm e).act (e q) a w = encodeAction e (tm.tr q a w) := by
  have hg : Function.Injective fun x : State × Option Bool × (Fin k → Option Bool) ↦
      ((e x.1, x.2.1, x.2.2) : CodeKey k) := by
    rintro ⟨q₁, a₁, w₁⟩ ⟨q₂, a₂, w₂⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h₁, rfl, rfl⟩ := h
    rw [he h₁]
  unfold act ofTM
  rw [lookup_map_of_injective hg (fun x ↦ encodeAction e (tm.tr x.1 x.2.1 x.2.2))
    (x := (q, a, w)) (Finset.mem_toList.mpr (Finset.mem_univ _))]
  rfl

/-- **The code of a machine simulates it.** Let $M$ be a machine over the binary alphabet with
$k$ work tapes, a finite set of states $Q$ and initial state $q_0$, and let $e : Q \to \mathbb{N}$
be injective with $e(q_0) = 0$. Then the machine of the code of $M$ with states numbered by $e$
simulates $M$ up to the relabelling $e$. -/
theorem isRelabelling_ofTM {State : Type*} [Fintype State] (tm : MultiTapeTM k Bool State)
    {e : State → ℕ} (he : Function.Injective e) (h₀ : e tm.q₀ = 0) :
    IsRelabelling e tm (ofTM tm e).toTM where
  q₀ := h₀.symm
  tr q a w := by
    rw [toTM, MultiTapeTM.tr_ofTr, tr, act_ofTM tm he, toAction_encodeAction]

/-- **Numbering a finite type from a chosen element.** For every finite type $Q$ and every
$q_0 \in Q$ there is an injective map $e : Q \to \mathbb{N}$ with $e(q_0) = 0$. -/
theorem exists_injective_nat_eq_zero {State : Type*} [Finite State] (q₀ : State) :
    ∃ e : State → ℕ, Function.Injective e ∧ e q₀ = 0 := by
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin State
  refine ⟨fun q ↦ Equiv.swap ((σ q₀ : Fin n) : ℕ) 0 (σ q), ?_, Equiv.swap_apply_left _ _⟩
  exact (Equiv.injective _).comp (Fin.val_injective.comp σ.injective)

/-- **Every finite-state machine has a code.** A binary machine with finitely many states is
simulated, up to an injective state relabelling, by the machine of some code. -/
theorem exists_code_isRelabelling {State : Type*} [Finite State]
    (tm : MultiTapeTM k Bool State) :
    ∃ (c : Code k) (e : State → ℕ), Function.Injective e ∧ IsRelabelling e tm c.toTM := by
  have := Fintype.ofFinite State
  obtain ⟨e, he, h₀⟩ := exists_injective_nat_eq_zero tm.q₀
  exact ⟨ofTM tm e, e, he, isRelabelling_ofTM tm he h₀⟩

end Code

/-! ### The classes over codes -/

/-- **Computability over codes.** Let $g : \alpha \to \beta$ be a function, let inputs in $\alpha$
and outputs in $\beta$ be encoded by injective maps into binary words, and let
$t, s : \alpha \to \mathbb{N}$. Say a machine computes $g$ within $t$ and $s$ when, started on the
encoding of any input $x$, it halts with the encoding of $g(x)$ as output, halts within $t(x)$
steps, and visits at most $s(x)$ work-tape cells. Then some binary multi-tape machine with
finitely many states computes $g$ within $t$ and $s$ if and only if, for some number $k$ of work
tapes, the machine of some code with $k$ work tapes computes $g$ within $t$ and $s$. -/
theorem computableInTimeAndSpace_iff_exists_code {α β : Type*} {g : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ} :
    MultiTapeTM.ComputableInTimeAndSpace g encIn encOut t s ↔
      ∃ (k : ℕ) (c : Code k), c.toTM.ComputesFunInTimeAndSpace encIn encOut g t s := by
  constructor
  · rintro ⟨k, State, _, tm, h⟩
    obtain ⟨c, e, -, he⟩ := Code.exists_code_isRelabelling tm
    exact ⟨k, c, he.computesFunInTimeAndSpace_iff.mpr h⟩
  · rintro ⟨k, c, h⟩
    exact c.computableInTimeAndSpace h

/-- **Decidability over codes.** Let $L$ be a set of binary words and let $t$ and $s$ map binary
words to natural numbers. Say a machine decides $L$ within $t$ and $s$ when, started on any
binary word $w$, it halts with the one-bit output $\mathrm{true}$ if $w \in L$ and
$\mathrm{false}$ otherwise, halts within $t(w)$ steps, and visits at most $s(w)$ work-tape cells.
Then some binary multi-tape machine with finitely many states decides $L$ within $t$ and $s$ if
and only if, for some number $k$ of work tapes, the machine of some code with $k$ work tapes
decides $L$ within $t$ and $s$. -/
theorem decidableInTimeAndSpace_iff_exists_code {L : Set (List Bool)} {t s : List Bool → ℕ} :
    MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _) t s ↔
      ∃ (k : ℕ) (c : Code k), Decides c.toTM L ∧ (∀ w, c.toTM.RunsInTime w (t w)) ∧
        ∀ w, c.toTM.RunsInSpace w (s w) := by
  rw [decidableInTimeAndSpace_iff]
  constructor
  · rintro ⟨k, State, _, tm, hd, ht, hs⟩
    obtain ⟨c, e, -, he⟩ := Code.exists_code_isRelabelling tm
    exact ⟨k, c, he.decides_iff.mpr hd, fun w ↦ he.runsInTime_iff.mpr (ht w),
      fun w ↦ he.runsInSpace_iff.mpr (hs w)⟩
  · rintro ⟨k, c, hd, ht, hs⟩
    exact decidableInTimeAndSpace_iff.mp (c.decidableInTimeAndSpace hd ht hs)

/-- **DTIME over codes.** For every $t : \mathbb{N} \to \mathbb{N}$ and every language $L$ of
binary words, $L \in \mathsf{DTIME}(t)$ if and only if there are natural numbers $c_1, c_2, k$
and a code $c$ with $k$ work tapes such that the machine of $c$ decides $L$, on every input $w$
runs in time $c_1 t(|w|) + c_2$, and for some $s : \mathbb{N} \to \mathbb{N}$ on every input
$w$ runs in space $s(|w|)$. -/
theorem mem_DTIME_iff_exists_code {t : ℕ → ℕ} {L : Set (List Bool)} :
    L ∈ DTIME t ↔ ∃ (c₁ c₂ k : ℕ) (c : Code k), Decides c.toTM L ∧
      TimeBoundedBy c.toTM (fun n ↦ c₁ * t n + c₂) ∧ ∃ s, SpaceBoundedBy c.toTM s := by
  constructor
  · rintro ⟨c₁, c₂, s, h⟩
    obtain ⟨k, c, hd, ht, hs⟩ := decidableInTimeAndSpace_iff_exists_code.mp h
    exact ⟨c₁, c₂, k, c, hd, ht, _, hs⟩
  · rintro ⟨c₁, c₂, k, c, hd, ht, s, hs⟩
    exact ⟨c₁, c₂, s, c.decidableInTimeAndSpace hd ht hs⟩

/-- **DSPACE over codes.** For every $s : \mathbb{N} \to \mathbb{N}$ and every language $L$ of
binary words, $L \in \mathsf{DSPACE}(s)$ if and only if there are natural numbers $c_1, c_2, k$
and a code $c$ with $k$ work tapes such that the machine of $c$ decides $L$, on every input $w$
runs in space $c_1 s(|w|) + c_2$, and for some $t : \mathbb{N} \to \mathbb{N}$ on every input
$w$ runs in time $t(|w|)$. -/
theorem mem_DSPACE_iff_exists_code {s : ℕ → ℕ} {L : Set (List Bool)} :
    L ∈ DSPACE s ↔ ∃ (c₁ c₂ k : ℕ) (c : Code k), Decides c.toTM L ∧
      SpaceBoundedBy c.toTM (fun n ↦ c₁ * s n + c₂) ∧ ∃ t, TimeBoundedBy c.toTM t := by
  constructor
  · rintro ⟨c₁, c₂, t, h⟩
    obtain ⟨k, c, hd, ht, hs⟩ := decidableInTimeAndSpace_iff_exists_code.mp h
    exact ⟨c₁, c₂, k, c, hd, hs, _, ht⟩
  · rintro ⟨c₁, c₂, k, c, hd, hs, t, ht⟩
    exact ⟨c₁, c₂, t, c.decidableInTimeAndSpace hd ht hs⟩

end Cslib.Turing.MultiTapeTM
