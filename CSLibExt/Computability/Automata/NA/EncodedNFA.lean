/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Encoded nondeterministic finite automata
-/
module

public import CSLibExt.Computability.Decidability.Regular
public import Mathlib.Computability.EpsilonNFA

/-!
# Encoded nondeterministic finite automata

Mathlib's `εNFA α σ` carries its type of states, so automata are not `Primcodable` and cannot be
inputs of computable functions. `Cslib.Automata.EncodedNFA α` is a concrete encoding of NFAs with
ε-moves, as in Sipser: states are natural numbers, with lists of start and accepting states, a
list of transitions `((s, a), t)` ("on letter `a`, state `s` may move to `t`") and a list of
ε-moves `(s, t)`.

* `EncodedNFA.toεNFA`, `EncodedNFA.language`: the Mathlib ε-NFA an encoding denotes and its
  language.
* `EncodedNFA.exists_language_eq_εNFA`, `EncodedNFA.exists_language_eq`: every ε-NFA, and every
  NFA, over a finite alphabet with finitely many states has an encoding with the same language.
* `EncodedNFA.closure`: the ε-closure of a list of states, by the list-based search
  `EncodedDFA.reachN`; `EncodedNFA.run`: the states reached on a word, one letter at a time with
  closures in between; `EncodedNFA.mem_run_iff` identifies it with Mathlib's `εNFA.eval`.
* `EncodedNFA.acceptsB_iff`, `EncodedNFA.tm2Decidable_mem_language`: **Sipser, Theorem 4.2**
  (A_NFA), membership is decidable by a multi-stack machine.
* `EncodedNFA.mem_reachable_iff`, `EncodedNFA.isEmptyB_iff`,
  `EncodedNFA.tm2Decidable_language_eq_zero`: emptiness (E_NFA), by searching for an accepting
  state reachable from a start state along transitions and ε-moves.
-/

@[expose] public section

namespace Cslib.Automata

open Cslib.Decidability

/-- **Encoded NFA.** An encoded NFA over an alphabet $\alpha$ is a nondeterministic finite
automaton with ε-moves given as data, with natural numbers as states: a list of start states, a
list of accepting states, a list of transitions $((s, a), t)$, meaning that on the letter $a$ the
state $s$ may move to $t$, and a list of ε-moves $(s, t)$, meaning that the state $s$ may move to
$t$ without reading a letter. -/
structure EncodedNFA (α : Type*) where
  /-- The start states. -/
  start : List ℕ
  /-- The accepting states. -/
  accept : List ℕ
  /-- The transitions `((s, a), t)`: on letter `a`, state `s` may move to `t`. -/
  trans : List ((ℕ × α) × ℕ)
  /-- The ε-moves `(s, t)`: state `s` may move to `t` without reading a letter. -/
  eps : List (ℕ × ℕ)

namespace EncodedNFA

variable {α : Type*}

/-! ## Semantics -/

/-- **The ε-NFA of an encoded NFA.** An encoded NFA $N$ over $\alpha$ denotes the ε-NFA over
$\alpha$ with state set $\mathbb{N}$ whose start states are the start states listed in $N$, whose
accepting states are the accepting states listed in $N$, and in which a state $s$ may move to $t$
on a letter $a$ exactly when $((s, a), t)$ is a transition of $N$, and without reading a letter
exactly when $(s, t)$ is an ε-move of $N$. -/
def toεNFA (N : EncodedNFA α) : εNFA α ℕ where
  step s o := match o with
    | some a => {t | ((s, a), t) ∈ N.trans}
    | none => {t | (s, t) ∈ N.eps}
  start := {s | s ∈ N.start}
  accept := {s | s ∈ N.accept}

/-- **Language of an encoded NFA.** The language of an encoded NFA $N$ over an alphabet $\alpha$
is the language accepted by the ε-NFA that $N$ denotes, whose states are the natural numbers:
the words $w$ over $\alpha$ such that some accepting state of $N$ is among the states reached on
$w$ from the start states of $N$, with ε-moves allowed before, between and after the letters. -/
def language (N : EncodedNFA α) : Language α :=
  N.toεNFA.accepts

/-- **States an encoded NFA mentions as start states or targets.** For an encoded NFA $N$, this is
the list of the start states of $N$, followed by the targets $t$ of its transitions $((s, a), t)$,
followed by the targets $t$ of its ε-moves $(s, t)$. -/
def states (N : EncodedNFA α) : List ℕ :=
  N.start ++ N.trans.map Prod.snd ++ N.eps.map Prod.snd

/-- **ε-move relation.** For an encoded NFA $N$, the ε-move relation holds between states $s$ and
$t$ exactly when $(s, t)$ is one of the ε-moves of $N$. -/
def EpsRel (N : EncodedNFA α) (s t : ℕ) : Prop :=
  (s, t) ∈ N.eps

/-- **The ε-closure is reachability along ε-moves.** For an encoded NFA $N$, a set $X$ of natural
numbers and a natural number $t$, $t$ lies in the ε-closure of $X$ in the ε-NFA that $N$ denotes
if and only if $t$ is reachable from some $u \in X$ by a sequence of zero or more ε-moves of $N$. -/
theorem mem_εClosure_iff {N : EncodedNFA α} {X : Set ℕ} {t : ℕ} :
    t ∈ N.toεNFA.εClosure X ↔ ∃ u ∈ X, Relation.ReflTransGen N.EpsRel u t := by
  constructor
  · intro ht
    induction ht using εNFA.εClosure_induction with
    | base x hx => exact ⟨x, hx, .refl⟩
    | step x y hyx _ ih =>
        obtain ⟨u, hu, h⟩ := ih
        exact ⟨u, hu, h.tail hyx⟩
  · rintro ⟨u, hu, h⟩
    induction h with
    | refl => exact N.toεNFA.subset_εClosure X hu
    | tail _ hst ih => exact N.toεNFA.mem_εClosure_of_mem_step hst ih

/-- **ε-successors of a state.** For an encoded NFA $N$ and a state $s$, the ε-successors of $s$
are the list of the targets $t$ of the ε-moves $(s, t)$ of $N$, in the order in which these
ε-moves are listed. -/
def epsNext (N : EncodedNFA α) (s : ℕ) : List ℕ :=
  N.eps.filterMap fun e => cond (decide (e.1 = s)) (some e.2) none

theorem mem_epsNext {N : EncodedNFA α} {s t : ℕ} : t ∈ N.epsNext s ↔ N.EpsRel s t := by
  simp only [epsNext, List.mem_filterMap]
  constructor
  · rintro ⟨⟨s', t'⟩, he, h⟩
    by_cases hs : s' = s
    · subst hs
      simp only [decide_true, Bool.cond_true, Option.some.injEq] at h
      subst h
      exact he
    · simp [hs] at h
  · intro he
    exact ⟨_, he, by simp⟩

/-- **ε-closure of a list of states.** For an encoded NFA $N$ and a list $S$ of states, the
ε-closure of $S$ is a list whose members are exactly the states reachable from some state of $S$
by finitely many ε-moves of $N$ (zero moves included), computed by a search from each state of
$S$. -/
def closure (N : EncodedNFA α) (S : List ℕ) : List ℕ :=
  S.flatMap fun s => EncodedDFA.reachN s N.epsNext (s :: N.states)

theorem mem_closure {N : EncodedNFA α} {S : List ℕ} {t : ℕ} :
    t ∈ N.closure S ↔ ∃ s ∈ S, Relation.ReflTransGen N.EpsRel s t := by
  simp only [closure, List.mem_flatMap]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  have hB : ∀ u ∈ s :: N.states, ∀ v ∈ N.epsNext u, v ∈ s :: N.states := fun u _ v hv =>
    List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨_, mem_epsNext.1 hv, rfl⟩))
  rw [EncodedDFA.mem_reachN_iff List.mem_cons_self hB]
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hst ih => exact ih.tail (mem_epsNext.1 hst)
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hst ih => exact ih.tail (mem_epsNext.2 hst)

theorem mem_closure_iff_εClosure {N : EncodedNFA α} {S : List ℕ} {t : ℕ} :
    t ∈ N.closure S ↔ t ∈ N.toεNFA.εClosure {s | s ∈ S} := by
  rw [mem_closure, mem_εClosure_iff]
  rfl

variable [DecidableEq α]

/-- **Letter step of an encoded NFA.** For an encoded NFA $N$, a list $S$ of states and a letter
$a$, the letter step lists the target $t$ of every transition $((s, a), t)$ of $N$ with $s \in S$,
in the order of the transition list of $N$, without taking the ε-closure. -/
def letterStep (N : EncodedNFA α) (S : List ℕ) (a : α) : List ℕ :=
  N.trans.filterMap fun e => cond (memB S e.1.1 && decide (e.1.2 = a)) (some e.2) none

/-- **One step of an encoded NFA on a list of states.** For an encoded NFA $N$, a list $S$ of
states and a letter $a$, the list of states reached from $S$ on $a$: the ε-closure, computed as a
list, of the list of states $t$ such that $((s, a), t)$ is a transition of $N$ for some $s$ in
$S$. -/
def stepList (N : EncodedNFA α) (S : List ℕ) (a : α) : List ℕ :=
  N.closure (N.letterStep S a)

/-- **Run of an encoded NFA.** For an encoded NFA $N$ and a word $w = a_1 \cdots a_n$, the run of
$N$ on $w$ is the list of states obtained by starting from the ε-closure of the start states of
$N$ and, for each letter $a_i$ in turn, taking the letter step on $a_i$ and then the ε-closure. -/
def run (N : EncodedNFA α) (w : List α) : List ℕ :=
  w.foldl N.stepList (N.closure N.start)

/-- **Membership test for encoded NFAs.** For an encoded NFA $N$ and a word $w$, the membership
test is the Boolean that is true exactly when some state reached on $w$ is an accepting state of
$N$. The states reached on $w$ are computed from the ε-closure of the start states by, for each
letter of $w$ in turn, following the transitions on that letter and taking the ε-closure. -/
def acceptsB (N : EncodedNFA α) (w : List α) : Bool :=
  (N.run w).any (memB N.accept)

theorem mem_letterStep {N : EncodedNFA α} {S : List ℕ} {a : α} {t : ℕ} :
    t ∈ N.letterStep S a ↔ ∃ s ∈ S, ((s, a), t) ∈ N.trans := by
  simp only [letterStep, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, h⟩
    cases hc : (memB S e.1.1 && decide (e.1.2 = a))
    · simp [hc] at h
    · simp only [hc, Bool.cond_true, Option.some.injEq] at h
      simp only [Bool.and_eq_true, memB_iff, decide_eq_true_eq] at hc
      obtain ⟨⟨s, b⟩, t'⟩ := e
      simp only at hc h
      obtain ⟨hs, rfl⟩ := hc
      subst h
      exact ⟨s, hs, he⟩
  · rintro ⟨s, hs, he⟩
    exact ⟨((s, a), t), he, by simp [memB_iff.2 hs]⟩

/-- **The run of an encoded NFA agrees with ε-NFA evaluation.** For an encoded NFA $N$, a word $w$
and a natural number $t$, $t$ is among the states in the run of $N$ on $w$ if and only if $t$ is
among the states that the ε-NFA denoted by $N$ reaches on $w$ from its start states, with ε-moves
allowed before, between and after the letters. -/
theorem mem_run_iff {N : EncodedNFA α} {w : List α} {t : ℕ} :
    t ∈ N.run w ↔ t ∈ N.toεNFA.eval w := by
  induction w using List.reverseRecOn generalizing t with
  | nil => exact mem_closure_iff_εClosure
  | append_singleton w a ih =>
      rw [run, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [← run, stepList, mem_closure, εNFA.eval_append_singleton, εNFA.mem_stepSet_iff]
      simp only [mem_letterStep, mem_εClosure_iff]
      constructor
      · rintro ⟨u, ⟨s, hs, hsu⟩, hut⟩
        exact ⟨s, ih.1 hs, u, hsu, hut⟩
      · rintro ⟨s, hs, u, hsu, hut⟩
        exact ⟨u, ⟨s, ih.2 hs, hsu⟩, hut⟩

/-- **Correctness of the NFA membership test.** For an encoded NFA $N$ and a word $w$, the
membership test returns true on $w$ if and only if $w$ belongs to the language of $N$. -/
theorem acceptsB_iff {N : EncodedNFA α} {w : List α} : N.acceptsB w = true ↔ w ∈ N.language := by
  rw [acceptsB, List.any_eq_true]
  simp only [memB_iff, mem_run_iff]
  constructor
  · rintro ⟨t, ht, hacc⟩
    exact ⟨t, hacc, ht⟩
  · rintro ⟨t, hacc, ht⟩
    exact ⟨t, ht, hacc⟩

/-- Membership in the language of an encoded NFA is decidable, by running it. -/
instance decidableMemLanguage (N : EncodedNFA α) (w : List α) : Decidable (w ∈ N.language) :=
  decidable_of_iff _ acceptsB_iff

/-! ## Emptiness -/

omit [DecidableEq α] in
/-- **The states reached on a word are closed under ε-moves.** Let $N$ be an encoded NFA and $w$ a
word. If $u$ is one of the states that the ε-NFA denoted by $N$ can be in after reading $w$, and
$N$ has an ε-move from $u$ to $v$, then $v$ is also one of these states. -/
theorem eval_epsRel {N : EncodedNFA α} {w : List α} {u v : ℕ} (hu : u ∈ N.toεNFA.eval w)
    (huv : N.EpsRel u v) : v ∈ N.toεNFA.eval w := by
  induction w using List.reverseRecOn with
  | nil => exact N.toεNFA.mem_εClosure_of_mem_step huv hu
  | append_singleton w a _ =>
      rw [εNFA.eval_append_singleton, εNFA.mem_stepSet_iff] at hu ⊢
      obtain ⟨s, hs, hsu⟩ := hu
      exact ⟨s, hs, N.toεNFA.mem_εClosure_of_mem_step huv hsu⟩

/-- **Successors of a state in an encoded NFA.** For an encoded NFA $N$ and a state $s$, this is the
list of the targets $t$ of the transitions $((s, a), t)$ of $N$ on any letter $a$, followed by the
targets $t$ of the ε-moves $(s, t)$ of $N$, each in the order of the corresponding list of $N$. -/
def next (N : EncodedNFA α) (s : ℕ) : List ℕ :=
  N.trans.filterMap (fun e => cond (decide (e.1.1 = s)) (some e.2) none) ++ N.epsNext s

omit [DecidableEq α] in
theorem mem_next {N : EncodedNFA α} {s t : ℕ} :
    t ∈ N.next s ↔ (∃ a, ((s, a), t) ∈ N.trans) ∨ N.EpsRel s t := by
  rw [next, List.mem_append, mem_epsNext]
  refine or_congr_left ?_
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨⟨⟨s', a⟩, t'⟩, he, h⟩
    by_cases hs : s' = s
    · subst hs
      simp only [decide_true, Bool.cond_true, Option.some.injEq] at h
      subst h
      exact ⟨a, he⟩
    · simp [hs] at h
  · rintro ⟨a, he⟩
    exact ⟨_, he, by simp⟩

/-- **Reachable states of an encoded NFA.** For an encoded NFA $N$, this is the list, found by a
search from each start state of $N$ in turn through the start states of $N$ and the targets of
its transitions and ε-moves, of the states reachable from a start state of $N$ by zero or more
moves, each a transition of $N$ on some letter or an ε-move of $N$. -/
def reachable (N : EncodedNFA α) : List ℕ :=
  N.start.flatMap fun s => EncodedDFA.reachN s N.next N.states

omit [DecidableEq α] in
/-- **The reachable states are those some word can lead to.** For an encoded NFA $N$ and a natural
number $t$, $t$ is among the reachable states of $N$ if and only if there is a word $w$ such that
$t$ is among the states that the ε-NFA denoted by $N$ reaches on $w$ from its start states, with
ε-moves allowed before, between and after the letters. -/
theorem mem_reachable_iff {N : EncodedNFA α} {t : ℕ} :
    t ∈ N.reachable ↔ ∃ w, t ∈ N.toεNFA.eval w := by
  have hB : ∀ s ∈ N.states, ∀ u ∈ N.next s, u ∈ N.states := fun s _ u hu => by
    rcases mem_next.1 hu with ⟨a, he⟩ | he
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨_, he, rfl⟩))
    · exact List.mem_append_right _ (List.mem_map.2 ⟨_, he, rfl⟩)
  have hs₀ : ∀ s ∈ N.start, s ∈ N.states := fun s hs =>
    List.mem_append_left _ (List.mem_append_left _ hs)
  simp only [reachable, List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, ht⟩
    rw [EncodedDFA.mem_reachN_iff (hs₀ s hs) hB] at ht
    induction ht with
    | refl => exact ⟨[], N.toεNFA.subset_εClosure _ hs⟩
    | tail _ hst ih =>
        obtain ⟨w, hw⟩ := ih
        rcases mem_next.1 hst with ⟨a, he⟩ | he
        · exact ⟨w ++ [a], by
            rw [εNFA.eval_append_singleton, εNFA.mem_stepSet_iff]
            exact ⟨_, hw, N.toεNFA.subset_εClosure _ he⟩⟩
        · exact ⟨w, eval_epsRel hw he⟩
  · rintro ⟨w, hw⟩
    suffices ∃ s ∈ N.start, Relation.ReflTransGen (fun s t => t ∈ N.next s) s t by
      obtain ⟨s, hs, h⟩ := this
      exact ⟨s, hs, (EncodedDFA.mem_reachN_iff (hs₀ s hs) hB).2 h⟩
    have hmono : ∀ {u v}, Relation.ReflTransGen N.EpsRel u v →
        Relation.ReflTransGen (fun s t => t ∈ N.next s) u v := by
      intro u v h
      induction h with
      | refl => exact .refl
      | tail _ hst ih => exact ih.tail (mem_next.2 (.inr hst))
    induction w using List.reverseRecOn generalizing t with
    | nil =>
        obtain ⟨u, hu, h⟩ := mem_εClosure_iff.1 hw
        exact ⟨u, hu, hmono h⟩
    | append_singleton w a ih =>
        rw [εNFA.eval_append_singleton, εNFA.mem_stepSet_iff] at hw
        obtain ⟨u, hu, hut⟩ := hw
        obtain ⟨v, hv, hvt⟩ := mem_εClosure_iff.1 hut
        obtain ⟨s, hs, h⟩ := ih hu
        exact ⟨s, hs, (h.tail (mem_next.2 (.inl ⟨a, hv⟩))).trans (hmono hvt)⟩

/-- **Emptiness test for encoded NFAs.** For an encoded NFA $N$, the emptiness test is the
Boolean that is true exactly when no state in the list of reachable states of $N$ is an
accepting state of $N$; the reachable states are those reachable from a start state of $N$ by
zero or more moves, each a transition on some letter or an ε-move. -/
def isEmptyB (N : EncodedNFA α) : Bool :=
  N.reachable.all fun s => !memB N.accept s

omit [DecidableEq α] in
theorem isEmptyB_iff {N : EncodedNFA α} : N.isEmptyB = true ↔ N.language = 0 := by
  rw [isEmptyB, List.all_eq_true]
  constructor
  · intro h
    ext w
    simp only [Language.notMem_zero, iff_false]
    rintro ⟨t, ht, htw⟩
    have h' := h t (mem_reachable_iff.2 ⟨w, htw⟩)
    rw [memB_iff.2 ht] at h'
    exact Bool.false_ne_true h'
  · intro h t ht
    obtain ⟨w, hw⟩ := mem_reachable_iff.1 ht
    cases hm : memB N.accept t
    · rfl
    · have : w ∈ N.language := ⟨t, memB_iff.1 hm, hw⟩
      rw [h] at this
      exact absurd this (Language.notMem_zero w)

/-! ## Every finite automaton has an encoding -/

omit [DecidableEq α] in
/-- **Every finite ε-NFA has an encoding.** An `εNFA` over a finite alphabet with finitely many
states has an encoded NFA with the same language. -/
theorem exists_language_eq_εNFA [Finite α] {σ : Type*} [Finite σ] (M : εNFA α σ) :
    ∃ N : EncodedNFA α, N.language = M.accepts := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite σ
  let f : σ → ℕ := fun s => (Fintype.equivFin σ s : ℕ)
  have hf : Function.Injective f := fun x y h => (Fintype.equivFin σ).injective (Fin.ext h)
  let N : EncodedNFA α :=
    ⟨(Finset.univ.filter (· ∈ M.start)).toList.map f,
      (Finset.univ.filter (· ∈ M.accept)).toList.map f,
      ((Finset.univ : Finset ((σ × α) × σ)).filter
        fun p => p.2 ∈ M.step p.1.1 (some p.1.2)).toList.map fun p => ((f p.1.1, p.1.2), f p.2),
      ((Finset.univ : Finset (σ × σ)).filter fun p => p.2 ∈ M.step p.1 none).toList.map
        fun p => (f p.1, f p.2)⟩
  have hstep : ∀ s o u, u ∈ N.toεNFA.step (f s) o ↔ ∃ t, f t = u ∧ t ∈ M.step s o := by
    intro s o u
    cases o with
    | none =>
        change (f s, u) ∈ List.map _ _ ↔ _
        rw [List.mem_map]
        constructor
        · rintro ⟨⟨s', t⟩, hp, he⟩
          simp only [Prod.mk.injEq] at he
          obtain ⟨h1, rfl⟩ := he
          rw [hf h1] at hp
          exact ⟨t, rfl, by simpa using hp⟩
        · rintro ⟨t, rfl, ht⟩
          exact ⟨(s, t), by simpa using ht, rfl⟩
    | some a =>
        change ((f s, a), u) ∈ List.map _ _ ↔ _
        rw [List.mem_map]
        constructor
        · rintro ⟨⟨⟨s', a'⟩, t⟩, hp, he⟩
          simp only [Prod.mk.injEq] at he
          obtain ⟨⟨h1, rfl⟩, rfl⟩ := he
          rw [hf h1] at hp
          exact ⟨t, rfl, by simpa using hp⟩
        · rintro ⟨t, rfl, ht⟩
          exact ⟨((s, a), t), by simpa using ht, rfl⟩
  have hpath : ∀ (x : List (Option α)) (s : σ) (u : ℕ),
      N.toεNFA.IsPath (f s) u x ↔ ∃ t, f t = u ∧ M.IsPath s t x := by
    intro x
    induction x with
    | nil =>
        intro s u
        rw [εNFA.isPath_nil]
        constructor
        · rintro rfl
          exact ⟨s, rfl, .nil s⟩
        · rintro ⟨t, rfl, h⟩
          rw [(εNFA.isPath_nil _).1 h]
    | cons o x ih =>
        intro s u
        simp only [show o :: x = [o] ++ x from rfl, εNFA.isPath_append, εNFA.isPath_singleton]
        constructor
        · rintro ⟨v, hv, hvu⟩
          obtain ⟨t', rfl, ht'⟩ := (hstep s o v).1 hv
          obtain ⟨t, rfl, ht⟩ := (ih t' u).1 hvu
          exact ⟨t, rfl, t', ht', ht⟩
        · rintro ⟨t, rfl, t', ht', ht⟩
          exact ⟨f t', (hstep s o _).2 ⟨t', rfl, ht'⟩, (ih t' _).2 ⟨t, rfl, ht⟩⟩
  refine ⟨N, ?_⟩
  ext w
  rw [language, εNFA.mem_accepts_iff_exists_path, εNFA.mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨s₁, s₂, x, hs₁, hs₂, hx, hp⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs₁
    obtain ⟨t, rfl, ht⟩ := (hpath x s s₂).1 hp
    obtain ⟨t', ht', hft⟩ := List.mem_map.1 hs₂
    rw [hf hft] at ht'
    exact ⟨s, t, x, by simpa using hs, by simpa using ht', hx, ht⟩
  · rintro ⟨s, t, x, hs, ht, hx, hp⟩
    exact ⟨f s, f t, x, List.mem_map.2 ⟨s, by simpa using hs, rfl⟩,
      List.mem_map.2 ⟨t, by simpa using ht, rfl⟩, hx, (hpath x s (f t)).2 ⟨t, rfl, hp⟩⟩

omit [DecidableEq α] in
/-- **Every finite NFA has an encoding.** An NFA over a finite alphabet with finitely many states
has an encoded NFA with the same language. -/
theorem exists_language_eq [Finite α] {σ : Type*} [Finite σ] (M : NFA α σ) :
    ∃ N : EncodedNFA α, N.language = M.accepts := by
  obtain ⟨N, hN⟩ := exists_language_eq_εNFA M.toεNFA
  exact ⟨N, hN.trans M.toεNFA_correct⟩

/-! ## Computability -/

section Computable

/-- **Encoded NFAs as tuples.** The bijection between encoded NFAs over $\alpha$ and quadruples
consisting of a list of natural numbers, a list of natural numbers, a list of elements of
$(\mathbb{N} \times \alpha) \times \mathbb{N}$ and a list of pairs of natural numbers, which sends
an encoded NFA to its start states, accepting states, transitions and ε-moves. -/
def equivProd : EncodedNFA α ≃ List ℕ × List ℕ × List ((ℕ × α) × ℕ) × List (ℕ × ℕ) where
  toFun N := (N.start, N.accept, N.trans, N.eps)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Primcodable α]

instance instPrimcodable : Primcodable (EncodedNFA α) :=
  Primcodable.ofEquiv _ equivProd

omit [DecidableEq α] in
theorem primrec_start : Primrec (start (α := α)) :=
  Primrec.fst.comp (Primrec.of_equiv (e := equivProd))

omit [DecidableEq α] in
theorem primrec_accept : Primrec (accept (α := α)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd)))

omit [DecidableEq α] in
theorem primrec_trans : Primrec (trans (α := α)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd))))

omit [DecidableEq α] in
theorem primrec_eps : Primrec (eps (α := α)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := equivProd))))

omit [DecidableEq α] in
theorem primrec_states : Primrec (states (α := α)) :=
  Primrec.list_append.comp
    (Primrec.list_append.comp primrec_start
      (Primrec.list_map primrec_trans (Primrec.snd.comp Primrec.snd).to₂))
    (Primrec.list_map primrec_eps (Primrec.snd.comp Primrec.snd).to₂)

omit [DecidableEq α] in
theorem primrec_epsNext : Primrec₂ (epsNext (α := α)) :=
  Primrec.listFilterMap (primrec_eps.comp Primrec.fst)
    (Primrec.cond
      (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const none)).to₂

omit [DecidableEq α] in
theorem primrec_closure : Primrec₂ (closure (α := α)) :=
  Primrec.list_flatMap Primrec.snd
    (EncodedDFA.primrec_reachN Primrec.snd
      (primrec_epsNext.comp₂ (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
        Primrec₂.right)
      (Primrec.list_cons.comp Primrec.snd (primrec_states.comp (Primrec.fst.comp Primrec.fst)))).to₂

theorem primrec_letterStep :
    Primrec fun p : EncodedNFA α × List ℕ × α => p.1.letterStep p.2.1 p.2.2 :=
  Primrec.listFilterMap (primrec_trans.comp Primrec.fst)
    (Primrec.cond
      (Primrec.and.comp
        (primrec_memB.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.eq.decide.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const none)).to₂

theorem primrec_stepList :
    Primrec fun p : EncodedNFA α × List ℕ × α => p.1.stepList p.2.1 p.2.2 :=
  primrec_closure.comp Primrec.fst primrec_letterStep

theorem primrec_run : Primrec₂ (run (α := α)) :=
  Primrec.list_foldl Primrec.snd (primrec_closure.comp Primrec.fst (primrec_start.comp Primrec.fst))
    (primrec_stepList.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))).to₂

theorem primrec_acceptsB : Primrec₂ (acceptsB (α := α)) :=
  (primrec_list_any (primrec_memB.comp₂ (primrec_accept.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
      Primrec₂.right) primrec_run).to₂

omit [DecidableEq α] in
theorem primrec_next : Primrec₂ (next (α := α)) :=
  Primrec.list_append.comp
    (Primrec.listFilterMap (primrec_trans.comp Primrec.fst)
      (Primrec.cond
        (Primrec.eq.decide.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const none)).to₂)
    primrec_epsNext

omit [DecidableEq α] in
theorem primrec_reachable : Primrec (reachable (α := α)) :=
  Primrec.list_flatMap primrec_start
    (EncodedDFA.primrec_reachN Primrec.snd (primrec_next.comp₂ (Primrec.fst.comp₂ Primrec₂.left)
      Primrec₂.right) (primrec_states.comp Primrec.fst)).to₂

omit [DecidableEq α] in
theorem primrec_isEmptyB : Primrec (isEmptyB (α := α)) :=
  primrec_list_all (Primrec.not.comp₂ (primrec_memB.comp₂ (primrec_accept.comp₂ Primrec₂.left)
    Primrec₂.right)) primrec_reachable

omit [DecidableEq α] in
/-- **Membership for NFAs is decidable.** For every alphabet $\alpha$ with a primitive recursive
encoding, the property of a pair $(N, w)$, where $N$ is an encoded NFA (with ε-moves) over
$\alpha$ and $w$ is a word over $\alpha$, that $w$ is in the language of $N$ is decidable by a
multi-stack machine. This is Sipser, Theorem 4.2: the problem $A_{\mathrm{NFA}}$ is decidable. -/
theorem tm2Decidable_mem_language :
    TM2Decidable fun p : EncodedNFA α × List α => p.2 ∈ p.1.language := by
  classical
  exact tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_acceptsB fun _ => acceptsB_iff)

omit [DecidableEq α] in
/-- **Emptiness of NFAs is decidable.** For every alphabet $\alpha$ with a primitive recursive
encoding, the property of an encoded NFA $N$ (with ε-moves) over $\alpha$ that its language is
empty is decidable by a multi-stack machine. This is the problem $E_{\mathrm{NFA}}$. -/
theorem tm2Decidable_language_eq_zero : TM2Decidable fun N : EncodedNFA α => N.language = 0 :=
  tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_isEmptyB fun _ => isEmptyB_iff)

end Computable

end EncodedNFA

end Cslib.Automata
