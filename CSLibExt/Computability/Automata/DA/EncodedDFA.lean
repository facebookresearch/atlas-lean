/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Encoded deterministic finite automata
-/
module

public import Mathlib.Computability.DFA
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.Fintype.Prod

/-!
# Encoded deterministic finite automata

Mathlib's `DFA α σ` carries its state type as a parameter, so automata with arbitrary state
types cannot be the inputs of computable functions. An `EncodedDFA α` is a DFA as data: natural
number states, a start state, a list of accepting states and a list of transitions
`((s, a), t)`. On a letter with no listed transition from a state the state does not change, and
the first listed transition applies. It denotes a Mathlib DFA with states `ℕ`
(`EncodedDFA.toDFA`).

## Main results

* `EncodedDFA.exists_language_eq`: every DFA with finitely many states over a finite alphabet has
  an encoding with the same language.
* `EncodedDFA.step_of_not_mem_letters`, `EncodedDFA.step_mem_states`: letters outside the
  transition list fix every state, and the listed states are closed under transitions.
* `EncodedDFA.instPrimcodable`, `EncodedDFA.primrec_step`, `EncodedDFA.primrec₂_eval`: encodings
  are `Primcodable`, and running an encoded DFA is primitive recursive.
-/

@[expose] public section

namespace Cslib.Automata

/-- **Encoded DFA.** An encoded deterministic finite automaton over an alphabet $\alpha$ is a
deterministic finite automaton given as data with natural-number states: a start state in
$\mathbb{N}$, a list of accepting states in $\mathbb{N}$, and a list of transitions $((s, a), t)$
with $s, t \in \mathbb{N}$ and $a \in \alpha$, read as "on letter $a$, state $s$ moves to $t$". -/
structure EncodedDFA (α : Type*) where
  /-- The start state. -/
  start : ℕ
  /-- The accepting states. -/
  accept : List ℕ
  /-- The transitions `((s, a), t)`: on letter `a`, state `s` moves to `t`. The first matching
  transition applies; without one the state does not change. -/
  trans : List ((ℕ × α) × ℕ)

namespace EncodedDFA

variable {α : Type*}

/-! ## Semantics -/

section Semantics

variable [DecidableEq α]

/-- **Transition function of an encoded DFA.** For an encoded DFA $D$, a state $s \in \mathbb{N}$
and a letter $a$, the step of $D$ from $s$ on $a$ is the target of the first transition that $D$
lists from $s$ on $a$, or $s$ itself when $D$ lists no such transition. -/
def step (D : EncodedDFA α) (s : ℕ) (a : α) : ℕ :=
  D.trans.foldr (fun e r => if e.1 = (s, a) then e.2 else r) s

/-- **The automaton denoted by an encoded DFA.** An encoded DFA $D$ over an alphabet $\alpha$
denotes the deterministic automaton over $\alpha$ with state set $\mathbb{N}$ whose start state is
the start state of $D$, whose transition function is the transition function of $D$, and whose
accepting states are the states in the accepting list of $D$. -/
def toDFA (D : EncodedDFA α) : DFA α ℕ where
  step := D.step
  start := D.start
  accept := {s | s ∈ D.accept}

/-- **Language of an encoded DFA.** The language of an encoded DFA $D$ is the set of words $w$
such that the state reached by running $D$ on $w$ from its start state, following its transition
function, is one of its accepting states. -/
def language (D : EncodedDFA α) : Language α :=
  D.toDFA.accepts

theorem mem_language_iff {D : EncodedDFA α} {w : List α} :
    w ∈ D.language ↔ D.toDFA.eval w ∈ D.accept :=
  Iff.rfl

/-- Membership in the language of an encoded DFA is decidable, by running it. -/
instance decidableMemLanguage (D : EncodedDFA α) (w : List α) : Decidable (w ∈ D.language) :=
  inferInstanceAs (Decidable (D.toDFA.eval w ∈ D.accept))

/-- **Letters of an encoded DFA.** The letters of an encoded DFA $D$ form the list of the letters
$a$ of its listed transitions $((s, a), t)$, in the order the transitions are listed. -/
def letters (D : EncodedDFA α) : List α :=
  D.trans.map fun e => e.1.2

/-- **States of an encoded DFA.** The states of an encoded DFA $D$ form the list consisting of its
start state followed by the targets of its listed transitions, in the order they are listed. -/
def states (D : EncodedDFA α) : List ℕ :=
  D.start :: D.trans.map Prod.snd

private theorem foldr_step_cases (l : List ((ℕ × α) × ℕ)) (s : ℕ) (a : α) :
    (l.foldr (fun e r => if e.1 = (s, a) then e.2 else r) s = s ∧
        ∀ e ∈ l, e.1 ≠ (s, a)) ∨
      ∃ e ∈ l, e.1 = (s, a) ∧ l.foldr (fun e r => if e.1 = (s, a) then e.2 else r) s = e.2 := by
  induction l with
  | nil => exact Or.inl ⟨rfl, by simp⟩
  | cons e l ih =>
      simp only [List.foldr_cons]
      by_cases he : e.1 = (s, a)
      · exact Or.inr ⟨e, List.mem_cons_self, he, by simp [he]⟩
      · simp only [he, ite_false]
        rcases ih with ⟨h, hall⟩ | ⟨e', he', hkey, h⟩
        · exact Or.inl ⟨h, fun x hx => by
            rcases List.mem_cons.1 hx with rfl | hx
            · exact he
            · exact hall x hx⟩
        · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hkey, h⟩

/-- **Unlisted transitions fix the state.** Let $D$ be an encoded DFA, $s \in \mathbb{N}$ a state
and $a$ a letter. If $D$ lists no transition from $s$ on $a$, then the transition function of $D$
takes $s$ on $a$ to $s$. -/
theorem step_eq_self {D : EncodedDFA α} {s : ℕ} {a : α} (h : ∀ e ∈ D.trans, e.1 ≠ (s, a)) :
    D.step s a = s := by
  rcases foldr_step_cases D.trans s a with ⟨h', -⟩ | ⟨e, he, hkey, -⟩
  · exact h'
  · exact absurd hkey (h e he)

/-- **A step determined by its listed transitions.** Let $D$ be an encoded DFA, let
$s, t \in \mathbb{N}$ be states and let $a$ be a letter. If $D$ lists at least one transition from
$s$ on $a$, and every transition listed from $s$ on $a$ has target $t$, then the transition
function of $D$ takes $s$ on $a$ to $t$. -/
theorem step_eq_of_forall {D : EncodedDFA α} {s t : ℕ} {a : α}
    (hmem : ∃ e ∈ D.trans, e.1 = (s, a)) (huniq : ∀ e ∈ D.trans, e.1 = (s, a) → e.2 = t) :
    D.step s a = t := by
  rcases foldr_step_cases D.trans s a with ⟨-, hall⟩ | ⟨e, he, hkey, h⟩
  · obtain ⟨e, he, hkey⟩ := hmem
    exact absurd hkey (hall e he)
  · exact h.trans (huniq e he hkey)

/-- **Letters without listed transitions fix every state.** Let $D$ be an encoded DFA and let $a$
be a letter that is not among the letters of $D$, that is, no listed transition of $D$ is labelled
$a$. Then for every state $s \in \mathbb{N}$ the transition function of $D$ takes $s$ on $a$ to
$s$. -/
theorem step_of_not_mem_letters {D : EncodedDFA α} {s : ℕ} {a : α} (h : a ∉ D.letters) :
    D.step s a = s :=
  step_eq_self fun e he hkey => h (List.mem_map.2 ⟨e, he, by rw [hkey]⟩)

/-- **Where a step can lead.** For every encoded DFA $D$, state $s \in \mathbb{N}$ and letter $a$,
the transition function of $D$ takes $s$ on $a$ either to the target of some listed transition of
$D$ or to $s$ itself. -/
theorem step_mem_or_eq (D : EncodedDFA α) (s : ℕ) (a : α) :
    D.step s a ∈ D.trans.map Prod.snd ∨ D.step s a = s := by
  rcases foldr_step_cases D.trans s a with ⟨h, -⟩ | ⟨e, he, -, h⟩
  · exact Or.inr h
  · left
    change List.foldr (fun e r => if e.1 = (s, a) then e.2 else r) s D.trans ∈ _
    rw [h]
    exact List.mem_map_of_mem he

/-- **The listed states are closed under transitions.** Let $D$ be an encoded DFA and let $s$ be
one of its states, that is, its start state or the target of one of its listed transitions. Then
for every letter $a$ the transition function of $D$ takes $s$ on $a$ to one of the states of $D$. -/
theorem step_mem_states {D : EncodedDFA α} {s : ℕ} (hs : s ∈ D.states) (a : α) :
    D.step s a ∈ D.states := by
  rcases D.step_mem_or_eq s a with h | h
  · exact List.mem_cons_of_mem _ h
  · rw [h]
    exact hs

theorem evalFrom_mem_states {D : EncodedDFA α} {s : ℕ} (hs : s ∈ D.states) :
    ∀ w : List α, D.toDFA.evalFrom s w ∈ D.states
  | [] => hs
  | a :: w => evalFrom_mem_states (step_mem_states hs a) w

theorem eval_mem_states (D : EncodedDFA α) (w : List α) : D.toDFA.eval w ∈ D.states :=
  evalFrom_mem_states List.mem_cons_self w

/-- **Complement of an encoded DFA.** The complement of an encoded DFA $D$ has the same start
state and the same transitions as $D$, and its accepting states are those states of $D$ (its
start state and the targets of its listed transitions) that $D$ does not accept. -/
def compl (D : EncodedDFA α) : EncodedDFA α :=
  ⟨D.start, D.states.filter fun s => decide (s ∉ D.accept), D.trans⟩

/-- **The complement DFA accepts the complement language.** For every encoded DFA $D$ and every
word $w$, the complement of $D$ accepts $w$ if and only if $D$ does not accept $w$. -/
theorem mem_language_compl {D : EncodedDFA α} {w : List α} :
    w ∈ D.compl.language ↔ w ∉ D.language := by
  have heval : D.compl.toDFA.eval w = D.toDFA.eval w := rfl
  rw [mem_language_iff, mem_language_iff, heval]
  simp only [compl, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨eval_mem_states D w, h⟩⟩

/-- **Every finite DFA has an encoding.** A DFA over a finite alphabet with finitely many states
has an encoded DFA with the same language. -/
theorem exists_language_eq [Finite α] {σ : Type*} [Finite σ] (M : DFA α σ) :
    ∃ D : EncodedDFA α, D.language = M.accepts := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite σ
  let f : σ → ℕ := fun s => (Fintype.equivFin σ s : ℕ)
  have hf : Function.Injective f := fun x y h => (Fintype.equivFin σ).injective (Fin.ext h)
  let D : EncodedDFA α :=
    ⟨f M.start, (Finset.univ.filter (· ∈ M.accept)).toList.map f,
      (Finset.univ : Finset (σ × α)).toList.map fun p => ((f p.1, p.2), f (M.step p.1 p.2))⟩
  have hstep : ∀ s a, D.step (f s) a = f (M.step s a) := by
    intro s a
    refine step_eq_of_forall ⟨((f s, a), f (M.step s a)),
      List.mem_map.2 ⟨(s, a), Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩, rfl⟩ ?_
    intro e he hkey
    obtain ⟨⟨s', a'⟩, -, rfl⟩ := List.mem_map.1 he
    simp only [Prod.mk.injEq] at hkey
    obtain ⟨h1, rfl⟩ := hkey
    rw [hf h1]
  have heval : ∀ w, D.toDFA.eval w = f (M.eval w) := by
    intro w
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w a ih =>
        rw [DFA.eval_append_singleton, DFA.eval_append_singleton, ih]
        exact hstep _ a
  refine ⟨D, ?_⟩
  ext w
  rw [mem_language_iff, heval, DFA.mem_accepts]
  constructor
  · intro h
    obtain ⟨s, hs, hfs⟩ := List.mem_map.1 h
    rw [← hf hfs]
    simpa using hs
  · intro h
    exact List.mem_map.2 ⟨_, by simpa using h, rfl⟩

end Semantics

/-! ## Computability -/

section Primcodable

/-- **Encoded DFAs as triples.** Sending an encoded DFA over $\alpha$ to the triple of its start
state, its list of accepting states and its list of transitions is an equivalence (a bijection
with explicit inverse) between encoded DFAs over $\alpha$ and the set
$\mathbb{N} \times \mathrm{List}\,\mathbb{N} \times \mathrm{List}((\mathbb{N} \times \alpha) \times
\mathbb{N})$. -/
def equivProd : EncodedDFA α ≃ ℕ × List ℕ × List ((ℕ × α) × ℕ) where
  toFun D := (D.start, D.accept, D.trans)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Primcodable α]

instance instPrimcodable : Primcodable (EncodedDFA α) :=
  Primcodable.ofEquiv _ equivProd

theorem primrec_equivProd : Primrec (equivProd (α := α)) :=
  Primrec.of_equiv

theorem primrec_start : Primrec (start (α := α)) :=
  Primrec.fst.comp primrec_equivProd

theorem primrec_accept : Primrec (accept (α := α)) :=
  Primrec.fst.comp (Primrec.snd.comp primrec_equivProd)

theorem primrec_trans : Primrec (trans (α := α)) :=
  Primrec.snd.comp (Primrec.snd.comp primrec_equivProd)

/-- **Assembling an encoded DFA is primitive recursive.** Let $\alpha$ be an alphabet with a
primitive recursive encoding, and encode encoded DFAs over $\alpha$ through their start state,
accepting states and transitions. The map sending a triple $(s, F, T)$, where $s \in \mathbb{N}$,
$F$ is a list of natural numbers and $T$ is a list of pairs $((q, a), t)$ with $q, t \in \mathbb{N}$
and $a \in \alpha$, to the encoded DFA over $\alpha$ with start state $s$, accepting states $F$
and transitions $T$ is primitive recursive. -/
theorem primrec_mk : Primrec fun p : ℕ × List ℕ × List ((ℕ × α) × ℕ) => (⟨p.1, p.2.1, p.2.2⟩ :
    EncodedDFA α) :=
  (Primrec.of_equiv_symm (e := equivProd)).of_eq fun _ => rfl

variable [DecidableEq α]

/-- **The transition function of encoded DFAs is primitive recursive.** Let $\alpha$ be an
alphabet with a primitive recursive encoding and decidable equality, and encode encoded DFAs over
$\alpha$ through their start state, accepting states and transitions. The map sending an encoded
DFA $D$ over $\alpha$, a state $s \in \mathbb{N}$ and a letter $a \in \alpha$ to the state that
$D$ moves to from $s$ on $a$ (the target of the first transition listed for $(s, a)$, or $s$ if
there is none) is primitive recursive. -/
theorem primrec_step : Primrec fun p : EncodedDFA α × ℕ × α => p.1.step p.2.1 p.2.2 :=
  Primrec.list_foldr (primrec_trans.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
    (Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

/-- **Running an encoded DFA is primitive recursive.** Let $\alpha$ be an alphabet with a
primitive recursive encoding and decidable equality, and encode encoded DFAs over $\alpha$
through their start state, accepting states and transitions. The map sending an encoded DFA $D$
and a word $w$ over $\alpha$ to the state reached by running $D$ on $w$ from its start state is
primitive recursive. -/
theorem primrec₂_eval : Primrec₂ fun (D : EncodedDFA α) (w : List α) => D.toDFA.eval w :=
  Primrec.list_foldl Primrec.snd (primrec_start.comp Primrec.fst)
    (primrec_step.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))).to₂

end Primcodable

end EncodedDFA

end Cslib.Automata
