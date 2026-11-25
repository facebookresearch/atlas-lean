/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Thompson's construction
-/
module

public import Mathlib.Computability.EpsilonNFA
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Option

import Mathlib.Data.List.ReduceOption

/-!
# Thompson's construction: regular expressions to ε-NFAs

K. Thompson, *Regular expression search algorithm*, CACM 11(6), 1968. For a Mathlib
`RegularExpression α`, `Thompson.toεNFA r` is a Mathlib `εNFA` with the finite state type
`Thompson.State r`, built by structural recursion, and `Thompson.accepts_toεNFA` proves that it
accepts exactly `r.matches'`.

The constructions on ε-NFAs, each with its language:

* `zeroAut`, `oneAut`, `charAut a`: the languages `0`, `1` and `{[a]}`.
* `union M N` on `σ ⊕ τ`: `M.accepts + N.accepts` (`accepts_union`).
* `concat M N` on `σ ⊕ τ`, with ε-moves from the accepting states of `M` to the start states of
  `N`: `M.accepts * N.accepts` (`accepts_concat`).
* `star M` on `Option σ`, with a new start and accepting state `none`, an ε-move from it to the
  start states of `M` and ε-moves back from the accepting states of `M`: `M.accepts∗`
  (`accepts_star`).

This is a compact Thompson-style variant rather than Thompson's exact automaton: the automata
use sets of start states, as Mathlib's `εNFA` does, so the union adds no states, the star adds
one state rather than two, and `0` and `1` use zero and one states; `numStates r` counts the
states of the automaton of `r` (`card_state`). Upstream CSLib proves that
the language of every regular expression is regular (`Cslib.Language.IsRegular.regex`) through
closure properties; this file gives the explicit automaton.
-/

@[expose] public section

namespace Cslib.Automata.Thompson

variable {α : Type*}

open εNFA Computability

theorem isPath_cons_iff {σ : Type*} {M : εNFA α σ} {s u : σ} {c : Option α}
    {x : List (Option α)} : M.IsPath s u (c :: x) ↔ ∃ t ∈ M.step s c, M.IsPath t u x := by
  rw [show c :: x = [c] ++ x from rfl, isPath_append]
  simp only [isPath_singleton]

/-! ## Basic automata -/

/-- **The ε-NFA with no states.** Over an alphabet $\alpha$, this is the ε-NFA whose set of
states is empty; consequently it has no start states, no accepting states and no transitions. -/
def zeroAut : εNFA α Empty := ⟨fun s => s.elim, ∅, ∅⟩

/-- **One-state automaton.** The ε-NFA over the alphabet $\alpha$ with a single state, which is both
its start state and its accepting state, and no moves at all (neither letter moves nor
ε-moves). -/
def oneAut : εNFA α Unit := ⟨fun _ _ => ∅, {()}, {()}⟩

/-- **Single-letter automaton.** For a letter $a$ of the alphabet $\alpha$, this is the ε-NFA over
$\alpha$ with two states, a start state and an accepting state, and a single move, which reads $a$
and goes from the start state to the accepting state; it has no other moves and no ε-moves. -/
def charAut (a : α) : εNFA α Bool :=
  ⟨fun s c => {t | s = false ∧ c = some a ∧ t = true}, {false}, {true}⟩

theorem accepts_zeroAut : (zeroAut : εNFA α Empty).accepts = 0 := by
  ext w
  simp only [mem_accepts_iff_exists_path, Language.notMem_zero, iff_false]
  rintro ⟨s, -, -, -, -, -, -⟩
  exact s.elim

theorem accepts_oneAut : (oneAut : εNFA α Unit).accepts = 1 := by
  ext w
  simp only [mem_accepts_iff_exists_path, Language.mem_one]
  constructor
  · rintro ⟨s₁, s₂, x, hs₁, hs₂, rfl, hx⟩
    cases hx with
    | nil => rfl
    | cons _ _ _ _ _ h _ => exact absurd h (Set.notMem_empty _)
  · rintro rfl
    exact ⟨(), (), [], rfl, rfl, rfl, IsPath.nil _⟩

theorem accepts_charAut (a : α) : (charAut a).accepts = {[a]} := by
  have htrue : ∀ {u x}, (charAut a).IsPath true u x → x = [] := by
    intro u x h
    cases h with
    | nil => rfl
    | cons _ _ _ _ _ h _ => exact absurd h.1 (by simp)
  ext w
  rw [mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨s, t, x, hs, ht, rfl, hx⟩
    change s = false at hs
    change t = true at ht
    subst hs ht
    cases hx with
    | cons v _ _ c x hv hrest =>
        obtain ⟨-, rfl, rfl⟩ := hv
        rw [htrue hrest]
        rfl
  · intro hw
    change w = [a] at hw
    subst hw
    exact ⟨false, true, [some a], rfl, rfl, rfl,
      IsPath.cons _ _ _ _ _ ⟨rfl, rfl, rfl⟩ (IsPath.nil _)⟩

/-! ## Union -/

variable {σ τ : Type*} (M : εNFA α σ) (N : εNFA α τ)

/-- **Union of ε-NFAs.** Given ε-NFAs $M$ with state set $\sigma$ and $N$ with state set $\tau$ over
the same alphabet, their union is the ε-NFA on the disjoint union $\sigma \sqcup \tau$ whose moves
are the moves of $M$ and the moves of $N$, whose start states are the start states of $M$ and of
$N$, and whose accepting states are the accepting states of $M$ and of $N$. -/
def union : εNFA α (σ ⊕ τ) where
  step
    | .inl s, c => .inl '' M.step s c
    | .inr t, c => .inr '' N.step t c
  start := .inl '' M.start ∪ .inr '' N.start
  accept := .inl '' M.accept ∪ .inr '' N.accept

variable {M N}

@[simp] theorem union_step_inl (s : σ) (c : Option α) :
    (union M N).step (.inl s) c = .inl '' M.step s c := rfl

@[simp] theorem union_step_inr (t : τ) (c : Option α) :
    (union M N).step (.inr t) c = .inr '' N.step t c := rfl

theorem union_isPath_inl {s : σ} {u : σ ⊕ τ} {x : List (Option α)} :
    (union M N).IsPath (.inl s) u x ↔ ∃ t, u = .inl t ∧ M.IsPath s t x := by
  induction x generalizing s with
  | nil => simp [eq_comm]
  | cons c x ih =>
      rw [isPath_cons_iff]
      constructor
      · rintro ⟨v, hv, hpath⟩
        rw [union_step_inl] at hv
        obtain ⟨s', hs', rfl⟩ := hv
        obtain ⟨t, rfl, ht⟩ := ih.1 hpath
        exact ⟨t, rfl, IsPath.cons _ _ _ _ _ hs' ht⟩
      · rintro ⟨t, rfl, ht⟩
        obtain ⟨s', hs', ht'⟩ := isPath_cons_iff.1 ht
        exact ⟨.inl s', ⟨s', hs', rfl⟩, ih.2 ⟨t, rfl, ht'⟩⟩

theorem union_isPath_inr {s : τ} {u : σ ⊕ τ} {x : List (Option α)} :
    (union M N).IsPath (.inr s) u x ↔ ∃ t, u = .inr t ∧ N.IsPath s t x := by
  induction x generalizing s with
  | nil => simp [eq_comm]
  | cons c x ih =>
      rw [isPath_cons_iff]
      constructor
      · rintro ⟨v, hv, hpath⟩
        rw [union_step_inr] at hv
        obtain ⟨s', hs', rfl⟩ := hv
        obtain ⟨t, rfl, ht⟩ := ih.1 hpath
        exact ⟨t, rfl, IsPath.cons _ _ _ _ _ hs' ht⟩
      · rintro ⟨t, rfl, ht⟩
        obtain ⟨s', hs', ht'⟩ := isPath_cons_iff.1 ht
        exact ⟨.inr s', ⟨s', hs', rfl⟩, ih.2 ⟨t, rfl, ht'⟩⟩

theorem accepts_union : (union M N).accepts = M.accepts + N.accepts := by
  ext w
  simp only [Language.mem_add, mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨s₁, s₂, x, hs₁, hs₂, rfl, hx⟩
    simp only [union, Set.mem_union, Set.mem_image] at hs₁ hs₂
    rcases hs₁ with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · obtain ⟨t, rfl, ht⟩ := union_isPath_inl.1 hx
      refine Or.inl ⟨s, t, x, hs, ?_, rfl, ht⟩
      rcases hs₂ with ⟨t', ht', h⟩ | ⟨t', -, h⟩
      · exact Sum.inl_injective h ▸ ht'
      · exact absurd h Sum.inr_ne_inl
    · obtain ⟨t, rfl, ht⟩ := union_isPath_inr.1 hx
      refine Or.inr ⟨s, t, x, hs, ?_, rfl, ht⟩
      rcases hs₂ with ⟨t', -, h⟩ | ⟨t', ht', h⟩
      · exact absurd h Sum.inl_ne_inr
      · exact Sum.inr_injective h ▸ ht'
  · rintro (⟨s, t, x, hs, ht, rfl, hx⟩ | ⟨s, t, x, hs, ht, rfl, hx⟩)
    · exact ⟨.inl s, .inl t, x, Or.inl ⟨s, hs, rfl⟩, Or.inl ⟨t, ht, rfl⟩, rfl,
        union_isPath_inl.2 ⟨t, rfl, hx⟩⟩
    · exact ⟨.inr s, .inr t, x, Or.inr ⟨s, hs, rfl⟩, Or.inr ⟨t, ht, rfl⟩, rfl,
        union_isPath_inr.2 ⟨t, rfl, hx⟩⟩

/-! ## Concatenation -/

variable (M N) in
/-- **Concatenation of ε-NFAs.** Given ε-NFAs $M$ with state set $\sigma$ and $N$ with state set
$\tau$ over the same alphabet, their concatenation is the ε-NFA on the disjoint union
$\sigma \sqcup \tau$ whose moves are the moves of $M$, the moves of $N$, and an ε-move from every
accepting state of $M$ to every start state of $N$. Its start states are the start states of $M$
and its accepting states are the accepting states of $N$. -/
def concat : εNFA α (σ ⊕ τ) where
  step
    | .inl s, c => .inl '' M.step s c ∪ {u | c = none ∧ s ∈ M.accept ∧ ∃ q ∈ N.start, u = .inr q}
    | .inr t, c => .inr '' N.step t c
  start := .inl '' M.start
  accept := .inr '' N.accept

@[simp] theorem concat_step_inl (s : σ) (c : Option α) :
    (concat M N).step (.inl s) c =
      .inl '' M.step s c ∪ {u | c = none ∧ s ∈ M.accept ∧ ∃ q ∈ N.start, u = .inr q} := rfl

@[simp] theorem concat_step_inr (t : τ) (c : Option α) :
    (concat M N).step (.inr t) c = .inr '' N.step t c := rfl

theorem concat_isPath_inr {s : τ} {u : σ ⊕ τ} {x : List (Option α)} :
    (concat M N).IsPath (.inr s) u x ↔ ∃ t, u = .inr t ∧ N.IsPath s t x := by
  induction x generalizing s with
  | nil => simp [eq_comm]
  | cons c x ih =>
      rw [isPath_cons_iff]
      constructor
      · rintro ⟨v, hv, hpath⟩
        rw [concat_step_inr] at hv
        obtain ⟨s', hs', rfl⟩ := hv
        obtain ⟨t, rfl, ht⟩ := ih.1 hpath
        exact ⟨t, rfl, IsPath.cons _ _ _ _ _ hs' ht⟩
      · rintro ⟨t, rfl, ht⟩
        obtain ⟨s', hs', ht'⟩ := isPath_cons_iff.1 ht
        exact ⟨.inr s', ⟨s', hs', rfl⟩, ih.2 ⟨t, rfl, ht'⟩⟩

theorem concat_isPath_inl_inr {s : σ} {t : τ} {x : List (Option α)} :
    (concat M N).IsPath (.inl s) (.inr t) x ↔
      ∃ p q x₁ x₂, x = x₁ ++ none :: x₂ ∧ M.IsPath s p x₁ ∧ p ∈ M.accept ∧ q ∈ N.start ∧
        N.IsPath q t x₂ := by
  induction x generalizing s with
  | nil =>
      simp only [isPath_nil, reduceCtorEq, false_iff, not_exists, not_and]
      intro p q x₁ x₂ h
      simp at h
  | cons c x ih =>
      rw [isPath_cons_iff]
      constructor
      · rintro ⟨v, hv, hpath⟩
        rw [concat_step_inl] at hv
        rcases hv with ⟨s', hs', rfl⟩ | ⟨rfl, hs, q, hq, rfl⟩
        · obtain ⟨p, q, x₁, x₂, rfl, h₁, hp, hq, h₂⟩ := ih.1 hpath
          exact ⟨p, q, c :: x₁, x₂, rfl, IsPath.cons _ _ _ _ _ hs' h₁, hp, hq, h₂⟩
        · obtain ⟨t', ht', h₂⟩ := concat_isPath_inr.1 hpath
          obtain rfl := Sum.inr_injective ht'
          exact ⟨s, q, [], x, rfl, IsPath.nil _, hs, hq, h₂⟩
      · rintro ⟨p, q, x₁, x₂, hx, h₁, hp, hq, h₂⟩
        cases x₁ with
        | nil =>
            obtain ⟨rfl, rfl⟩ := List.cons.inj hx
            obtain rfl := h₁.eq_of_nil
            exact ⟨.inr q, Or.inr ⟨rfl, hp, q, hq, rfl⟩, concat_isPath_inr.2 ⟨t, rfl, h₂⟩⟩
        | cons c' x₁ =>
            obtain ⟨rfl, rfl⟩ := List.cons.inj hx
            obtain ⟨s', hs', h₁'⟩ := isPath_cons_iff.1 h₁
            exact ⟨.inl s', Or.inl ⟨s', hs', rfl⟩, ih.2 ⟨p, q, x₁, x₂, rfl, h₁', hp, hq, h₂⟩⟩

theorem accepts_concat : (concat M N).accepts = M.accepts * N.accepts := by
  ext w
  simp only [Language.mem_mul, mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨s₁, s₂, x, ⟨s, hs, rfl⟩, ⟨t, ht, rfl⟩, rfl, hx⟩
    obtain ⟨p, q, x₁, x₂, rfl, h₁, hp, hq, h₂⟩ := concat_isPath_inl_inr.1 hx
    refine ⟨x₁.reduceOption, ⟨s, p, x₁, hs, hp, rfl, h₁⟩, x₂.reduceOption,
      ⟨q, t, x₂, hq, ht, rfl, h₂⟩, ?_⟩
    simp [List.reduceOption_append, List.reduceOption_cons_of_none]
  · rintro ⟨_, ⟨s, p, x₁, hs, hp, rfl, h₁⟩, _, ⟨q, t, x₂, hq, ht, rfl, h₂⟩, rfl⟩
    refine ⟨.inl s, .inr t, x₁ ++ none :: x₂, ⟨s, hs, rfl⟩, ⟨t, ht, rfl⟩, ?_,
      concat_isPath_inl_inr.2 ⟨p, q, x₁, x₂, rfl, h₁, hp, hq, h₂⟩⟩
    simp [List.reduceOption_append, List.reduceOption_cons_of_none]

/-! ## Kleene star -/

variable (M) in
/-- **Kleene star of an ε-NFA.** Given an ε-NFA $M$ with state set $\sigma$, its star automaton has
the states of $M$ together with one new state $q_0$, which is its only start state and its only
accepting state. Its moves are the moves of $M$, an ε-move from $q_0$ to every start state of $M$,
and an ε-move from every accepting state of $M$ to $q_0$. -/
def star : εNFA α (Option σ) where
  step
    | none, c => {u | c = none ∧ ∃ q ∈ M.start, u = some q}
    | some s, c => some '' M.step s c ∪ {u | c = none ∧ s ∈ M.accept ∧ u = none}
  start := {none}
  accept := {none}

@[simp] theorem star_step_none (c : Option α) :
    (star M).step none c = {u | c = none ∧ ∃ q ∈ M.start, u = some q} := rfl

@[simp] theorem star_step_some (s : σ) (c : Option α) :
    (star M).step (some s) c = some '' M.step s c ∪ {u | c = none ∧ s ∈ M.accept ∧ u = none} :=
  rfl

theorem star_isPath_some {s t : σ} {x : List (Option α)} (h : M.IsPath s t x) :
    (star M).IsPath (some s) (some t) x := by
  induction h with
  | nil => exact IsPath.nil _
  | cons t s u c x hstep _ ih => exact IsPath.cons _ _ _ _ _ (Or.inl ⟨t, hstep, rfl⟩) ih

theorem star_isPath_some_none {s : σ} {x : List (Option α)}
    (h : (star M).IsPath (some s) none x) :
    ∃ p x₁ x₂, x = x₁ ++ none :: x₂ ∧ M.IsPath s p x₁ ∧ p ∈ M.accept ∧
      (star M).IsPath none none x₂ := by
  induction x generalizing s with
  | nil => exact absurd h.eq_of_nil (by simp)
  | cons c x ih =>
      obtain ⟨v, hv, hpath⟩ := isPath_cons_iff.1 h
      rw [star_step_some] at hv
      rcases hv with ⟨s', hs', rfl⟩ | ⟨rfl, hs, rfl⟩
      · obtain ⟨p, x₁, x₂, rfl, h₁, hp, h₂⟩ := ih hpath
        exact ⟨p, c :: x₁, x₂, rfl, IsPath.cons _ _ _ _ _ hs' h₁, hp, h₂⟩
      · exact ⟨s, [], x, rfl, IsPath.nil _, hs, hpath⟩

theorem star_isPath_none_none {x : List (Option α)} (h : (star M).IsPath none none x) :
    x = [] ∨ ∃ q x', x = none :: x' ∧ q ∈ M.start ∧ (star M).IsPath (some q) none x' := by
  cases x with
  | nil => exact Or.inl rfl
  | cons c x =>
      obtain ⟨v, ⟨rfl, q, hq, rfl⟩, hpath⟩ := isPath_cons_iff.1 h
      exact Or.inr ⟨q, x, rfl, hq, hpath⟩

theorem reduceOption_mem_kstar_of_isPath :
    ∀ (n : ℕ) (x : List (Option α)), x.length = n → (star M).IsPath none none x →
      x.reduceOption ∈ M.accepts∗ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hlen h
    rcases star_isPath_none_none h with rfl | ⟨q, x', rfl, hq, h'⟩
    · exact Language.nil_mem_kstar _
    · obtain ⟨p, x₁, x₂, rfl, h₁, hp, h₂⟩ := star_isPath_some_none h'
      have hlt : x₂.length < n := by
        rw [← hlen]
        simp only [List.length_cons, List.length_append]
        omega
      obtain ⟨L, hL, hmem⟩ := Language.mem_kstar.1 (ih _ hlt x₂ rfl h₂)
      refine Language.mem_kstar.2 ⟨x₁.reduceOption :: L, ?_, ?_⟩
      · simp [List.reduceOption_append, List.reduceOption_cons_of_none, hL]
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact (mem_accepts_iff_exists_path M).2 ⟨q, p, x₁, hq, hp, rfl, h₁⟩
        · exact hmem y hy

theorem accepts_star : (star M).accepts = M.accepts∗ := by
  ext w
  rw [mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨s₁, s₂, x, rfl, rfl, rfl, hx⟩
    exact reduceOption_mem_kstar_of_isPath _ x rfl hx
  · intro hw
    obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.1 hw
    suffices ∃ x, x.reduceOption = L.flatten ∧ (star M).IsPath none none x from
      let ⟨x, hx, hpath⟩ := this
      ⟨none, none, x, rfl, rfl, hx, hpath⟩
    clear hw
    induction L with
    | nil => exact ⟨[], rfl, IsPath.nil _⟩
    | cons y L ih =>
        obtain ⟨x₂, hx₂, h₂⟩ := ih fun z hz => hL z (List.mem_cons_of_mem _ hz)
        obtain ⟨s, t, x₁, hs, ht, rfl, h₁⟩ :=
          (mem_accepts_iff_exists_path M).1 (hL _ List.mem_cons_self)
        refine ⟨none :: (x₁ ++ none :: x₂), ?_, ?_⟩
        · simp [List.reduceOption_append, List.reduceOption_cons_of_none, hx₂]
        · refine IsPath.cons (some s) _ _ _ _ ⟨rfl, s, hs, rfl⟩ ?_
          rw [isPath_append]
          exact ⟨some t, star_isPath_some h₁, IsPath.cons none _ _ _ _ (Or.inr ⟨rfl, ht, rfl⟩) h₂⟩

/-! ## The construction -/

/-- **States of Thompson's automaton.** The state set $S(r)$ of Thompson's automaton of a regular
expression $r$ is defined by structural recursion: $S(0)$ is empty, $S(\varepsilon)$ has one
element, $S(a)$ has two elements for a letter $a$, both $S(P + Q)$ and $S(PQ)$ are the disjoint
union $S(P) \sqcup S(Q)$, and $S(P^*)$ is $S(P)$ together with one new element. -/
def State : RegularExpression α → Type
  | .zero => Empty
  | .epsilon => Unit
  | .char _ => Bool
  | .plus P Q => State P ⊕ State Q
  | .comp P Q => State P ⊕ State Q
  | .star P => Option (State P)

/-- The Thompson automaton has finitely many states. -/
instance instFintypeState : (r : RegularExpression α) → Fintype (State r)
  | .zero => inferInstanceAs (Fintype Empty)
  | .epsilon => inferInstanceAs (Fintype Unit)
  | .char _ => inferInstanceAs (Fintype Bool)
  | .plus P Q =>
      haveI := instFintypeState P
      haveI := instFintypeState Q
      inferInstanceAs (Fintype (State P ⊕ State Q))
  | .comp P Q =>
      haveI := instFintypeState P
      haveI := instFintypeState Q
      inferInstanceAs (Fintype (State P ⊕ State Q))
  | .star P =>
      haveI := instFintypeState P
      inferInstanceAs (Fintype (Option (State P)))

/-- **Thompson's construction.** To each regular expression $r$ over an alphabet $\alpha$ it assigns
an ε-NFA over $\alpha$ with state set $S(r)$, the states of Thompson's automaton of $r$, by
structural recursion: $0$ goes to the automaton with no states, $\varepsilon$ to the one-state
automaton, a letter $a$ to the single-letter automaton of $a$, $P + Q$ to the union of the
automata of $P$ and $Q$, $PQ$ to their concatenation, and $P^*$ to the star automaton of the
automaton of $P$. -/
def toεNFA : (r : RegularExpression α) → εNFA α (State r)
  | .zero => zeroAut
  | .epsilon => oneAut
  | .char a => charAut a
  | .plus P Q => union (toεNFA P) (toεNFA Q)
  | .comp P Q => concat (toεNFA P) (toεNFA Q)
  | .star P => star (toεNFA P)

/-- **Correctness of Thompson's construction**: the automaton accepts exactly the words the
regular expression matches. -/
theorem accepts_toεNFA (r : RegularExpression α) : (toεNFA r).accepts = r.matches' := by
  induction r with
  | zero => exact accepts_zeroAut
  | epsilon => exact accepts_oneAut
  | char a => exact accepts_charAut a
  | plus P Q hP hQ =>
      change (union (toεNFA P) (toεNFA Q)).accepts = P.matches' + Q.matches'
      rw [accepts_union, hP, hQ]
  | comp P Q hP hQ =>
      change (concat (toεNFA P) (toεNFA Q)).accepts = P.matches' * Q.matches'
      rw [accepts_concat, hP, hQ]
  | star P hP =>
      change (star (toεNFA P)).accepts = P.matches'∗
      rw [accepts_star, hP]

/-- **Thompson state count.** The state count $n(r)$ of a regular expression $r$ is defined by
structural recursion: $n(0) = 0$, $n(\varepsilon) = 1$, $n(a) = 2$ for a letter $a$,
$n(P + Q) = n(P) + n(Q)$, $n(PQ) = n(P) + n(Q)$ and $n(P^*) = n(P) + 1$.

It is the number of states of Thompson's automaton of $r$. -/
def numStates : RegularExpression α → ℕ
  | .zero => 0
  | .epsilon => 1
  | .char _ => 2
  | .plus P Q => numStates P + numStates Q
  | .comp P Q => numStates P + numStates Q
  | .star P => numStates P + 1

/-- **Number of states of Thompson's automaton.** For every regular expression $r$, the number of
states of Thompson's automaton of $r$ is $n(r)$, the Thompson state count of $r$: $n(0) = 0$,
$n(\varepsilon) = 1$, $n(a) = 2$ for a letter $a$, $n(P + Q) = n(P) + n(Q)$, $n(PQ) = n(P) + n(Q)$
and $n(P^*) = n(P) + 1$. -/
theorem card_state (r : RegularExpression α) : Fintype.card (State r) = numStates r := by
  induction r with
  | zero => exact Fintype.card_empty
  | epsilon => exact Fintype.card_unit
  | char a => exact Fintype.card_bool
  | plus P Q hP hQ =>
      change Fintype.card (State P ⊕ State Q) = _
      rw [Fintype.card_sum, hP, hQ]
      rfl
  | comp P Q hP hQ =>
      change Fintype.card (State P ⊕ State Q) = _
      rw [Fintype.card_sum, hP, hQ]
      rfl
  | star P hP =>
      change Fintype.card (Option (State P)) = _
      rw [Fintype.card_option, hP]
      rfl

end Cslib.Automata.Thompson
