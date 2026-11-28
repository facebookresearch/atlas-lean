/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Regular languages under substitution
-/
module

public import CSLibExt.Computability.Languages.Substitution
public import Mathlib.Computability.EpsilonNFA
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

import Mathlib.Data.List.ReduceOption

/-!
# Regular languages under substitution

When `L` is regular over a finite alphabet and every `s a` is regular, so is
`substitution L s`. From a DFA `M` for `L` and DFAs `N a` for the `s a`, an ε-NFA follows a
transition `q -a-> M.step q a` of `M` by an ε-move into a copy of `N a` tagged with `(q, a)`, runs
`N a` on a word, and leaves by an ε-move to `M.step q a` from an accepting state of `N a`.

## Main results

* `Cslib.Language.IsRegular.substitution`: substitution of regular languages into a regular
  language over a finite alphabet is regular. It generalizes `IsRegular.homImage`
  (`RegularHomImage.lean`), which substitutes single words.

The finiteness of the source alphabet is needed: over `ℕ`, the language of all one-letter words
is regular, and substituting `{aⁿbⁿ}` for `n` gives a language that is not.
-/

@[expose] public section

namespace Cslib.Language

namespace RegularSubstitution

variable {T T' : Type*} {σ : Type*} (M : DFA T σ) {τ : T → Type*} (N : ∀ a, DFA T' (τ a))

/-- **The ε-NFA for a substitution.** Let $M$ be a DFA over $T$ with states $\sigma$, and for each
letter $a \in T$ let $N_a$ be a DFA over $T'$ with states $\tau_a$. This ε-NFA over $T'$ has as
states the states $q$ of $M$ and the triples $(q, a, p)$ with $q$ a state of $M$, $a \in T$ and
$p$ a state of $N_a$, read as the state $p$ of the copy of $N_a$ entered from $q$. A state $q$ of
$M$ has an ε-move to $(q, a, s_a)$ for every $a \in T$, where $s_a$ is the start state of $N_a$,
and no letter moves. A state $(q, a, p)$ moves on a letter $b$ to $(q, a, \delta_a(p, b))$, where
$\delta_a$ is the transition function of $N_a$, and has an ε-move, to the state $\delta_M(q, a)$
of $M$, exactly when $p$ is an accepting state of $N_a$; here $\delta_M$ is the transition
function of $M$. The start state is the start state of $M$, and the accepting states are the
accepting states of $M$. -/
def εnfa : εNFA T' (σ ⊕ (σ × Σ a, τ a)) where
  step
    | .inl q, none => {s | ∃ a, s = .inr (q, ⟨a, (N a).start⟩)}
    | .inl _, some _ => ∅
    | .inr (q, ⟨a, p⟩), some b => {.inr (q, ⟨a, (N a).step p b⟩)}
    | .inr (q, ⟨a, p⟩), none => {s | p ∈ (N a).accept ∧ s = .inl (M.step q a)}
  start := {.inl M.start}
  accept := {s | ∃ q ∈ M.accept, s = .inl q}

theorem reduceOption_map_some (l : List T') : (l.map some).reduceOption = l := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.map_cons, List.reduceOption_cons_of_some, ih]

/-- **Paths inside one copy of a letter automaton.** Let $M$ be a DFA over $T$, and for each
letter $a \in T$ let $N_a$ be a DFA over $T'$. For every state $q$ of $M$, letter $a \in T$,
state $p$ of $N_a$ and word $y$ over $T'$, the ε-NFA built from $M$ and the $N_a$ has a path
reading the letters of $y$, with no ε-moves, from the state $p$ of the copy of $N_a$ entered from
$q$ to the state of the same copy that $N_a$ reaches from $p$ on $y$. -/
theorem isPath_run (q : σ) (a : T) (p : τ a) (y : List T') :
    (εnfa M N).IsPath (.inr (q, ⟨a, p⟩)) (.inr (q, ⟨a, (N a).evalFrom p y⟩)) (y.map some) := by
  induction y generalizing p with
  | nil => exact .nil _
  | cons b y ih => exact .cons _ _ _ _ _ rfl (ih _)

/-- **Detour labels.** For a word $y = b_1 \cdots b_n$ over $T'$, the detour labels of $y$ are
the sequence of ε-NFA labels $\varepsilon, b_1, \ldots, b_n, \varepsilon$: an ε-move, the letters
of $y$ in order, and a final ε-move.

They label the detour that the substitution ε-NFA takes through a copy of the automaton for one
letter. -/
def detour (y : List T') : List (Option T') :=
  none :: (y.map some ++ [none])

theorem reduceOption_detour (y : List T') : (detour y).reduceOption = y := by
  rw [detour, List.reduceOption_cons_of_none, List.reduceOption_append, reduceOption_map_some]
  simp

theorem isPath_detour (q : σ) (a : T) {y : List T'} (hy : y ∈ (N a).accepts) :
    (εnfa M N).IsPath (.inl q) (.inl (M.step q a)) (detour y) := by
  refine .cons _ _ _ _ _ ⟨a, rfl⟩ ?_
  refine (εNFA.isPath_append _).2 ⟨_, isPath_run M N q a _ y, ?_⟩
  exact (εNFA.isPath_singleton _).2 ⟨hy, rfl⟩

theorem isPath_word (w : List T) :
    ∀ (q : σ) {y : List T'}, y ∈ (w.map fun a => (N a).accepts).prod →
      ∃ x, x.reduceOption = y ∧ (εnfa M N).IsPath (.inl q) (.inl (M.evalFrom q w)) x := by
  induction w with
  | nil =>
      intro q y hy
      rw [List.map_nil, List.prod_nil, Language.mem_one] at hy
      exact ⟨[], hy.symm ▸ rfl, .nil _⟩
  | cons a w ih =>
      intro q y hy
      rw [List.map_cons, List.prod_cons] at hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Language.mem_mul.1 hy
      obtain ⟨x, hx, hpath⟩ := ih (M.step q a) hy₂
      exact ⟨detour y₁ ++ x, by rw [List.reduceOption_append, reduceOption_detour, hx],
        (εNFA.isPath_append _).2 ⟨_, isPath_detour M N q a hy₁, hpath⟩⟩

/-- **Soundness of the paths of the substitution ε-NFA.** Let $M$ be a DFA over $T$ with start
state $q_0$, and for each letter $a \in T$ let $N_a$ be a DFA over $T'$, with accepted language
$L(N_a)$; for a word $w = a_1 \cdots a_n$ over $T$ write $L_w = L(N_{a_1}) \cdots L(N_{a_n})$,
which is $\{\varepsilon\}$ when $w$ is empty. Let $x$ be a sequence of labels, each a letter of
$T'$ or $\varepsilon$, let $\bar x$ be the word over $T'$ obtained from $x$ by deleting the
$\varepsilon$'s, and suppose the ε-NFA built from $M$ and the $N_a$ has a path reading $x$ from
the state $q_0$ of $M$ to a state $u$. If $u$ is a state $q$ of $M$, then there is a word $w$
over $T$ such that $M$ reaches $q$ from $q_0$ on $w$ and $\bar x \in L_w$. If $u$ is the state
$p$ of the copy of $N_a$ entered from the state $q$ of $M$, then there are a word $w$ over $T$
such that $M$ reaches $q$ from $q_0$ on $w$, a word $y_1 \in L_w$ and a word $y_2$ over $T'$
such that $\bar x = y_1 y_2$ and $N_a$ reaches $p$ from its start state on $y_2$. -/
theorem exists_of_isPath (x : List (Option T')) :
    ∀ u, (εnfa M N).IsPath (.inl M.start) u x →
      (∀ q, u = .inl q →
        ∃ w, M.eval w = q ∧ x.reduceOption ∈ (w.map fun a => (N a).accepts).prod) ∧
      (∀ q a p, u = .inr (q, ⟨a, p⟩) →
        ∃ w, M.eval w = q ∧ ∃ y₁ ∈ (w.map fun a => (N a).accepts).prod, ∃ y₂,
          x.reduceOption = y₁ ++ y₂ ∧ (N a).evalFrom (N a).start y₂ = p) := by
  induction x using List.reverseRecOn with
  | nil =>
      intro u hu
      rw [εNFA.isPath_nil] at hu
      subst hu
      refine ⟨fun q hq => ⟨[], (Sum.inl.inj hq).symm ▸ rfl, ?_⟩, fun _ _ _ h => by cases h⟩
      exact (Language.mem_one _).2 rfl
  | append_singleton x o ih =>
      intro u hu
      obtain ⟨t, ht, hstep⟩ := (εNFA.isPath_append _).1 hu
      rw [εNFA.isPath_singleton] at hstep
      obtain ⟨ihl, ihr⟩ := ih t ht
      rcases t with q | ⟨q, a, p⟩ <;> rcases o with _ | b
      · -- entering a copy of `N a`
        obtain ⟨a, rfl⟩ := hstep
        obtain ⟨w, hw, hwx⟩ := ihl q rfl
        refine ⟨fun _ h => (by cases h), fun q' a' p' h => ?_⟩
        cases h
        exact ⟨w, hw, _, hwx, [], by simp [List.reduceOption_append], rfl⟩
      · exact absurd hstep (Set.notMem_empty _)
      · -- leaving the copy of `N a` from an accepting state
        obtain ⟨hp, rfl⟩ := hstep
        obtain ⟨w, hw, y₁, hy₁, y₂, hx, hy₂⟩ := ihr q a p rfl
        refine ⟨fun q' hq' => ⟨w ++ [a], ?_, ?_⟩, fun _ _ _ h => by cases h⟩
        · rw [DFA.eval_append_singleton, hw, ← Sum.inl.inj hq']
        · rw [List.reduceOption_append, hx, List.map_append, List.prod_append]
          simp only [List.reduceOption_cons_of_none, List.reduceOption_nil, List.append_nil,
            List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          refine Language.mem_mul.2 ⟨y₁, hy₁, y₂, ?_, rfl⟩
          rw [DFA.mem_accepts, DFA.eval, hy₂]
          exact hp
      · -- reading a letter inside the copy of `N a`
        have hstep' : u = .inr (q, ⟨a, (N a).step p b⟩) := hstep
        subst hstep'
        obtain ⟨w, hw, y₁, hy₁, y₂, hx, hy₂⟩ := ihr q a p rfl
        refine ⟨fun _ h => (by cases h), fun q' a' p' h => ?_⟩
        cases h
        refine ⟨w, hw, y₁, hy₁, y₂ ++ [b], ?_, ?_⟩
        · rw [List.reduceOption_append, hx, List.append_assoc]
          rfl
        · rw [DFA.evalFrom_append_singleton, hy₂]

theorem accepts_εnfa : (εnfa M N).accepts =
    {y | ∃ w ∈ M.accepts, y ∈ (w.map fun a => (N a).accepts).prod} := by
  ext y
  rw [εNFA.mem_accepts_iff_exists_path]
  change _ ↔ ∃ w ∈ M.accepts, y ∈ (w.map fun a => (N a).accepts).prod
  constructor
  · rintro ⟨s₁, s₂, x, hs₁, ⟨q, hq, rfl⟩, rfl, hpath⟩
    rw [Set.mem_singleton_iff.1 hs₁] at hpath
    obtain ⟨w, hw, hwx⟩ := (exists_of_isPath M N x _ hpath).1 q rfl
    exact ⟨w, by rwa [DFA.mem_accepts, hw], hwx⟩
  · rintro ⟨w, hw, hy⟩
    obtain ⟨x, hx, hpath⟩ := isPath_word M N w M.start hy
    exact ⟨.inl M.start, .inl (M.eval w), x, rfl, ⟨_, hw, rfl⟩, hx, hpath⟩

end RegularSubstitution

/-- **Regular languages are closed under substitution over a finite alphabet.** Let $T$ be a
finite alphabet and $T'$ any alphabet. If $L$ is a regular language over $T$ and $s(a)$ is a
regular language over $T'$ for every letter $a \in T$, then the substitution of $s$ into $L$ is a
regular language over $T'$. -/
theorem IsRegular.substitution {T T' : Type*} [Finite T] {L : Language T} (hL : L.IsRegular)
    {s : T → Language T'} (hs : ∀ a, (s a).IsRegular) :
    (Cslib.Language.substitution L s).IsRegular := by
  classical
  have := Fintype.ofFinite T
  obtain ⟨σ, _, M, rfl⟩ := hL
  choose τ hτ N hN using hs
  have : ∀ a, Fintype (τ a) := hτ
  refine Language.isRegular_iff.2 ⟨_, inferInstance,
    (RegularSubstitution.εnfa M N).toNFA.toDFA, ?_⟩
  rw [NFA.toDFA_correct, εNFA.toNFA_correct, RegularSubstitution.accepts_εnfa]
  ext y
  change (∃ w ∈ M.accepts, y ∈ (w.map fun a => (N a).accepts).prod) ↔
    ∃ w ∈ M.accepts, y ∈ (w.map s).prod
  simp only [hN]

end Cslib.Language
