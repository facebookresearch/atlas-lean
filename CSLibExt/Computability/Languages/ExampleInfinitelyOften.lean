/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Büchi automata for "infinitely often" and "eventually always"
-/
module

public import Cslib.Computability.Languages.OmegaRegularLanguage

/-!
# Büchi automata for "infinitely often" and "eventually always"

For a set `p` of symbols, `infinitelyOften p` is the ω-language of words with infinitely many
letters in `p` (LTL `G F p`), and `eventuallyAlways p` the words whose letters are eventually all
in `p` (LTL `F G p`). Each is accepted by a two-state nondeterministic Büchi automaton
(`language_infinitelyOftenNa`, `language_eventuallyAlwaysNa`), so both are ω-regular, and they
are dual: `compl_infinitelyOften`.

The `infinitelyOften` automaton has a single start state and a functional transition relation,
so each word has exactly one run. The `eventuallyAlways` automaton guesses the
point after which all letters are in `p`; upstream's `Cslib.ωLanguage.Example.eventuallyZero` is
the case `p = {0}` over `Fin 2`, and upstream shows that no deterministic Büchi automaton accepts
that language (`Cslib.ωLanguage.IsRegular.not_da_buchi`).
-/

@[expose] public section

namespace Cslib.ωLanguage.Example

open Filter ωSequence Automata ωAcceptor

variable {Symbol : Type*}

/-- Words with infinitely many letters in `p`. -/
def infinitelyOften (p : Set Symbol) : ωLanguage Symbol :=
  { xs : ωSequence Symbol | ∃ᶠ k in atTop, xs k ∈ p }

/-- Words whose letters are eventually all in `p`. -/
def eventuallyAlways (p : Set Symbol) : ωLanguage Symbol :=
  { xs : ωSequence Symbol | ∀ᶠ k in atTop, xs k ∈ p }

theorem mem_infinitelyOften {p : Set Symbol} {xs : ωSequence Symbol} :
    xs ∈ infinitelyOften p ↔ ∃ᶠ k in atTop, xs k ∈ p :=
  Iff.rfl

theorem mem_eventuallyAlways {p : Set Symbol} {xs : ωSequence Symbol} :
    xs ∈ eventuallyAlways p ↔ ∀ᶠ k in atTop, xs k ∈ p :=
  Iff.rfl

/-- Not infinitely often in `p` is eventually always outside `p`. -/
theorem compl_infinitelyOften (p : Set Symbol) :
    (infinitelyOften p)ᶜ = eventuallyAlways pᶜ := by
  apply ωLanguage.mem_ext
  intro xs
  rw [ωLanguage.mem_compl, mem_infinitelyOften, mem_eventuallyAlways, not_frequently]
  rfl

/-- A two-state Büchi automaton for `infinitelyOften p`, with a single start state and exactly one
successor for each state and letter: the state records whether the last letter read was in `p`
(initially `true`), and `true` is accepting. -/
def infinitelyOftenNa (p : Set Symbol) : NA.Buchi Bool Symbol where
  Tr _ x s' := (s' = true ↔ x ∈ p)
  start := {true}
  accept := {true}

theorem language_infinitelyOftenNa (p : Set Symbol) :
    language (infinitelyOftenNa p) = infinitelyOften p := by
  classical
  apply ωLanguage.mem_ext
  intro xs
  rw [mem_language, mem_infinitelyOften]
  constructor
  · rintro ⟨ss, hrun, hacc⟩
    rw [frequently_atTop] at hacc ⊢
    intro a
    obtain ⟨b, hb, hsb⟩ := hacc (a + 1)
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    exact ⟨c, by omega, (hrun.trans c).mp hsb⟩
  · intro h
    let ss : ωSequence Bool := fun k => match k with
      | 0 => true
      | k + 1 => decide (xs k ∈ p)
    refine ⟨ss, ⟨rfl, fun k => ?_⟩, ?_⟩
    · change (decide (xs k ∈ p) = true ↔ xs k ∈ p)
      exact decide_eq_true_iff
    · rw [frequently_atTop] at h ⊢
      intro a
      obtain ⟨b, hb, hpb⟩ := h a
      exact ⟨b + 1, by omega, by
        change decide (xs b ∈ p) ∈ ({true} : Set Bool)
        simp [hpb]⟩

/-- The two-state Büchi automaton for `eventuallyAlways p`: in state `false` it reads anything
and may guess to move to `true`; in state `true`, the accepting state, it only reads letters in
`p` and stays. -/
def eventuallyAlwaysNa (p : Set Symbol) : NA.Buchi Bool Symbol where
  Tr s x s' := s = true → x ∈ p ∧ s' = true
  start := {false}
  accept := {true}

theorem language_eventuallyAlwaysNa (p : Set Symbol) :
    language (eventuallyAlwaysNa p) = eventuallyAlways p := by
  classical
  apply ωLanguage.mem_ext
  intro xs
  rw [mem_language, mem_eventuallyAlways]
  constructor
  · rintro ⟨ss, hrun, hacc⟩
    obtain ⟨m, hm⟩ := Frequently.exists hacc
    have key : ∀ k, ss (m + k) = true := by
      intro k
      induction k with
      | zero => exact hm
      | succ k ih => exact (hrun.trans (m + k) ih).2
    rw [eventually_atTop]
    refine ⟨m, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (hrun.trans (m + k) (key k)).1
  · intro h
    obtain ⟨m, hm⟩ := eventually_atTop.mp h
    let ss : ωSequence Bool := fun k => decide (m < k)
    refine ⟨ss, ⟨?_, fun k hk => ?_⟩, ?_⟩
    · change decide (m < 0) ∈ ({false} : Set Bool)
      simp
    · change decide (m < k) = true at hk
      change xs k ∈ p ∧ decide (m < k + 1) = true
      rw [decide_eq_true_iff] at hk ⊢
      exact ⟨hm k (by omega), by omega⟩
    · apply Eventually.frequently
      rw [eventually_atTop]
      refine ⟨m + 1, fun n hn => ?_⟩
      change decide (m < n) ∈ ({true} : Set Bool)
      simp only [Set.mem_singleton_iff, decide_eq_true_eq]
      omega

theorem isRegular_infinitelyOften (p : Set Symbol) : (infinitelyOften p).IsRegular :=
  ⟨Bool, inferInstance, infinitelyOftenNa p, language_infinitelyOftenNa p⟩

theorem isRegular_eventuallyAlways (p : Set Symbol) : (eventuallyAlways p).IsRegular :=
  ⟨Bool, inferInstance, eventuallyAlwaysNa p, language_eventuallyAlwaysNa p⟩

end Cslib.ωLanguage.Example
