/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.NA.MathlibNFA
public import CSLibExt.Computability.Automata.EpsilonNA.Thompson

/-!
# Tests for the bridge between upstream nondeterministic automata and Mathlib NFAs

* Converting a Mathlib NFA (words over `Bool` ending in `true`) to an upstream `NA.FinAcc` and
  back is the identity; a word accepted and a word rejected through the upstream acceptance
  condition transfer to Mathlib's `NFA.accepts`.
* The same for a Mathlib ε-NFA whose start state reaches the loop on `true` only by an ε-move:
  the round trip, the ε-closure and run lemmas, the empty word and `[true]` accepted (both need
  the ε-move), and `[false]` rejected.
* Two degenerate ε-NFAs read upstream: over the empty alphabet, a run around an ε-cycle accepts
  the empty word; without start states, no word is accepted.
* Thompson's automaton of a regular expression, as an upstream `εNA.FinAcc`, accepts the words the
  expression matches.
* The bridge lemmas apply to automata with state and alphabet types in arbitrary universes.
-/

@[expose] public section

namespace Cslib.Automata.MathlibNFATests

open NA.FinAcc εNA.FinAcc

universe u v

/-! ## Automata without ε-moves -/

/-- Guess the last symbol: from state `0`, reading `true` may move to the accepting state `1`. The
language is the words that end in `true`. -/
def endsInTrue : NFA Bool (Fin 2) where
  step s b := if s = 0 then (if b then {0, 1} else {0}) else ∅
  start := {0}
  accept := {1}

example : toNFA (ofNFA endsInTrue) = endsInTrue := rfl

example : Acceptor.language (ofNFA endsInTrue) = endsInTrue.accepts := accepts_ofNFA _

example : [false, true] ∈ endsInTrue.accepts := by
  rw [← accepts_ofNFA]
  refine ⟨0, Set.mem_singleton _, 1, Set.mem_singleton _, .stepL (s2 := 0) ?_ (.stepL ?_ .refl)⟩
  · simp [ofNFA, endsInTrue]
  · simp [ofNFA, endsInTrue]

example : [true, false] ∉ endsInTrue.accepts := by
  rw [← accepts_ofNFA]
  rintro ⟨s, -, t, ht, h⟩
  obtain ⟨u, -, h⟩ := LTS.MTr.cons_iff.1 h
  obtain ⟨v, hv, h⟩ := LTS.MTr.cons_iff.1 h
  rw [LTS.MTr.nil_iff] at h
  subst h
  rw [Set.mem_singleton_iff.1 ht] at hv
  change (1 : Fin 2) ∈ endsInTrue.step u false at hv
  by_cases hu : u = 0 <;> simp [endsInTrue, hu] at hv

/-! ## Automata with ε-moves -/

/-- From the start state `0`, an ε-move to the accepting state `1`, which loops on `true`. The
language is the words `[true, ..., true]`, including the empty word. -/
def trueStar : εNFA Bool (Fin 2) where
  step s c := if s = 0 ∧ c = none then {1} else if s = 1 ∧ c = some true then {1} else ∅
  start := {0}
  accept := {1}

/-- The ε-move of `trueStar`, read upstream. -/
theorem trueStar_tr_none : (ofεNFA trueStar).Tr 0 none 1 := by
  simp [ofεNFA, trueStar]

/-- The loop of `trueStar` on `true`, read upstream. -/
theorem trueStar_tr_true : (ofεNFA trueStar).Tr 1 (some true) 1 := by
  simp [ofεNFA, trueStar]

example : toεNFA (ofεNFA trueStar) = trueStar := rfl

example (S : Set (Fin 2)) : trueStar.εClosure S = (ofεNFA trueStar).εClosure S := by
  rw [← toεNFA_εClosure, toεNFA_ofεNFA]

example : [] ∈ trueStar.accepts := by
  rw [← accepts_ofεNFA]
  exact ⟨0, Set.mem_singleton _, 1, Set.mem_singleton _, .τ (.single trueStar_tr_none)⟩

example : [true] ∈ trueStar.accepts := by
  rw [← accepts_ofεNFA]
  exact ⟨0, Set.mem_singleton _, 1, Set.mem_singleton _,
    .stepL (.tr (.single trueStar_tr_none) trueStar_tr_true .refl) (LTS.SMTr.refl _ 1)⟩

example : [false] ∉ trueStar.accepts := by
  rw [← accepts_ofεNFA]
  rintro ⟨s, -, t, -, h⟩
  cases h with
  | stepL hstr _ =>
    cases hstr with
    | tr _ htr _ => simp [ofεNFA, trueStar] at htr

example (xs : List Bool) (S : Set (Fin 2)) (t : Fin 2) :
    t ∈ trueStar.evalFrom S xs ↔ ∃ s ∈ S, (ofεNFA trueStar).SMTr s (xs.map some) t := by
  rw [← mem_toεNFA_evalFrom, toεNFA_ofεNFA]

/-- An empty alphabet still permits ε-moves, including a cycle. -/
private def silent : εNFA Empty Bool where
  step _ _ := Set.univ
  start := {false}
  accept := {true}

example : [] ∈ Acceptor.language (ofεNFA silent) := by
  rw [accepts_ofεNFA, εNFA.mem_accepts_iff_exists_path]
  exact ⟨false, true, [none, none, none], rfl, rfl, rfl,
    εNFA.IsPath.cons true false true none _ trivial
      (εNFA.IsPath.cons false true true none _ trivial
        (εNFA.IsPath.cons true false true none [] trivial (εNFA.IsPath.nil true)))⟩

/-- Without initial states, even arbitrary ε-moves cannot accept a word. -/
private def noStart : εNFA Bool Unit where
  step _ _ := Set.univ
  start := ∅
  accept := Set.univ

example (xs : List Bool) : xs ∉ Acceptor.language (ofεNFA noStart) := by
  rw [accepts_ofεNFA]
  simp [εNFA.mem_accepts_iff_exists_path, noStart]

/-- Thompson's automaton, read as an upstream automaton with ε-moves, accepts exactly the words
that the regular expression matches. -/
example {α : Type*} (r : RegularExpression α) :
    Acceptor.language (ofεNFA (Thompson.toεNFA r)) = r.matches' := by
  rw [accepts_ofεNFA, Thompson.accepts_toεNFA]

/-! ## Arbitrary universes -/

example {State : Type u} {Symbol : Type v} (M : NFA Symbol State) :
    toNFA (ofNFA M) = M := by
  simp

example {State : Type u} {Symbol : Type v} (M : NA.FinAcc State Symbol) :
    (toNFA M).accepts = Acceptor.language M := by
  simp

example {State : Type u} {Symbol : Type v} (M : NFA Symbol State) :
    Acceptor.language (ofNFA M) = M.accepts := by
  simp

example {State : Type u} {Symbol : Type v} (M : NA.FinAcc State Symbol) (S : Set State)
    (xs : List Symbol) : (toNFA M).evalFrom S xs = M.setImageMultistep S xs :=
  toNFA_evalFrom M S xs

example {State : Type u} {Symbol : Type v} (M : εNFA Symbol State) :
    toεNFA (ofεNFA M) = M := by
  simp

example {State : Type u} {Symbol : Type v} (M : εNA.FinAcc State Symbol) (S : Set State) :
    (toεNFA M).εClosure S = M.εClosure S := by
  simp

example {State : Type u} {Symbol : Type v} (M : εNA.FinAcc State Symbol) :
    (toεNFA M).accepts = Acceptor.language M := by
  simp

example {State : Type u} {Symbol : Type v} (M : εNFA Symbol State) :
    Acceptor.language (ofεNFA M) = M.accepts := by
  simp

end Cslib.Automata.MathlibNFATests
