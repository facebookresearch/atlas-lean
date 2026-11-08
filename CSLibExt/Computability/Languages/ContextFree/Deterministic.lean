/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Hom
public import CSLibExt.Computability.Languages.ContextFree.InterRegular
public import CSLibExt.Computability.Languages.ContextFree.PDAEquiv
public import Mathlib.Computability.DFA

/-!
# Deterministic pushdown automata and deterministic context-free languages

A pushdown automaton is deterministic when every transition set has at
most one element, and when an `ε`-transition is available from a
configuration no consuming transition is available from it; the machine
can then never choose between two moves, nor between moving on `ε` and
moving on the next input letter.

A language is deterministic context-free when it is accepted by empty
stack by a deterministic pushdown automaton over the alphabet `T ⊕
Unit`, where the extra letter `Sum.inr ()` is an explicit end marker:
the machine accepts exactly the encodings `w ↦ w.map Sum.inl ++
[Sum.inr ()]` of the words of the language. The end marker is
essential: deterministic acceptance by empty stack over the original
alphabet alone accepts only prefix-free languages, since a machine
that has emptied its stack cannot consume further input. In
particular the standard deterministic context-free language `{[],
[a]}` is not prefix-free, so it cannot be accepted that way, but it
is accepted with an end marker (the machine empties its stack on the
marker, whether the input before it was empty or `[a]`). Every
deterministic context-free language is context-free: the encoded
language is accepted by a pushdown automaton, hence context-free, and
the original language is its image under the homomorphism erasing the
end marker, intersected first with the regular language of encodings.

## Main definitions

* `Cslib.Automata.PDA.IsDeterministic`: determinism of a pushdown automaton.
* `Cslib.Language.endMarkerEncode`: append the end marker to a word.
* `Cslib.Language.endMarkerErase`: erase the end marker (and read left letters).
* `Cslib.Language.encodedWords`: the encodings of words over `T`.
* `Cslib.Language.IsDeterministicContextFree`: deterministic context-free
  languages, by end-marker acceptance.

## Main results

* `Cslib.Language.isRegular_encodedWords`: the encodings form a regular language.
* `Cslib.Language.IsDeterministicContextFree.isContextFree`:
  deterministic context-free languages are context-free.
-/

@[expose] public section

namespace Cslib.Automata

variable {T : Type*} {σ : Type*} {Γ : Type*} {M : PDA T σ Γ}

/-- A pushdown automaton is deterministic when every transition set
has at most one element, and an available `ε`-transition precludes
every consuming transition from the same state and stack symbol.
Source: Sipser, Introduction to the Theory of Computation, 3rd ed.,
Chapter 2 (deterministic pushdown automata); Hopcroft, Motwani, and
Ullman, Introduction to Automata Theory, Languages, and Computation,
3rd ed., Section 10.3. -/
def PDA.IsDeterministic (M : PDA T σ Γ) : Prop :=
  (∀ (q : σ) (γ : Γ), (M.step q none γ).card ≤ 1) ∧
    (∀ (q : σ) (a : T) (γ : Γ), (M.step q (some a) γ).card ≤ 1) ∧
    ∀ (q : σ) (γ : Γ), (M.step q none γ).Nonempty →
      ∀ (a : T), M.step q (some a) γ = ∅

end Cslib.Automata

namespace Cslib.Language

open Automata

variable {T : Type*} {L : Language T}

/-- Encode a word by copying it to the left summand and appending the
end marker `Sum.inr ()`.
Source: Hopcroft, Motwani, and Ullman, Introduction to Automata
Theory, Languages, and Computation, 3rd ed., Section 10.3
(deterministic pushdown automata, acceptance by empty stack with an
end marker). -/
def endMarkerEncode (w : List T) : List (T ⊕ Unit) :=
  w.map Sum.inl ++ [Sum.inr ()]

/-- Erase the end marker: a left letter maps to its one-letter word,
the end marker maps to the empty word.
Source: Hopcroft, Motwani, and Ullman, Introduction to Automata
Theory, Languages, and Computation, 3rd ed., Section 10.3
(deterministic pushdown automata, acceptance by empty stack with an
end marker). -/
def endMarkerErase : T ⊕ Unit → List T
  | .inl a => [a]
  | .inr _ => []

/-- The encodings of words over `T`: the words over `T ⊕ Unit`
consisting of left letters followed by a single end marker.
Source: Hopcroft, Motwani, and Ullman, Introduction to Automata
Theory, Languages, and Computation, 3rd ed., Section 10.3
(deterministic pushdown automata, acceptance by empty stack with an
end marker). -/
def encodedWords : Language (T ⊕ Unit) :=
  {u | ∃ w : List T, u = endMarkerEncode w}

/-- Erasing an encoding recovers the word.
Source: Hopcroft, Motwani, and Ullman, Introduction to Automata
Theory, Languages, and Computation, 3rd ed., Section 10.3. -/
theorem endMarkerErase_endMarkerEncode (w : List T) :
    ((endMarkerEncode w).map endMarkerErase).flatten = w := by
  have h1 : ((w.map Sum.inl).map endMarkerErase).flatten = w := by
    induction w with
    | nil => rfl
    | cons a w ih =>
      show (([a] :: (w.map Sum.inl).map endMarkerErase).flatten) = a :: w
      simp only [List.flatten_cons, ih, List.cons_append, List.nil_append]
  have h2 : (([Sum.inr ()] : List (T ⊕ Unit)).map endMarkerErase).flatten = [] :=
    rfl
  rw [endMarkerEncode, List.map_append, List.flatten_append, h1, h2,
    List.append_nil]

/-- Encoding is injective.
Source: Hopcroft, Motwani, and Ullman, Introduction to Automata
Theory, Languages, and Computation, 3rd ed., Section 10.3. -/
theorem endMarkerEncode_injective :
    Function.Injective (endMarkerEncode (T := T)) := by
  intro w w' h
  have h' := congrArg (fun u => (u.map endMarkerErase).flatten) h
  rwa [endMarkerErase_endMarkerEncode, endMarkerErase_endMarkerEncode] at h'

/-- The DFA for the encodings: state `inl false` while reading left
letters, `inl true` after the end marker (the accepting state), and
`inr ()` dead once anything follows the end marker.
Source: Hopcroft, Motwani, and Ullman, Introduction to Automata
Theory, Languages, and Computation, 3rd ed., Section 10.3. -/
noncomputable def endMarkerDFA : DFA (T ⊕ Unit) (Bool ⊕ Unit) where
  step := fun q c => match q, c with
    | .inl false, .inl _ => .inl false
    | .inl false, .inr _ => .inl true
    | .inl true, _ => .inr ()
    | .inr _, _ => .inr ()
  start := .inl false
  accept := {.inl true}

/-- The dead state of the encoding DFA stays dead.
Source: Hopcroft, Motwani, and Ullman, Introduction to Automata
Theory, Languages, and Computation, 3rd ed., Section 10.3. -/
theorem endMarkerDFA_evalFrom_dead (u : List (T ⊕ Unit)) :
    endMarkerDFA.evalFrom (Sum.inr ()) u = Sum.inr () := by
  induction u with
  | nil => rfl
  | cons b u ih => exact ih

/-- The encoding DFA stays in its start state while reading left
letters.
Source: Hopcroft, Motwani, and Ullman, Introduction to Automata
Theory, Languages, and Computation, 3rd ed., Section 10.3. -/
theorem endMarkerDFA_evalFrom_inl (w : List T) :
    endMarkerDFA.evalFrom (Sum.inl false) (w.map Sum.inl) = Sum.inl false := by
  induction w with
  | nil => rfl
  | cons a w ih => exact ih

/-- After the end marker, the encoding DFA can only be in its
accepting state on empty input.
Source: Hopcroft, Motwani, and Ullman, Introduction to Automata
Theory, Languages, and Computation, 3rd ed., Section 10.3. -/
theorem endMarkerDFA_evalFrom_afterMarker {u : List (T ⊕ Unit)}
    (h : endMarkerDFA.evalFrom (Sum.inl true) u = Sum.inl true) : u = [] := by
  cases u with
  | nil => rfl
  | cons b u =>
    have h' : endMarkerDFA.evalFrom (Sum.inr ()) u = Sum.inl true := h
    rw [endMarkerDFA_evalFrom_dead] at h'
    cases h'

/-- The encoding DFA accepts exactly the encodings: it reaches the
accepting state on an encoding.
Source: Hopcroft, Motwani, and Ullman, Introduction to Automata
Theory, Languages, and Computation, 3rd ed., Section 10.3. -/
theorem endMarkerDFA_evalFrom_encode (w : List T) :
    endMarkerDFA.evalFrom (Sum.inl false) (endMarkerEncode w) = Sum.inl true := by
  rw [endMarkerEncode, DFA.evalFrom_of_append, endMarkerDFA_evalFrom_inl]
  rfl

/-- The encoding DFA reaches the accepting state only on encodings.
Source: Hopcroft, Motwani, and Ullman, Introduction to Automata
Theory, Languages, and Computation, 3rd ed., Section 10.3. -/
theorem exists_endMarkerEncode_of_endMarkerDFA_evalFrom {u : List (T ⊕ Unit)}
    (h : endMarkerDFA.evalFrom (Sum.inl false) u = Sum.inl true) :
    ∃ w : List T, u = endMarkerEncode w := by
  induction u with
  | nil => simp at h
  | cons c u ih =>
    cases c with
    | inl a =>
      obtain ⟨w, hw⟩ := ih h
      exact ⟨a :: w, by simp [hw, endMarkerEncode]⟩
    | inr _ =>
      have hu : u = [] := endMarkerDFA_evalFrom_afterMarker h
      exact ⟨[], by rw [hu]; rfl⟩

/-- The encodings of words form a regular language.
Source: Hopcroft, Motwani, and Ullman, Introduction to Automata
Theory, Languages, and Computation, 3rd ed., Section 10.3. -/
theorem isRegular_encodedWords :
    (encodedWords : Language (T ⊕ Unit)).IsRegular := by
  refine ⟨Bool ⊕ Unit, inferInstance, endMarkerDFA, ?_⟩
  ext u
  rw [DFA.mem_accepts]
  constructor
  · intro h
    have heq : endMarkerDFA.evalFrom (Sum.inl false) u = Sum.inl true :=
      Set.mem_singleton_iff.mp h
    exact exists_endMarkerEncode_of_endMarkerDFA_evalFrom heq
  · rintro ⟨w, rfl⟩
    apply Set.mem_singleton_iff.mpr
    show endMarkerDFA.evalFrom (Sum.inl false) (endMarkerEncode w) = Sum.inl true
    exact endMarkerDFA_evalFrom_encode w

/-- A language is deterministic context-free when some deterministic
pushdown automaton with finite state and stack alphabets, whose
transitions consume letters from a finite set, accepts by empty stack
exactly the end-marker encodings of its words.
Source: Ginsburg and Greibach, "Deterministic context free
languages", Information and Control 9 (1966), 620-648; Hopcroft,
Motwani, and Ullman, Introduction to Automata Theory, Languages, and
Computation, 3rd ed., Section 10.3. -/
def IsDeterministicContextFree (L : Language T) : Prop :=
  ∃ (σ Γ : Type) (_ : Fintype σ) (_ : Fintype Γ) (M : PDA (T ⊕ Unit) σ Γ),
    M.IsDeterministic ∧
      (∃ T₀ : Finset (T ⊕ Unit), ∀ (p : σ) (a : T ⊕ Unit) (γ : Γ),
        a ∉ T₀ → M.step p (some a) γ = ∅) ∧
      M.accepts = (fun w : List T => endMarkerEncode w) '' L

/-- Every deterministic context-free language is context-free: the
encoded language is accepted by a pushdown automaton, hence
context-free; intersecting with the regular language of encodings and
erasing the end marker recovers the original language.
Source: Ginsburg and Greibach, "Deterministic context free
languages", Information and Control 9 (1966), 620-648; Hopcroft,
Motwani, and Ullman, Introduction to Automata Theory, Languages, and
Computation, 3rd ed., Section 10.3. -/
theorem IsDeterministicContextFree.isContextFree
    (hL : IsDeterministicContextFree L) : L.IsContextFree := by
  obtain ⟨σ, Γ, hσ, hΓ, M, -, ⟨T₀, hT⟩, hM⟩ := hL
  have := hσ
  have := hΓ
  have hK : M.accepts.IsContextFree :=
    PDA.isContextFree_accepts (M := M) (T₀ := T₀) hT
  have hInter := IsContextFree.inf_isRegular hK isRegular_encodedWords
  have hHom := IsContextFree.homImage hInter endMarkerErase
  have hEq : L = (fun u => (u.map endMarkerErase).flatten) ''
      (M.accepts ⊓ encodedWords) := by
    ext y
    constructor
    · intro hy
      refine ⟨endMarkerEncode y, ⟨?_, ?_⟩, endMarkerErase_endMarkerEncode y⟩
      · rw [hM]
        exact ⟨y, hy, rfl⟩
      · exact ⟨y, rfl⟩
    · rintro ⟨u, ⟨huK, huR⟩, rfl⟩
      obtain ⟨w, hw⟩ := huR
      rw [hM] at huK
      obtain ⟨w', hw'L, henc⟩ := huK
      have hww : w' = w := endMarkerEncode_injective (henc.trans hw)
      rw [hww] at hw'L
      rw [hw]
      change ((endMarkerEncode w).map endMarkerErase).flatten ∈ L
      rw [endMarkerErase_endMarkerEncode]
      exact hw'L
  rw [hEq]
  exact hHom

end Cslib.Language
