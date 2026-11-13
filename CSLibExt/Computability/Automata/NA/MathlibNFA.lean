/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Upstream nondeterministic automata and Mathlib NFAs
-/
module

public import Cslib.Computability.Automata.EpsilonNA.Basic
public import Mathlib.Computability.EpsilonNFA

/-!
# Upstream nondeterministic automata and Mathlib NFAs

Upstream CSLib's finite-word nondeterministic automata (`Cslib.Automata.NA.FinAcc`, and
`Cslib.Automata.εNA.FinAcc` with ε-moves) and Mathlib's `NFA` and `εNFA` are parallel. Several
local constructions, such as Thompson's construction in
`CSLibExt/Computability/Automata/EpsilonNA/Thompson.lean`, are stated on the Mathlib side. This file
identifies the two sides, as `CSLibExt/Computability/Automata/DA/MathlibDFA.lean` does for
deterministic automata.

* `Cslib.Automata.NA.FinAcc.toNFA` and `Cslib.Automata.NA.FinAcc.ofNFA`: the two kinds of
  automata are the same data (mutually inverse, `toNFA_ofNFA`, `ofNFA_toNFA`), running the Mathlib
  form from a set of states gives the upstream multistep image (`toNFA_evalFrom`), and they accept
  the same language (`language_toNFA`, `accepts_ofNFA`).
* `Cslib.Automata.εNA.FinAcc.toεNFA` and `Cslib.Automata.εNA.FinAcc.ofεNFA`: the same for automata
  with ε-moves, where both sides read the label `none` as an ε-move (`toεNFA_ofεNFA`,
  `ofεNFA_toεNFA`). The ε-closures agree (`toεNFA_εClosure`), running the Mathlib form from a set
  of states `S` on a word `xs` reaches exactly the states that upstream saturated multistep
  transitions labelled `xs.map some` reach from `S` (`mem_toεNFA_evalFrom`), and the languages
  agree (`language_toεNFA`, `accepts_ofεNFA`).
-/

@[expose] public section

namespace Cslib.Automata

/-! ## Automata without ε-moves -/

namespace NA.FinAcc

variable {State Symbol : Type*}

/-- An upstream finite-word nondeterministic automaton as a Mathlib `NFA`. -/
def toNFA (M : NA.FinAcc State Symbol) : NFA Symbol State where
  step s a := {s' | M.Tr s a s'}
  start := M.start
  accept := M.accept

/-- A Mathlib `NFA` as an upstream finite-word nondeterministic automaton. -/
def ofNFA (M : NFA Symbol State) : NA.FinAcc State Symbol where
  Tr s a s' := s' ∈ M.step s a
  start := M.start
  accept := M.accept

/-- Converting a Mathlib `NFA` to an upstream automaton and back gives the same `NFA`. -/
@[simp]
theorem toNFA_ofNFA (M : NFA Symbol State) : toNFA (ofNFA M) = M :=
  rfl

/-- Converting an upstream automaton to a Mathlib `NFA` and back gives the same automaton. -/
@[simp]
theorem ofNFA_toNFA (M : NA.FinAcc State Symbol) : ofNFA (toNFA M) = M :=
  rfl

/-- Running the Mathlib form of an upstream automaton from a set of states `S` on a word `xs`
gives the upstream multistep image of `S` under `xs`. -/
theorem toNFA_evalFrom (M : NA.FinAcc State Symbol) (S : Set State) (xs : List Symbol) :
    M.toNFA.evalFrom S xs = M.setImageMultistep S xs := by
  rw [LTS.setImageMultistep_foldl_setImage]
  rfl

/-- An upstream automaton and its Mathlib form accept the same language. -/
@[simp]
theorem language_toNFA (M : NA.FinAcc State Symbol) :
    M.toNFA.accepts = Acceptor.language M := by
  ext xs
  rw [NFA.mem_accepts, toNFA_evalFrom, Acceptor.mem_language]
  constructor
  · rintro ⟨t, ht, hst⟩
    obtain ⟨s, hs, h⟩ := LTS.mem_setImageMultistep.1 hst
    exact ⟨s, hs, t, ht, h⟩
  · rintro ⟨s, hs, t, ht, h⟩
    exact ⟨t, ht, LTS.mem_setImageMultistep.2 ⟨s, hs, h⟩⟩

/-- A Mathlib `NFA` and its upstream form accept the same language. -/
@[simp]
theorem accepts_ofNFA (M : NFA Symbol State) : Acceptor.language (ofNFA M) = M.accepts := by
  rw [← language_toNFA, toNFA_ofNFA]

end NA.FinAcc

/-! ## Automata with ε-moves -/

namespace εNA.FinAcc

variable {State Symbol : Type*}

/-- An upstream finite-word automaton with ε-moves as a Mathlib `εNFA`. Both sides read the label
`none` as an ε-move. -/
def toεNFA (M : εNA.FinAcc State Symbol) : εNFA Symbol State where
  step s a := {s' | M.Tr s a s'}
  start := M.start
  accept := M.accept

/-- A Mathlib `εNFA` as an upstream finite-word automaton with ε-moves. Both sides read the label
`none` as an ε-move. -/
def ofεNFA (M : εNFA Symbol State) : εNA.FinAcc State Symbol where
  Tr s a s' := s' ∈ M.step s a
  start := M.start
  accept := M.accept

/-- Converting a Mathlib `εNFA` to an upstream automaton and back gives the same `εNFA`. -/
@[simp]
theorem toεNFA_ofεNFA (M : εNFA Symbol State) : toεNFA (ofεNFA M) = M :=
  rfl

/-- Converting an upstream automaton with ε-moves to a Mathlib `εNFA` and back gives the same
automaton. -/
@[simp]
theorem ofεNFA_toεNFA (M : εNA.FinAcc State Symbol) : ofεNFA (toεNFA M) = M :=
  rfl

/-- Membership in the upstream ε-closure: reachability by ε-moves from a state of `S`. -/
private theorem mem_εClosure_iff {M : εNA.FinAcc State Symbol} {S : Set State} {t : State} :
    t ∈ M.εClosure S ↔ ∃ s ∈ S, M.τSTr s t := by
  change t ∈ M.saturate.setImage S HasTau.τ ↔ _
  rw [LTS.mem_setImage, LTS.saturate_tr_sTr]
  exact exists_congr fun s => and_congr_right fun _ => LTS.sTr_τSTr_iff M.toLTS

/-- A saturated multistep transition along `μs₁ ++ μs₂` passes through a state reached along
`μs₁`. -/
private theorem sMTr_append {M : εNA.FinAcc State Symbol} {s t : State}
    {μs₁ μs₂ : List (Option Symbol)} (h : M.SMTr s (μs₁ ++ μs₂) t) :
    ∃ u, M.SMTr s μs₁ u ∧ M.SMTr u μs₂ t := by
  induction μs₁ generalizing s with
  | nil => exact ⟨s, LTS.SMTr.refl _ s, h⟩
  | cons μ μs₁ ih =>
    cases h with
    | stepL hstr hrest =>
      obtain ⟨u, hu, hut⟩ := ih hrest
      exact ⟨u, .stepL hstr hu, hut⟩

/-- The Mathlib ε-closure of the Mathlib form of an upstream automaton is the upstream
ε-closure. -/
@[simp]
theorem toεNFA_εClosure (M : εNA.FinAcc State Symbol) (S : Set State) :
    M.toεNFA.εClosure S = M.εClosure S := by
  ext t
  rw [mem_εClosure_iff]
  constructor
  · intro ht
    induction ht using εNFA.εClosure_induction with
    | base x hx => exact ⟨x, hx, .refl⟩
    | step x y hyx _ ih =>
      obtain ⟨s, hs, hsx⟩ := ih
      exact ⟨s, hs, hsx.tail hyx⟩
  · rintro ⟨s, hs, hst⟩
    induction hst with
    | refl => exact M.toεNFA.subset_εClosure S hs
    | tail _ hyz ih => exact M.toεNFA.mem_εClosure_of_mem_step hyz ih

/-- Running the Mathlib form of an upstream automaton from a set of states `S` on a word `xs`
reaches exactly the states that an upstream saturated multistep transition labelled
`xs.map some` reaches from a state of `S`. -/
theorem mem_toεNFA_evalFrom {M : εNA.FinAcc State Symbol} {S : Set State} {xs : List Symbol}
    {t : State} : t ∈ M.toεNFA.evalFrom S xs ↔ ∃ s ∈ S, M.SMTr s (xs.map some) t := by
  induction xs using List.reverseRecOn generalizing t with
  | nil =>
    rw [εNFA.evalFrom_nil, toεNFA_εClosure, mem_εClosure_iff, List.map_nil]
    exact exists_congr fun s => and_congr_right fun _ => LTS.sMTr_τSTr_iff
  | append_singleton xs a ih =>
    rw [εNFA.evalFrom_append_singleton, εNFA.mem_stepSet_iff, List.map_append]
    constructor
    · rintro ⟨u, hu, htu⟩
      obtain ⟨s, hs, hsu⟩ := ih.1 hu
      rw [toεNFA_εClosure, mem_εClosure_iff] at htu
      obtain ⟨v, huv, hvt⟩ := htu
      exact ⟨s, hs, hsu.comp (.stepL (.tr .refl huv hvt) (LTS.SMTr.refl _ t))⟩
    · rintro ⟨s, hs, h⟩
      obtain ⟨u, hsu, hut⟩ := sMTr_append h
      obtain ⟨w, huw, hwt⟩ : ∃ w, M.STr u (some a) w ∧ M.SMTr w [] t := by
        cases hut with
        | stepL huw hwt => exact ⟨_, huw, hwt⟩
      obtain ⟨p, q, hup, hpq, hqw⟩ :
          ∃ p q, M.τSTr u p ∧ M.Tr p (some a) q ∧ M.τSTr q w := by
        cases huw with
        | tr hup hpq hqw => exact ⟨_, _, hup, hpq, hqw⟩
      refine ⟨p, ih.2 ⟨s, hs, ?_⟩, ?_⟩
      · rw [← List.append_nil (xs.map some)]
        exact hsu.comp (LTS.sMTr_τSTr_iff.1 hup)
      · rw [toεNFA_εClosure, mem_εClosure_iff]
        exact ⟨q, hpq, hqw.trans (LTS.sMTr_τSTr_iff.2 hwt)⟩

/-- An upstream automaton with ε-moves and its Mathlib form accept the same language. -/
@[simp]
theorem language_toεNFA (M : εNA.FinAcc State Symbol) :
    M.toεNFA.accepts = Acceptor.language M := by
  ext xs
  change (∃ t ∈ M.accept, t ∈ M.toεNFA.evalFrom M.start xs) ↔
    ∃ s ∈ M.start, ∃ t ∈ M.accept, M.SMTr s (xs.map some) t
  simp only [mem_toεNFA_evalFrom]
  constructor
  · rintro ⟨t, ht, s, hs, h⟩
    exact ⟨s, hs, t, ht, h⟩
  · rintro ⟨s, hs, t, ht, h⟩
    exact ⟨t, ht, s, hs, h⟩

/-- A Mathlib `εNFA` and its upstream form accept the same language. -/
@[simp]
theorem accepts_ofεNFA (M : εNFA Symbol State) : Acceptor.language (ofεNFA M) = M.accepts := by
  rw [← language_toεNFA, toεNFA_ofεNFA]

end εNA.FinAcc

end Cslib.Automata
