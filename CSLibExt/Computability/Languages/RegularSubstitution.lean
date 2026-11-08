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

/-- The ε-NFA: states of `M`, and states `(q, ⟨a, p⟩)` of the copy of `N a` entered from `q`. -/
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

/-- Inside a copy of `N a`, reading `y` runs `N a`. -/
theorem isPath_run (q : σ) (a : T) (p : τ a) (y : List T') :
    (εnfa M N).IsPath (.inr (q, ⟨a, p⟩)) (.inr (q, ⟨a, (N a).evalFrom p y⟩)) (y.map some) := by
  induction y generalizing p with
  | nil => exact .nil _
  | cons b y ih => exact .cons _ _ _ _ _ rfl (ih _)

/-- The labels of the detour through `N a` reading `y`. -/
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

/-- **Soundness of the paths**: a path from the start state reads a word of the substitution
image of a word of `M`, followed by part of a word of the current copy of `N a`. -/
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

/-- **Substitution of regular languages into a regular language over a finite alphabet gives a
regular language.** -/
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
