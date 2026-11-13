/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Regular languages under shuffle and cyclic shift
-/
module

public import Cslib.Computability.Languages.RegularLanguage
public import Mathlib.Computability.NFA

/-!
# Regular languages under shuffle and cyclic shift

Two closure properties of the regular languages (Hopcroft and Ullman, *Introduction to Automata
Theory, Languages, and Computation*, 1979, exercises to Chapter 3):

* **Shuffle.** `IsShuffle u v w` says that `w` interleaves `u` and `v`, and
  `shuffle L M = {w | ∃ u ∈ L, ∃ v ∈ M, IsShuffle u v w}`. An NFA on pairs of states advances
  one of two DFAs at each letter (`RegularShuffle.shuffleNFA`); `IsRegular.shuffle`.
* **Cyclic shift.** `cyclicShift L = {y ++ x | x ++ y ∈ L}`. With `q` the state a DFA for `L`
  reaches on `x`, the word `y ++ x` lies in (words leading from `q` to acceptance) · (words
  leading from the start to `q`), a finite union of products of regular languages
  (`cyclicShift_eq_iSup`); `IsRegular.cyclicShift`.
-/

@[expose] public section

namespace Cslib.Language

variable {α : Type*}

/-- `IsShuffle u v w`: the word `w` interleaves `u` and `v`. -/
inductive IsShuffle : List α → List α → List α → Prop
  | nil : IsShuffle [] [] []
  | left {u v w : List α} (a : α) : IsShuffle u v w → IsShuffle (a :: u) v (a :: w)
  | right {u v w : List α} (a : α) : IsShuffle u v w → IsShuffle u (a :: v) (a :: w)

theorem isShuffle_nil_iff {u v : List α} : IsShuffle u v [] ↔ u = [] ∧ v = [] := by
  constructor
  · rintro ⟨⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .nil

theorem isShuffle_cons_iff {u v w : List α} {a : α} :
    IsShuffle u v (a :: w) ↔
      (∃ u', u = a :: u' ∧ IsShuffle u' v w) ∨ ∃ v', v = a :: v' ∧ IsShuffle u v' w := by
  constructor
  · rintro (_ | ⟨_, h⟩ | ⟨_, h⟩)
    · exact .inl ⟨_, rfl, h⟩
    · exact .inr ⟨_, rfl, h⟩
  · rintro (⟨u', rfl, h⟩ | ⟨v', rfl, h⟩)
    exacts [.left a h, .right a h]

/-- The shuffle of two languages: all interleavings of a word of `L` with a word of `M`. -/
def shuffle (L M : Language α) : Language α :=
  {w | ∃ u ∈ L, ∃ v ∈ M, IsShuffle u v w}

@[simp]
theorem mem_shuffle {L M : Language α} {w : List α} :
    w ∈ shuffle L M ↔ ∃ u ∈ L, ∃ v ∈ M, IsShuffle u v w :=
  Iff.rfl

/-- The cyclic shifts of the words of `L`. -/
def cyclicShift (L : Language α) : Language α :=
  {w | ∃ x y, x ++ y ∈ L ∧ w = y ++ x}

@[simp]
theorem mem_cyclicShift {L : Language α} {w : List α} :
    w ∈ cyclicShift L ↔ ∃ x y, x ++ y ∈ L ∧ w = y ++ x :=
  Iff.rfl

namespace RegularShuffle

variable {σ τ : Type*} (M : DFA α σ) (N : DFA α τ)

/-- At each letter, advance `M` or `N`. -/
def shuffleNFA : NFA α (σ × τ) where
  step s a := {(M.step s.1 a, s.2), (s.1, N.step s.2 a)}
  start := {(M.start, N.start)}
  accept := M.accept ×ˢ N.accept

theorem mem_shuffleNFA_evalFrom (w : List α) :
    ∀ (S : Set (σ × τ)) (t : σ × τ), t ∈ (shuffleNFA M N).evalFrom S w ↔
      ∃ s ∈ S, ∃ u v, IsShuffle u v w ∧ (M.evalFrom s.1 u, N.evalFrom s.2 v) = t := by
  induction w with
  | nil =>
      intro S t
      rw [NFA.evalFrom_nil]
      constructor
      · intro ht
        exact ⟨t, ht, [], [], .nil, rfl⟩
      · rintro ⟨s, hs, u, v, h, rfl⟩
        obtain ⟨rfl, rfl⟩ := isShuffle_nil_iff.1 h
        exact hs
  | cons a w ih =>
      intro S t
      rw [NFA.evalFrom_cons, ih]
      constructor
      · rintro ⟨s', hs', u, v, h, rfl⟩
        obtain ⟨s, hs, hstep⟩ := NFA.mem_stepSet.1 hs'
        rcases hstep with rfl | rfl
        · exact ⟨s, hs, a :: u, v, .left a h, rfl⟩
        · exact ⟨s, hs, u, a :: v, .right a h, rfl⟩
      · rintro ⟨s, hs, u, v, h, rfl⟩
        rcases isShuffle_cons_iff.1 h with ⟨u', rfl, h'⟩ | ⟨v', rfl, h'⟩
        · exact ⟨(M.step s.1 a, s.2), NFA.mem_stepSet.2 ⟨s, hs, .inl rfl⟩, u', v, h', rfl⟩
        · exact ⟨(s.1, N.step s.2 a), NFA.mem_stepSet.2 ⟨s, hs, .inr rfl⟩, u, v', h', rfl⟩

theorem shuffleNFA_accepts : (shuffleNFA M N).accepts = shuffle M.accepts N.accepts := by
  ext w
  rw [NFA.mem_accepts]
  constructor
  · rintro ⟨t, ht, hw⟩
    obtain ⟨s, hs, u, v, h, rfl⟩ := (mem_shuffleNFA_evalFrom M N w _ t).1 hw
    rw [Set.mem_singleton_iff.1 hs] at ht
    exact mem_shuffle.2 ⟨u, ht.1, v, ht.2, h⟩
  · rintro ⟨u, hu, v, hv, h⟩
    exact ⟨(M.eval u, N.eval v), ⟨hu, hv⟩,
      (mem_shuffleNFA_evalFrom M N w _ _).2 ⟨_, rfl, u, v, h, rfl⟩⟩

/-- The words leading `M` from `p` into `S`. -/
def fromTo (p : σ) (S : Set σ) : Language α :=
  {w | M.evalFrom p w ∈ S}

@[simp]
theorem mem_fromTo {p : σ} {S : Set σ} {w : List α} : w ∈ fromTo M p S ↔ M.evalFrom p w ∈ S :=
  Iff.rfl

theorem fromTo_isRegular [Finite σ] (p : σ) (S : Set σ) : (fromTo M p S).IsRegular := by
  have := Fintype.ofFinite σ
  exact Language.isRegular_iff.2 ⟨σ, inferInstance, ⟨M.step, p, S⟩, rfl⟩

theorem cyclicShift_eq_iSup :
    cyclicShift M.accepts =
      ⨆ q ∈ (Set.univ : Set σ), fromTo M q M.accept * fromTo M M.start {q} := by
  ext w
  simp only [mem_cyclicShift, Language.mem_iSup, Set.mem_univ, iSup_pos, Language.mem_mul,
    mem_fromTo, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    refine ⟨M.eval x, y, ?_, x, rfl, rfl⟩
    change M.evalFrom (M.evalFrom M.start x) y ∈ M.accept
    rw [← DFA.evalFrom_of_append]
    exact hxy
  · rintro ⟨q, y, hy, x, hx, rfl⟩
    refine ⟨x, y, ?_, rfl⟩
    change M.evalFrom M.start (x ++ y) ∈ M.accept
    rw [DFA.evalFrom_of_append, hx]
    exact hy

end RegularShuffle

/-- **The shuffle of two regular languages is regular.** -/
theorem IsRegular.shuffle {L M : Language α} (hL : L.IsRegular) (hM : M.IsRegular) :
    (Cslib.Language.shuffle L M).IsRegular := by
  classical
  obtain ⟨σ, _, D, rfl⟩ := hL
  obtain ⟨τ, _, E, rfl⟩ := hM
  exact ⟨Set (σ × τ), inferInstance, (RegularShuffle.shuffleNFA D E).toDFA, by
    rw [NFA.toDFA_correct, RegularShuffle.shuffleNFA_accepts]⟩

/-- **The cyclic shifts of the words of a regular language form a regular language.** -/
theorem IsRegular.cyclicShift {L : Language α} (hL : L.IsRegular) :
    (Cslib.Language.cyclicShift L).IsRegular := by
  obtain ⟨σ, _, D, rfl⟩ := hL
  rw [RegularShuffle.cyclicShift_eq_iSup]
  exact IsRegular.iSup fun q _ =>
    IsRegular.mul (RegularShuffle.fromTo_isRegular D q _) (RegularShuffle.fromTo_isRegular D _ _)

end Cslib.Language
