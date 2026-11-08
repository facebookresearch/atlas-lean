/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Regular languages under word-valued homomorphisms
-/
module

public import Mathlib.Computability.EpsilonNFA
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

import Mathlib.Data.List.ReduceOption

/-!
# Regular languages under word-valued homomorphisms

For a map `φ : T → List T'` from a finite alphabet, the image of a regular language under the
induced word homomorphism `w ↦ (w.map φ).flatten` is regular. From a DFA `M` for the language we
build an ε-NFA that, for each transition `q -a-> M.step q a`, spells out `φ a` along a path of
fresh states `(q, a, i)` (one per position `0 < i < (φ a).length`), or takes an ε-move when
`φ a = []`.

## Main results

* `Cslib.Language.IsRegular.homImage`: homomorphic images of regular languages over finite
  alphabets are regular (backlog B2; the context-free analogue is `IsContextFree.homImage`).

The finiteness of the source alphabet is needed: over `ℕ`, the language of all one-letter words
is regular, and its image under `n ↦ aⁿbⁿ` is not.
-/

@[expose] public section

namespace Cslib.Language

namespace HomImage

variable {T T' : Type*} [Fintype T] (φ : T → List T') {σ : Type*} (M : DFA T σ)

/-- An upper bound on the lengths of the images of the letters. -/
def bound : ℕ :=
  Finset.univ.sup fun a => (φ a).length

theorem length_le_bound (a : T) : (φ a).length ≤ bound φ :=
  Finset.le_sup (f := fun a => (φ a).length) (Finset.mem_univ a)

/-- The states of the ε-NFA: a state of `M`, or a state `q`, a letter `a` and a position `i`
inside `φ a` while it is spelled out from `q`. -/
abbrev State (σ : Type*) : Type _ :=
  σ ⊕ (σ × T × Fin (bound φ))

/-- After spelling out position `i` of `φ a` from `q`: the next position, or `M.step q a` at the
end. -/
def advance (q : σ) (a : T) (i : ℕ) : State φ σ :=
  if h : i + 1 < (φ a).length then .inr (q, a, ⟨i + 1, lt_of_lt_of_le h (length_le_bound φ a)⟩)
  else .inl (M.step q a)

/-- The ε-NFA spelling out the images of the transitions of `M`. -/
def εnfa : εNFA T' (State φ σ) where
  step
    | .inl q, some b => {s | ∃ a, (φ a)[0]? = some b ∧ s = advance φ M q a 0}
    | .inr (q, a, i), some b => {s | (φ a)[i.val]? = some b ∧ s = advance φ M q a i}
    | .inl q, none => {s | ∃ a, φ a = [] ∧ s = .inl (M.step q a)}
    | .inr _, none => ∅
  start := {.inl M.start}
  accept := {s | ∃ q ∈ M.accept, s = .inl q}

/-- The labels of the path spelling out `φ a`: one ε-move when `φ a` is empty. -/
def code (a : T) : List (Option T') :=
  if φ a = [] then [none] else (φ a).map some

theorem reduceOption_map_some (l : List T') : (l.map some).reduceOption = l := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [List.map_cons, List.reduceOption_cons_of_some, ih]

omit [Fintype T] in
theorem reduceOption_code (a : T) : (code φ a).reduceOption = φ a := by
  unfold code
  split_ifs with h
  · simp [h]
  · exact reduceOption_map_some _

/-- From the state after position `i`, the rest of `φ a` leads to `M.step q a`. -/
theorem isPath_advance (q : σ) (a : T) :
    ∀ i, (εnfa φ M).IsPath (advance φ M q a i) (.inl (M.step q a))
      (((φ a).drop (i + 1)).map some) := by
  intro i
  induction h : (φ a).length - (i + 1) generalizing i with
  | zero =>
      have hi : ¬i + 1 < (φ a).length := by omega
      simp only [advance, hi, ↓reduceDIte]
      rw [List.drop_eq_nil_of_le (by omega)]
      exact .nil _
  | succ n ih =>
      have hi : i + 1 < (φ a).length := by omega
      rw [List.drop_eq_getElem_cons hi, List.map_cons]
      refine .cons _ _ _ _ _ ?_ (ih (i + 1) (by omega))
      simp only [advance, hi, ↓reduceDIte]
      exact ⟨List.getElem?_eq_getElem hi, rfl⟩

/-- The path spelling out `φ a` from `q` ends in `M.step q a`. -/
theorem isPath_code (q : σ) (a : T) :
    (εnfa φ M).IsPath (.inl q) (.inl (M.step q a)) (code φ a) := by
  unfold code
  split_ifs with h
  · exact (εNFA.isPath_singleton _).2 ⟨a, h, rfl⟩
  · obtain ⟨b, rest, hb⟩ := List.exists_cons_of_ne_nil h
    have hpath := isPath_advance φ M q a 0
    rw [hb] at hpath ⊢
    refine .cons _ _ _ _ _ ⟨a, by simp [hb], rfl⟩ ?_
    simpa using hpath

theorem isPath_word (q : σ) (w : List T) :
    (εnfa φ M).IsPath (.inl q) (.inl (M.evalFrom q w)) (w.flatMap (code φ)) := by
  induction w generalizing q with
  | nil => exact .nil _
  | cons a w ih =>
      rw [List.flatMap_cons]
      exact (εNFA.isPath_append _).2 ⟨_, isPath_code φ M q a, ih (M.step q a)⟩

omit [Fintype T] in
theorem reduceOption_flatMap_code (w : List T) :
    (w.flatMap (code φ)).reduceOption = (w.map φ).flatten := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [List.flatMap_cons, List.reduceOption_append, reduceOption_code, ih]; rfl

/-- **Soundness of the paths**: a path from the start state spells out the image of a word, up to
the part of the current letter's image already emitted. -/
theorem exists_of_isPath (x : List (Option T')) :
    ∀ u, (εnfa φ M).IsPath (.inl M.start) u x →
      (∀ q, u = .inl q → ∃ w, M.eval w = q ∧ (w.map φ).flatten = x.reduceOption) ∧
      (∀ q a i, u = .inr (q, a, i) →
        ∃ w, M.eval w = q ∧ (w.map φ).flatten ++ (φ a).take i = x.reduceOption) := by
  induction x using List.reverseRecOn with
  | nil =>
      intro u hu
      rw [εNFA.isPath_nil] at hu
      subst hu
      exact ⟨fun q hq => ⟨[], (Sum.inl.inj hq).symm ▸ rfl, rfl⟩, fun _ _ _ h => by cases h⟩
  | append_singleton x o ih =>
      intro u hu
      obtain ⟨t, ht, hstep⟩ := (εNFA.isPath_append _).1 hu
      rw [εNFA.isPath_singleton] at hstep
      obtain ⟨ihl, ihr⟩ := ih t ht
      rcases t with q | ⟨q, a, i⟩ <;> rcases o with _ | b
      · -- an ε-move for a letter with empty image
        obtain ⟨a, ha, rfl⟩ := hstep
        obtain ⟨w, hw, hwx⟩ := ihl q rfl
        refine ⟨fun q' hq' => ⟨w ++ [a], ?_, ?_⟩, fun _ _ _ h => by cases h⟩
        · rw [DFA.eval_append_singleton, hw, ← Sum.inl.inj hq']
        · simp [hwx, ha, List.reduceOption_append]
      · -- the first letter of a nonempty image
        obtain ⟨a, ha, rfl⟩ := hstep
        obtain ⟨w, hw, hwx⟩ := ihl q rfl
        have h0 : 0 < (φ a).length := by
          rcases h : φ a with _ | ⟨c, l⟩
          · simp [h] at ha
          · simp
        have hb : (φ a).take 1 = [b] := by
          rw [List.take_one, List.head?_eq_getElem?, ha]; rfl
        unfold advance
        split_ifs with h1
        · refine ⟨fun _ h => (by cases h), fun q' a' i' h => ?_⟩
          cases h
          refine ⟨w, hw, ?_⟩
          simp [hb, hwx, List.reduceOption_append]
        · refine ⟨fun q' hq' => ⟨w ++ [a], ?_, ?_⟩, fun _ _ _ h => by cases h⟩
          · rw [DFA.eval_append_singleton, hw, ← Sum.inl.inj hq']
          · have hlen : (φ a).length = 1 := by omega
            have : φ a = [b] := by
              rw [← hb, List.take_of_length_le (by omega)]
            simp [this, hwx, List.reduceOption_append]
      · exact absurd hstep (Set.notMem_empty _)
      · -- a later letter of an image
        obtain ⟨hb, rfl⟩ := hstep
        obtain ⟨w, hw, hwx⟩ := ihr q a i rfl
        have hi : i.val < (φ a).length := by
          by_contra h
          rw [List.getElem?_eq_none (by omega)] at hb
          cases hb
        have htake : (φ a).take (i.val + 1) = (φ a).take i.val ++ [b] := by
          rw [List.take_add_one, hb]; rfl
        unfold advance
        split_ifs with h1
        · refine ⟨fun _ h => (by cases h), fun q' a' i' h => ?_⟩
          cases h
          refine ⟨w, hw, ?_⟩
          rw [htake, ← List.append_assoc, hwx, List.reduceOption_append]
          rfl
        · refine ⟨fun q' hq' => ⟨w ++ [a], ?_, ?_⟩, fun _ _ _ h => by cases h⟩
          · rw [DFA.eval_append_singleton, hw, ← Sum.inl.inj hq']
          · have hfull : (φ a).take (i.val + 1) = φ a := List.take_of_length_le (by omega)
            rw [List.map_append, List.flatten_append, List.map_singleton, List.flatten_singleton,
              ← hfull, htake, ← List.append_assoc, hwx, List.reduceOption_append]
            rfl

theorem accepts_εnfa :
    (εnfa φ M).accepts = {y | ∃ w ∈ M.accepts, (w.map φ).flatten = y} := by
  ext y
  rw [εNFA.mem_accepts_iff_exists_path]
  change _ ↔ ∃ w ∈ M.accepts, (w.map φ).flatten = y
  constructor
  · rintro ⟨s₁, s₂, x, hs₁, ⟨q, hq, rfl⟩, rfl, hpath⟩
    rw [Set.mem_singleton_iff.1 hs₁] at hpath
    obtain ⟨w, hw, hwx⟩ := (exists_of_isPath φ M x _ hpath).1 q rfl
    exact ⟨w, by rwa [DFA.mem_accepts, hw], hwx⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨.inl M.start, .inl (M.eval w), w.flatMap (code φ), rfl, ⟨_, hw, rfl⟩,
      reduceOption_flatMap_code φ w, isPath_word φ M M.start w⟩

end HomImage

/-- **Homomorphic images of regular languages over finite alphabets are regular.** -/
theorem IsRegular.homImage {T T' : Type*} [Finite T] {L : Language T} (hL : L.IsRegular)
    (φ : T → List T') : Language.IsRegular ((fun w => (w.map φ).flatten) '' L) := by
  classical
  have := Fintype.ofFinite T
  obtain ⟨σ, _, M, rfl⟩ := hL
  refine Language.isRegular_iff.2 ⟨_, inferInstance, (HomImage.εnfa φ M).toNFA.toDFA, ?_⟩
  rw [NFA.toDFA_correct, εNFA.toNFA_correct, HomImage.accepts_εnfa]
  rfl

end Cslib.Language
