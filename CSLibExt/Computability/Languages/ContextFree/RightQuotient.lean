/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Right quotients of context-free languages by regular languages
-/
module

public import CSLibExt.Computability.Languages.ContextFree.InverseHom
public import CSLibExt.Computability.Languages.ContextFree.InterRegular
public import CSLibExt.Computability.Languages.ContextFree.Hom
public import Cslib.Computability.Languages.RegularLanguage

/-!
# Right quotients of context-free languages by regular languages

The right quotient of a language `L` by a language `R` is the set of words `x` with `x ++ y ∈ L`
for some `y ∈ R`. Over a finite alphabet, the right quotient of a context-free language by a regular
language is context-free, a standard closure property of the context-free languages.

The proof is the classical one: it composes closure properties over the doubled alphabet
`T ⊕ T`, whose right copy marks the removed suffix:

* the words whose unmarked form lies in `L` (an inverse homomorphism,
  `IsContextFree.preimage_hom`, which is where the finite alphabet is used);
* intersected with the regular language `x.map inl ++ y.map inr` for `y ∈ R`
  (`IsContextFree.inf_isRegular`, with `IsRegular.mul` of two small automata);
* mapped by the homomorphism erasing the right copy (`eraseRight`, `IsContextFree.homImage`).

## Main results

* `Cslib.Language.rightQuotientLang L R` and `Cslib.Language.IsContextFree.rightQuotientLang`.
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*}

/-- The right quotient of `L` by `R`: the words `x` with `x ++ y ∈ L` for some `y ∈ R`. The
quotient by a single word is `rightQuotient` (`Congruences/Quotients.lean`). -/
def rightQuotientLang (L R : Language T) : Language T :=
  {x | ∃ y ∈ R, x ++ y ∈ L}

@[simp]
theorem mem_rightQuotientLang {L R : Language T} {x : List T} :
    x ∈ rightQuotientLang L R ↔ ∃ y ∈ R, x ++ y ∈ L :=
  Iff.rfl

namespace RightQuotientLang

/-- The words over the left copy. -/
def leftWords : Language (T ⊕ T) :=
  {u | ∃ x : List T, u = x.map Sum.inl}

/-- The words of `R`, marked by the right copy. -/
def rightWords (R : Language T) : Language (T ⊕ T) :=
  {u | ∃ y ∈ R, u = y.map Sum.inr}

/-- Reads left letters only. -/
def leftDFA : DFA (T ⊕ T) Bool :=
  ⟨fun b c => b && c.isLeft, true, {true}⟩

theorem leftDFA_evalFrom (u : List (T ⊕ T)) :
    ∀ b, leftDFA.evalFrom b u = (b && u.all Sum.isLeft) := by
  induction u with
  | nil => intro b; simp [DFA.evalFrom]
  | cons c u ih =>
      intro b
      rw [DFA.evalFrom_cons, ih]
      simp [leftDFA, Bool.and_assoc]

theorem all_isLeft_iff (u : List (T ⊕ T)) :
    u.all Sum.isLeft = true ↔ ∃ x : List T, u = x.map Sum.inl := by
  induction u with
  | nil => exact ⟨fun _ => ⟨[], rfl⟩, fun _ => rfl⟩
  | cons c u ih =>
      rw [List.all_cons, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hc, x, rfl⟩
        cases c with
        | inl a => exact ⟨a :: x, rfl⟩
        | inr a => simp at hc
      · rintro ⟨_ | ⟨a, x⟩, h⟩
        · cases h
        · simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, x, rfl⟩

theorem leftWords_isRegular : (leftWords : Language (T ⊕ T)).IsRegular := by
  refine ⟨Bool, inferInstance, leftDFA, ?_⟩
  ext u
  rw [DFA.mem_accepts, DFA.eval, leftDFA_evalFrom]
  change (true && u.all Sum.isLeft) = true ↔ _
  rw [Bool.true_and, all_isLeft_iff]
  rfl

variable {σ : Type*} (D : DFA T σ)

/-- Runs `D` on right letters; a left letter leads to the dead state `none`. -/
def rightDFA : DFA (T ⊕ T) (Option σ) where
  step o c := match o, c with
    | some p, .inr a => some (D.step p a)
    | _, _ => none
  start := some D.start
  accept := {o | ∃ p ∈ D.accept, o = some p}

theorem rightDFA_evalFrom_none (u : List (T ⊕ T)) : (rightDFA D).evalFrom none u = none := by
  induction u with
  | nil => rfl
  | cons c u ih => exact ih

theorem rightDFA_evalFrom_some (u : List (T ⊕ T)) :
    ∀ p q, (rightDFA D).evalFrom (some p) u = some q ↔
      ∃ y : List T, u = y.map Sum.inr ∧ D.evalFrom p y = q := by
  induction u with
  | nil =>
      intro p q
      simp only [DFA.evalFrom_nil, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨[], rfl, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        cases y with
        | nil => rfl
        | cons b y => cases hy
  | cons c u ih =>
      intro p q
      cases c with
      | inl a =>
          change (rightDFA D).evalFrom none u = some q ↔ _
          rw [rightDFA_evalFrom_none]
          simp only [reduceCtorEq, false_iff, not_exists, not_and]
          intro y hy
          cases y with
          | nil => cases hy
          | cons b y => simp at hy
      | inr a =>
          change (rightDFA D).evalFrom (some (D.step p a)) u = some q ↔ _
          rw [ih]
          constructor
          · rintro ⟨y, rfl, hy⟩
            exact ⟨a :: y, rfl, hy⟩
          · rintro ⟨_ | ⟨b, y⟩, h, hy⟩
            · cases h
            · simp only [List.map_cons, List.cons.injEq, Sum.inr.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨y, rfl, hy⟩

theorem rightWords_isRegular {R : Language T} (hR : R.IsRegular) : (rightWords R).IsRegular := by
  obtain ⟨σ, _, D, rfl⟩ := hR
  refine ⟨Option σ, inferInstance, rightDFA D, ?_⟩
  ext u
  rw [DFA.mem_accepts, DFA.eval]
  change (∃ p ∈ D.accept, (rightDFA D).evalFrom (some D.start) u = some p) ↔ _
  constructor
  · rintro ⟨p, hp, h⟩
    obtain ⟨y, rfl, hy⟩ := (rightDFA_evalFrom_some D u _ _).1 h
    exact ⟨y, by rw [DFA.mem_accepts, DFA.eval, hy]; exact hp, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, hy, (rightDFA_evalFrom_some D _ _ _).2 ⟨y, rfl, rfl⟩⟩

/-- Forget the copy. -/
def unmark : T ⊕ T → List T :=
  Sum.elim (fun a => [a]) (fun a => [a])

theorem flatten_map_unmark_inl (x : List T) : ((x.map Sum.inl).map unmark).flatten = x := by
  induction x with
  | nil => rfl
  | cons a x ih => rw [List.map_cons, List.map_cons, List.flatten_cons, ih]; rfl

theorem flatten_map_unmark_inr (y : List T) : ((y.map Sum.inr).map unmark).flatten = y := by
  induction y with
  | nil => rfl
  | cons a y ih => rw [List.map_cons, List.map_cons, List.flatten_cons, ih]; rfl

theorem flatten_map_eraseRight_inl (x : List T) :
    ((x.map Sum.inl).map (eraseRight (T := T) (T' := T))).flatten = x := by
  induction x with
  | nil => rfl
  | cons a x ih => rw [List.map_cons, List.map_cons, List.flatten_cons, ih]; rfl

theorem flatten_map_eraseRight_inr (y : List T) :
    ((y.map Sum.inr).map (eraseRight (T := T) (T' := T))).flatten = [] := by
  induction y with
  | nil => rfl
  | cons a y ih => rw [List.map_cons, List.map_cons, List.flatten_cons, ih]; rfl

theorem image_eq (L R : Language T) :
    (fun u => (u.map eraseRight).flatten) ''
        ({u | (u.map unmark).flatten ∈ L} ⊓ (leftWords * rightWords R) : Language (T ⊕ T)) =
      rightQuotientLang L R := by
  ext x
  constructor
  · rintro ⟨u, ⟨hu, hK⟩, rfl⟩
    obtain ⟨l, ⟨x, rfl⟩, r, ⟨y, hy, rfl⟩, rfl⟩ := Language.mem_mul.1 hK
    refine ⟨y, hy, ?_⟩
    change ((x.map Sum.inl ++ y.map Sum.inr).map eraseRight).flatten ++ y ∈ L
    have hu' : ((x.map Sum.inl ++ y.map Sum.inr).map unmark).flatten ∈ L := hu
    rw [List.map_append, List.flatten_append, flatten_map_unmark_inl, flatten_map_unmark_inr]
      at hu'
    rw [List.map_append, List.flatten_append, flatten_map_eraseRight_inl,
      flatten_map_eraseRight_inr,
      List.append_nil]
    exact hu'
  · rintro ⟨y, hy, hxy⟩
    refine ⟨x.map Sum.inl ++ y.map Sum.inr, ⟨?_, Language.mem_mul.2
      ⟨_, ⟨x, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩⟩, ?_⟩
    · change ((x.map Sum.inl ++ y.map Sum.inr).map unmark).flatten ∈ L
      rw [List.map_append, List.flatten_append, flatten_map_unmark_inl, flatten_map_unmark_inr]
      exact hxy
    · change ((x.map Sum.inl ++ y.map Sum.inr).map eraseRight).flatten = x
      rw [List.map_append, List.flatten_append, flatten_map_eraseRight_inl,
        flatten_map_eraseRight_inr, List.append_nil]

end RightQuotientLang

/-- **The right quotient of a context-free language by a regular language is context-free**, over
a finite alphabet. -/
theorem IsContextFree.rightQuotientLang [Finite T] {L R : Language T} (hL : L.IsContextFree)
    (hR : R.IsRegular) : (Cslib.Language.rightQuotientLang L R).IsContextFree := by
  rw [← RightQuotientLang.image_eq]
  exact IsContextFree.homImage
    (IsContextFree.inf_isRegular (IsContextFree.preimage_hom hL RightQuotientLang.unmark)
      (IsRegular.mul RightQuotientLang.leftWords_isRegular
        (RightQuotientLang.rightWords_isRegular hR)))
    eraseRight

end Cslib.Language
