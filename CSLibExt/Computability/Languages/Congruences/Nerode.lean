/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import Mathlib.Computability.MyhillNerode

/-!
# Nerode equivalence and the canonical quotient automaton

This file develops the word-equivalence formulation of the Myhill--Nerode theorem. Two words are
equivalent when no continuation distinguishes their membership in the language. The equivalence is
stable under appending a common continuation, so its quotient carries a canonical deterministic
automaton.

Mathlib's `Language.toDFA` uses left quotients directly as states. Here we expose the corresponding
quotient of words, prove it equivalent to the range of left quotients, and construct the canonical
automaton on equivalence classes.

## Main definitions

* `Cslib.Language.nerodeRel`: indistinguishability by continuations.
* `Cslib.Language.nerodeSetoid`: the induced equivalence relation on words.
* `Cslib.Language.NerodeClass`: equivalence classes of words.
* `Cslib.Language.nerodeDFA`: the canonical DFA on Nerode classes.

## Main results

* `nerodeRel_iff`: the continuation characterization.
* `nerodeRel_append_right`: Nerode equivalence is a right congruence.
* `nerodeClassEquivResidual`: classes are equivalent to reachable left quotients.
* `accepts_nerodeDFA`: the canonical quotient automaton recognizes the original language.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u

variable {Symbol : Type u} {L : Language Symbol}

/-- Two words are Nerode equivalent for `L` when they have the same left quotient. -/
def nerodeRel (L : Language Symbol) (x y : List Symbol) : Prop :=
  L.leftQuotient x = L.leftQuotient y

@[refl]
theorem nerodeRel_refl (L : Language Symbol) (x : List Symbol) : nerodeRel L x x :=
  rfl

@[symm]
theorem nerodeRel_symm {x y : List Symbol} (h : nerodeRel L x y) : nerodeRel L y x :=
  h.symm

@[trans]
theorem nerodeRel_trans {x y z : List Symbol} (hxy : nerodeRel L x y)
    (hyz : nerodeRel L y z) : nerodeRel L x z :=
  hxy.trans hyz

/-- The Setoid of Nerode equivalence classes. -/
def nerodeSetoid (L : Language Symbol) : Setoid (List Symbol) where
  r := nerodeRel L
  iseqv := ⟨nerodeRel_refl L, nerodeRel_symm, nerodeRel_trans⟩

/-- The quotient of words by Nerode equivalence. -/
abbrev NerodeClass (L : Language Symbol) := Quotient (nerodeSetoid L)

/-- Nerode equivalence means that every continuation gives the same membership answer. -/
theorem nerodeRel_iff {x y : List Symbol} :
    nerodeRel L x y ↔ ∀ z, x ++ z ∈ L ↔ y ++ z ∈ L := by
  constructor
  · intro h z
    exact Set.ext_iff.mp h z
  · intro h
    exact Set.ext fun z ↦ h z

/-- Equivalent words themselves have the same membership status. -/
theorem nerodeRel.mem_iff {x y : List Symbol} (h : nerodeRel L x y) : x ∈ L ↔ y ∈ L := by
  simpa using (nerodeRel_iff.mp h [])

/-- Appending the same continuation preserves Nerode equivalence. -/
theorem nerodeRel_append_right {x y : List Symbol} (h : nerodeRel L x y)
    (z : List Symbol) : nerodeRel L (x ++ z) (y ++ z) := by
  unfold nerodeRel at h ⊢
  rw [L.leftQuotient_append, L.leftQuotient_append, h]

/-- Appending one common symbol preserves Nerode equivalence. -/
theorem nerodeRel_append_singleton {x y : List Symbol} (h : nerodeRel L x y)
    (a : Symbol) : nerodeRel L (x ++ [a]) (y ++ [a]) :=
  nerodeRel_append_right h [a]

/-- Every word is equivalent to itself with the empty continuation appended. -/
@[simp]
theorem nerodeRel_append_nil (x : List Symbol) : nerodeRel L (x ++ []) x := by
  simpa using nerodeRel_refl L x

/-- The Nerode class represented by a word. -/
def nerodeClass (L : Language Symbol) (x : List Symbol) : NerodeClass L :=
  Quotient.mk (nerodeSetoid L) x

@[simp]
theorem nerodeClass_eq_iff {x y : List Symbol} :
    nerodeClass L x = nerodeClass L y ↔ nerodeRel L x y := by
  exact Quotient.eq

/-- Send a Nerode class to its well-defined residual language. -/
def classResidual (L : Language Symbol) : NerodeClass L → Set.range L.leftQuotient :=
  Quotient.lift
    (fun x ↦ ⟨L.leftQuotient x, ⟨x, rfl⟩⟩)
    (fun _ _ h ↦ Subtype.ext h)

@[simp]
theorem classResidual_nerodeClass (x : List Symbol) :
    classResidual L (nerodeClass L x) = ⟨L.leftQuotient x, ⟨x, rfl⟩⟩ :=
  rfl

theorem classResidual_injective : Function.Injective (classResidual L) := by
  intro p q h
  induction p using Quotient.inductionOn with
  | _ x =>
    induction q using Quotient.inductionOn with
    | _ y =>
      apply (nerodeClass_eq_iff (L := L)).mpr
      exact Subtype.ext_iff.mp h

theorem classResidual_surjective : Function.Surjective (classResidual L) := by
  rintro ⟨R, x, rfl⟩
  exact ⟨nerodeClass L x, rfl⟩

/-- Nerode classes are precisely the residual languages reachable by left quotients. -/
noncomputable def nerodeClassEquivResidual (L : Language Symbol) :
    NerodeClass L ≃ Set.range L.leftQuotient :=
  Equiv.ofBijective (classResidual L) ⟨classResidual_injective, classResidual_surjective⟩

/-- Append a symbol to a Nerode class. -/
def NerodeClass.step (a : Symbol) : NerodeClass L → NerodeClass L :=
  Quotient.map (· ++ [a]) (fun _ _ h ↦ nerodeRel_append_singleton h a)

@[simp]
theorem NerodeClass.step_nerodeClass (x : List Symbol) (a : Symbol) :
    NerodeClass.step (L := L) a (nerodeClass L x) = nerodeClass L (x ++ [a]) :=
  rfl

/-- Whether a Nerode class is accepting. This is well-defined because equivalent words have equal
membership in `L`. -/
def NerodeClass.Accepting (L : Language Symbol) : Set (NerodeClass L) :=
  {q | Quotient.lift (s := nerodeSetoid L) (fun x ↦ x ∈ L)
    (fun _ _ h ↦ propext (nerodeRel.mem_iff h)) q}

@[simp]
theorem nerodeClass_mem_accepting (x : List Symbol) :
    nerodeClass L x ∈ NerodeClass.Accepting L ↔ x ∈ L :=
  Iff.rfl

/-- The canonical deterministic automaton whose states are Nerode classes. -/
def nerodeDFA (L : Language Symbol) : DFA Symbol (NerodeClass L) where
  step q a := q.step a
  start := nerodeClass L []
  accept := NerodeClass.Accepting L

@[simp]
theorem nerodeDFA_start : (nerodeDFA L).start = nerodeClass L [] :=
  rfl

@[simp]
theorem nerodeDFA_step (q : NerodeClass L) (a : Symbol) :
    (nerodeDFA L).step q a = q.step a :=
  rfl

theorem nerodeDFA_evalFrom_class (x y : List Symbol) :
    (nerodeDFA L).evalFrom (nerodeClass L x) y = nerodeClass L (x ++ y) := by
  induction y using List.reverseRecOn with
  | nil => simp
  | append_singleton y a ih =>
      simp only [DFA.evalFrom_append_singleton, nerodeDFA_step,
        NerodeClass.step_nerodeClass, ih, List.append_assoc]

@[simp]
theorem nerodeDFA_eval (x : List Symbol) :
    (nerodeDFA L).eval x = nerodeClass L x := by
  simpa [DFA.eval] using nerodeDFA_evalFrom_class (L := L) [] x

/-- The canonical Nerode automaton recognizes exactly `L`. -/
@[simp]
theorem accepts_nerodeDFA : (nerodeDFA L).accepts = L := by
  ext x
  rw [DFA.mem_accepts, nerodeDFA_eval]
  exact nerodeClass_mem_accepting x

/-- Every state of the canonical Nerode automaton is reachable. -/
theorem nerodeDFA_state_reachable (q : NerodeClass L) :
    ∃ x, (nerodeDFA L).eval x = q := by
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨x, nerodeDFA_eval (L := L) x⟩

/-- Finiteness of Nerode classes is the quotient formulation of the Myhill--Nerode criterion. -/
theorem finite_nerodeClass_iff : Finite (NerodeClass L) ↔ (Set.range L.leftQuotient).Finite := by
  constructor
  · intro h
    let _ : Finite (NerodeClass L) := h
    let _ : Finite (Set.range L.leftQuotient) :=
      Finite.of_equiv (NerodeClass L) (nerodeClassEquivResidual L)
    exact Set.toFinite _
  · intro h
    let _ := @Fintype.ofFinite (Set.range L.leftQuotient) h
    exact Finite.of_injective (nerodeClassEquivResidual L) (nerodeClassEquivResidual L).injective

/-- Quotient formulation of the Myhill--Nerode theorem. -/
theorem isRegular_iff_finite_nerodeClass : L.IsRegular ↔ Finite (NerodeClass L) := by
  rw [Language.isRegular_iff_finite_range_leftQuotient, finite_nerodeClass_iff]

end Cslib.Language
