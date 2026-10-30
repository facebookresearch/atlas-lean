/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear temporal logic over ω-words
-/
module

public import CSLibExt.Logics.LTL.Syntax
public import Cslib.Computability.Languages.OmegaLanguage
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Linear temporal logic over ω-words

LTL formulas (`Cslib.LTL.Formula`) are interpreted over upstream ω-words
`w : Cslib.ωSequence Symbol` under an atom valuation `valuation : Symbol → Atom → Prop`.  Atoms
are read at the first letter, `next` moves to `w.tail`, and `until` quantifies over the suffixes
`w.drop k`.  The usual alphabet `Set Atom` (letters are sets of true atoms) is the valuation
`fun s a => a ∈ s`.

## Main definitions

* `Cslib.LTL.Word.Satisfies valuation w φ`: `φ` holds on `w`.
* `Cslib.LTL.Word.SatisfiesAt valuation w k φ`: `φ` holds at position `k` of `w`, that is, on
  the suffix `w.drop k`.
* `Cslib.LTL.Word.language valuation φ`: the ω-language of words satisfying `φ`.

## Main statements

* Semantics of the derived operators: `Satisfies.eventually_iff`, `Satisfies.always_iff`,
  `Satisfies.release_iff`, and their positional forms `satisfiesAt_eventually`,
  `satisfiesAt_always`.
* Suffixes: `satisfiesAt_drop` (position `j` of the suffix at `k` is position `k + j`), and
  `Satisfies.next_iff` / `Satisfies.until_iff` in terms of positions.
* Expansion laws: `Satisfies.until_expansion`, `Satisfies.release_expansion`,
  `Satisfies.eventually_expansion`, `Satisfies.always_expansion`.
* Duality: `Satisfies.not_next`, `Satisfies.not_until`, `Satisfies.not_release`,
  `Satisfies.not_eventually`, `Satisfies.not_always`.
* `Satisfies.always_eventually_iff` and `Satisfies.eventually_always_iff`: `G F φ` and `F G φ`
  are `∃ᶠ` and `∀ᶠ` along `atTop`.
* `satisfies_map`: relabelling the letters of a word is composing the valuation.
* Boolean structure of `language`: `language_not`, `language_and`, `language_or`.

The semantics does not use the local LTS core. A run-based semantics over state sequences,
and a proof that it agrees with this ω-word semantics, are future work.
-/

@[expose] public section

namespace Cslib
namespace LTL
namespace Word

open Filter

variable {Atom Symbol : Type*}

/-- Satisfaction of an LTL formula on an ω-word under a valuation of atoms on letters.  The
temporal operators recurse on suffixes of the word. -/
def Satisfies (valuation : Symbol → Atom → Prop) (w : ωSequence Symbol) :
    Formula Atom → Prop
  | .atom a => valuation (w 0) a
  | .top => True
  | .not φ => ¬ Satisfies valuation w φ
  | .and φ ψ => Satisfies valuation w φ ∧ Satisfies valuation w ψ
  | .next φ => Satisfies valuation w.tail φ
  | .until φ ψ =>
      ∃ k, Satisfies valuation (w.drop k) ψ ∧ ∀ j < k, Satisfies valuation (w.drop j) φ

/-- Satisfaction at position `k` of an ω-word: satisfaction on the suffix starting at `k`. -/
def SatisfiesAt (valuation : Symbol → Atom → Prop) (w : ωSequence Symbol) (k : ℕ)
    (φ : Formula Atom) : Prop :=
  Satisfies valuation (w.drop k) φ

/-- The ω-language of an LTL formula: the words satisfying it. -/
def language (valuation : Symbol → Atom → Prop) (φ : Formula Atom) : ωLanguage Symbol :=
  { w : ωSequence Symbol | Satisfies valuation w φ }

variable {valuation : Symbol → Atom → Prop} {w : ωSequence Symbol} {φ ψ : Formula Atom}
  {a : Atom}

/-! ### Positions and suffixes -/

@[simp]
theorem satisfiesAt_zero : SatisfiesAt valuation w 0 φ ↔ Satisfies valuation w φ :=
  Iff.rfl

/-- Satisfaction is well defined on suffixes: position `j` of the suffix at `k` is position
`k + j` of the word. -/
theorem satisfiesAt_drop {k j : ℕ} :
    SatisfiesAt valuation (w.drop k) j φ ↔ SatisfiesAt valuation w (k + j) φ := by
  rw [SatisfiesAt, SatisfiesAt, ωSequence.drop_drop]

theorem satisfies_drop {k : ℕ} :
    Satisfies valuation (w.drop k) φ ↔ SatisfiesAt valuation w k φ :=
  Iff.rfl

theorem satisfies_tail : Satisfies valuation w.tail φ ↔ SatisfiesAt valuation w 1 φ :=
  Iff.rfl

namespace Satisfies

/-! ### Primitive connectives -/

theorem atom_iff : Satisfies valuation w (.atom a) ↔ valuation (w 0) a :=
  Iff.rfl

theorem top_iff : Satisfies valuation w (.top : Formula Atom) ↔ True :=
  Iff.rfl

theorem not_iff : Satisfies valuation w (.not φ) ↔ ¬ Satisfies valuation w φ :=
  Iff.rfl

theorem and_iff :
    Satisfies valuation w (.and φ ψ) ↔ Satisfies valuation w φ ∧ Satisfies valuation w ψ :=
  Iff.rfl

theorem next_iff : Satisfies valuation w (.next φ) ↔ SatisfiesAt valuation w 1 φ :=
  Iff.rfl

theorem until_iff :
    Satisfies valuation w (.until φ ψ) ↔
      ∃ k, SatisfiesAt valuation w k ψ ∧ ∀ j < k, SatisfiesAt valuation w j φ :=
  Iff.rfl

/-! ### Derived propositional connectives -/

theorem bot_iff : Satisfies valuation w (Formula.bot : Formula Atom) ↔ False := by
  simp [Formula.bot, Satisfies]

theorem or_iff :
    Satisfies valuation w (Formula.or φ ψ) ↔ Satisfies valuation w φ ∨ Satisfies valuation w ψ := by
  simp only [Formula.or, Satisfies]
  tauto

theorem imp_iff :
    Satisfies valuation w (Formula.imp φ ψ) ↔
      (Satisfies valuation w φ → Satisfies valuation w ψ) := by
  rw [Formula.imp, or_iff, not_iff]
  tauto

theorem iff_iff :
    Satisfies valuation w (Formula.iff φ ψ) ↔
      (Satisfies valuation w φ ↔ Satisfies valuation w ψ) := by
  rw [Formula.iff, and_iff, imp_iff, imp_iff]
  tauto

/-! ### Derived temporal operators -/

theorem eventually_iff :
    Satisfies valuation w (Formula.eventually φ) ↔ ∃ k, SatisfiesAt valuation w k φ := by
  simp [Formula.eventually, until_iff, SatisfiesAt, Satisfies]

theorem always_iff :
    Satisfies valuation w (Formula.always φ) ↔ ∀ k, SatisfiesAt valuation w k φ := by
  rw [Formula.always, not_iff, eventually_iff]
  simp [SatisfiesAt, Satisfies]

/-- `φ R ψ`: at every position `ψ` holds, unless `φ` already held at an earlier position. -/
theorem release_iff :
    Satisfies valuation w (Formula.release φ ψ) ↔
      ∀ k, SatisfiesAt valuation w k ψ ∨ ∃ j < k, SatisfiesAt valuation w j φ := by
  rw [Formula.release, not_iff, until_iff]
  simp only [SatisfiesAt, Satisfies, not_exists, not_and, not_forall, not_not]
  refine forall_congr' fun k => ?_
  tauto

/-! ### Duality -/

/-- `next` is self-dual on ω-words. -/
theorem not_next :
    Satisfies valuation w (.not (.next φ)) ↔ Satisfies valuation w (.next (.not φ)) :=
  Iff.rfl

theorem not_until :
    Satisfies valuation w (.not (.until φ ψ)) ↔
      Satisfies valuation w (Formula.release (.not φ) (.not ψ)) := by
  simp only [Formula.release, Satisfies, not_not]

theorem not_release :
    Satisfies valuation w (.not (Formula.release φ ψ)) ↔
      Satisfies valuation w (.until (.not φ) (.not ψ)) := by
  simp only [Formula.release, Satisfies, not_not]

theorem not_eventually :
    Satisfies valuation w (.not (Formula.eventually φ)) ↔
      Satisfies valuation w (Formula.always (.not φ)) := by
  rw [not_iff, eventually_iff, always_iff]
  simp [SatisfiesAt, Satisfies]

theorem not_always :
    Satisfies valuation w (.not (Formula.always φ)) ↔
      Satisfies valuation w (Formula.eventually (.not φ)) := by
  rw [not_iff, always_iff, eventually_iff]
  simp [SatisfiesAt, Satisfies]

/-! ### Expansion laws -/

/-- The expansion law for `until`: either the target holds now, or the guard holds now and the
`until` is postponed by one step. -/
theorem until_expansion :
    Satisfies valuation w (.until φ ψ) ↔
      Satisfies valuation w ψ ∨
        (Satisfies valuation w φ ∧ Satisfies valuation w (.next (.until φ ψ))) := by
  rw [next_iff, SatisfiesAt, until_iff, until_iff]
  simp only [satisfiesAt_drop]
  constructor
  · rintro ⟨k, hψ, hφ⟩
    cases k with
    | zero => exact Or.inl hψ
    | succ k =>
        refine Or.inr ⟨hφ 0 (Nat.zero_lt_succ k), k, ?_, fun j hj => ?_⟩
        · rwa [Nat.add_comm]
        · rw [Nat.add_comm]
          exact hφ (j + 1) (by omega)
  · rintro (hψ | ⟨hφ, k, hψ, hφs⟩)
    · exact ⟨0, hψ, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · refine ⟨k + 1, by rwa [Nat.add_comm], fun j hj => ?_⟩
      cases j with
      | zero => exact hφ
      | succ j =>
          rw [Nat.add_comm]
          exact hφs j (by omega)

/-- The expansion law for `release`: the second argument holds now, and either the first
argument holds now or the `release` is postponed by one step. -/
theorem release_expansion :
    Satisfies valuation w (Formula.release φ ψ) ↔
      Satisfies valuation w ψ ∧
        (Satisfies valuation w φ ∨ Satisfies valuation w (.next (Formula.release φ ψ))) := by
  rw [Formula.release, not_iff, until_expansion]
  simp only [Satisfies]
  exact (fun A B C : Prop => by tauto : ∀ A B C : Prop, ¬(¬B ∨ ¬A ∧ C) ↔ B ∧ (A ∨ ¬C)) _ _ _

theorem eventually_expansion :
    Satisfies valuation w (Formula.eventually φ) ↔
      Satisfies valuation w φ ∨ Satisfies valuation w (.next (Formula.eventually φ)) := by
  rw [Formula.eventually, until_expansion]
  simp [Satisfies]

theorem always_expansion :
    Satisfies valuation w (Formula.always φ) ↔
      Satisfies valuation w φ ∧ Satisfies valuation w (.next (Formula.always φ)) := by
  rw [Formula.always, not_iff, eventually_expansion]
  simp only [Satisfies]
  tauto

/-! ### Idempotence and recurrence -/

theorem always_always :
    Satisfies valuation w (Formula.always (Formula.always φ)) ↔
      Satisfies valuation w (Formula.always φ) := by
  simp only [always_iff, SatisfiesAt, ωSequence.drop_drop]
  exact ⟨fun h k => by simpa using h 0 k, fun h k j => h (k + j)⟩

theorem eventually_eventually :
    Satisfies valuation w (Formula.eventually (Formula.eventually φ)) ↔
      Satisfies valuation w (Formula.eventually φ) := by
  simp only [eventually_iff, SatisfiesAt, ωSequence.drop_drop]
  exact ⟨fun ⟨k, j, h⟩ => ⟨k + j, h⟩, fun ⟨k, h⟩ => ⟨0, k, by simpa using h⟩⟩

/-- `G F φ`: `φ` holds at infinitely many positions. -/
theorem always_eventually_iff :
    Satisfies valuation w (Formula.always (Formula.eventually φ)) ↔
      ∃ᶠ k in atTop, SatisfiesAt valuation w k φ := by
  simp only [always_iff, Filter.frequently_atTop]
  refine forall_congr' fun k => ?_
  rw [SatisfiesAt, eventually_iff]
  simp only [satisfiesAt_drop]
  exact ⟨fun ⟨j, h⟩ => ⟨k + j, by omega, h⟩,
    fun ⟨m, hm, h⟩ => ⟨m - k, by rwa [Nat.add_sub_cancel' hm]⟩⟩

/-- `F G φ`: `φ` holds at all but finitely many positions. -/
theorem eventually_always_iff :
    Satisfies valuation w (Formula.eventually (Formula.always φ)) ↔
      ∀ᶠ k in atTop, SatisfiesAt valuation w k φ := by
  simp only [eventually_iff, Filter.eventually_atTop]
  refine exists_congr fun k => ?_
  rw [SatisfiesAt, always_iff]
  simp only [satisfiesAt_drop]
  exact ⟨fun h m hm => by simpa [Nat.add_sub_cancel' hm] using h (m - k),
    fun h j => h (k + j) (by omega)⟩

end Satisfies

/-! ### Positional forms -/

theorem satisfiesAt_atom {k : ℕ} : SatisfiesAt valuation w k (.atom a) ↔ valuation (w k) a := by
  simp [SatisfiesAt, Satisfies]

theorem satisfiesAt_next {k : ℕ} :
    SatisfiesAt valuation w k (.next φ) ↔ SatisfiesAt valuation w (k + 1) φ :=
  satisfiesAt_drop

theorem satisfiesAt_always {k : ℕ} :
    SatisfiesAt valuation w k (Formula.always φ) ↔ ∀ j, SatisfiesAt valuation w (k + j) φ := by
  rw [SatisfiesAt, Satisfies.always_iff]
  exact forall_congr' fun _ => satisfiesAt_drop

theorem satisfiesAt_eventually {k : ℕ} :
    SatisfiesAt valuation w k (Formula.eventually φ) ↔
      ∃ j, SatisfiesAt valuation w (k + j) φ := by
  rw [SatisfiesAt, Satisfies.eventually_iff]
  exact exists_congr fun _ => satisfiesAt_drop

/-! ### Relabelling letters -/

/-- Satisfaction on a relabelled word is satisfaction under the composed valuation. -/
theorem satisfies_map {Symbol' : Type*} (f : Symbol' → Symbol) :
    ∀ (φ : Formula Atom) (w : ωSequence Symbol'),
      Satisfies valuation (w.map f) φ ↔ Satisfies (fun s a => valuation (f s) a) w φ
  | .atom _, _ => Iff.rfl
  | .top, _ => Iff.rfl
  | .not φ, w => not_congr (satisfies_map f φ w)
  | .and φ ψ, w => and_congr (satisfies_map f φ w) (satisfies_map f ψ w)
  | .next φ, w => by
      change Satisfies valuation (w.map f).tail φ ↔ _
      rw [ωSequence.tail_map]
      exact satisfies_map f φ w.tail
  | .until φ ψ, w => by
      change (∃ k, Satisfies valuation ((w.map f).drop k) ψ ∧
          ∀ j < k, Satisfies valuation ((w.map f).drop j) φ) ↔ _
      simp only [ωSequence.drop_map, satisfies_map f φ, satisfies_map f ψ]
      rfl

/-! ### Languages -/

@[simp]
theorem mem_language : w ∈ language valuation φ ↔ Satisfies valuation w φ :=
  Iff.rfl

theorem language_not : language valuation (.not φ) = (language valuation φ)ᶜ := by
  refine ωLanguage.mem_ext fun w => ?_
  rw [ωLanguage.mem_compl]
  exact Iff.rfl

theorem language_and :
    language valuation (.and φ ψ) = language valuation φ ⊓ language valuation ψ := by
  refine ωLanguage.mem_ext fun w => ?_
  rw [ωLanguage.mem_inf]
  exact Iff.rfl

theorem language_or :
    language valuation (Formula.or φ ψ) = language valuation φ ⊔ language valuation ψ := by
  refine ωLanguage.mem_ext fun w => ?_
  rw [ωLanguage.mem_sup]
  exact Satisfies.or_iff

end Word
end LTL
end Cslib
