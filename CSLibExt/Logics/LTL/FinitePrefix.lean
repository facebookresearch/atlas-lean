/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.OmegaWord
import Cslib.Foundations.Data.OmegaSequence.Init

/-!
# Three-valued LTL semantics on finite prefixes

Source: Bauer, Leucker, and Schallhart, *Runtime Verification for LTL and TLTL*,
ACM TOSEM 20(4), Article 14 (2011), Definitions 2.4, 3.1, and 3.4.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.LTL.Word

/-- The possible verdicts when only a finite prefix of an infinite word is known. -/
inductive PrefixVerdict where
  | satisfied
  | violated
  | inconclusive
  deriving DecidableEq

variable {Atom Symbol : Type*}

/-- **Three-valued LTL semantics.** Over a nonempty alphabet, a finite prefix $u$ satisfies a
formula if every infinite continuation $w$ makes $uw$ satisfy it, violates the formula if no
continuation does, and is inconclusive otherwise. This is a semantic definition, not an
executable monitor. A nonempty alphabet ensures the first two cases are disjoint. -/
noncomputable def prefixVerdict [Nonempty Symbol] (valuation : Symbol → Atom → Prop)
    (u : List Symbol) (φ : Formula Atom) : PrefixVerdict := by
  classical
  exact if ∀ w : ωSequence Symbol, Satisfies valuation (u ++ω w) φ then .satisfied
    else if ∀ w : ωSequence Symbol, ¬ Satisfies valuation (u ++ω w) φ then .violated
    else .inconclusive

variable [Nonempty Symbol] {valuation : Symbol → Atom → Prop} {u v : List Symbol}
  {φ : Formula Atom}

/-- A satisfied verdict means the prefix forces truth. -/
theorem prefixVerdict_eq_satisfied_iff : prefixVerdict valuation u φ = .satisfied ↔
    ∀ w : ωSequence Symbol, Satisfies valuation (u ++ω w) φ := by
  classical
  by_cases hp : ∀ w : ωSequence Symbol, Satisfies valuation (u ++ω w) φ
  · rw [prefixVerdict, ite_eq_left hp]
    exact ⟨fun _ => hp, fun _ => rfl⟩
  · rw [prefixVerdict, ite_eq_right hp]
    by_cases hn : ∀ w : ωSequence Symbol, ¬ Satisfies valuation (u ++ω w) φ
    · rw [ite_eq_left hn]
      exact Iff.intro (fun h => nomatch h) (fun h => (hp h).elim)
    · rw [ite_eq_right hn]
      exact Iff.intro (fun h => nomatch h) (fun h => (hp h).elim)

/-- A violated verdict means the prefix forces falsity. -/
theorem prefixVerdict_eq_violated_iff : prefixVerdict valuation u φ = .violated ↔
    ∀ w : ωSequence Symbol, ¬ Satisfies valuation (u ++ω w) φ := by
  classical
  by_cases hp : ∀ w : ωSequence Symbol, Satisfies valuation (u ++ω w) φ
  · obtain ⟨a⟩ := ‹Nonempty Symbol›
    rw [prefixVerdict, ite_eq_left hp]
    exact Iff.intro (fun h => nomatch h)
      (fun hn => (hn (ωSequence.const a) (hp (ωSequence.const a))).elim)
  · rw [prefixVerdict, ite_eq_right hp]
    by_cases hn : ∀ w : ωSequence Symbol, ¬ Satisfies valuation (u ++ω w) φ
    · rw [ite_eq_left hn]
      exact ⟨fun _ => hn, fun _ => rfl⟩
    · rw [ite_eq_right hn]
      exact Iff.intro (fun h => nomatch h) (fun h => (hn h).elim)

/-- An inconclusive verdict means that both a satisfying and a violating continuation exist. -/
theorem prefixVerdict_eq_inconclusive_iff : prefixVerdict valuation u φ = .inconclusive ↔
    (∃ w : ωSequence Symbol, Satisfies valuation (u ++ω w) φ) ∧
      (∃ w : ωSequence Symbol, ¬ Satisfies valuation (u ++ω w) φ) := by
  classical
  constructor
  · intro h
    have hp : ¬ ∀ w : ωSequence Symbol, Satisfies valuation (u ++ω w) φ := by
      intro hall
      rw [prefixVerdict_eq_satisfied_iff.mpr hall] at h
      cases h
    have hn : ¬ ∀ w : ωSequence Symbol, ¬ Satisfies valuation (u ++ω w) φ := by
      intro hall
      rw [prefixVerdict_eq_violated_iff.mpr hall] at h
      cases h
    exact ⟨not_forall_not.mp hn, not_forall.mp hp⟩
  · rintro ⟨⟨wp, hp⟩, ⟨wn, hn⟩⟩
    have hpos : ¬ ∀ w : ωSequence Symbol, Satisfies valuation (u ++ω w) φ :=
      fun h => hn (h wn)
    have hneg : ¬ ∀ w : ωSequence Symbol, ¬ Satisfies valuation (u ++ω w) φ :=
      fun h => h wp hp
    simp [prefixVerdict, hpos, hneg]

/-- **Persistence of definite verdicts.** Reading any further finite word does not change
an already satisfied or violated verdict. -/
theorem prefixVerdict_append_of_definite
    (h : prefixVerdict valuation u φ ≠ .inconclusive) :
    prefixVerdict valuation (u ++ v) φ = prefixVerdict valuation u φ := by
  cases hv : prefixVerdict valuation u φ with
  | satisfied =>
      apply prefixVerdict_eq_satisfied_iff.mpr
      intro w
      rw [ωSequence.append_append_ωSequence]
      exact prefixVerdict_eq_satisfied_iff.mp hv (v ++ω w)
  | violated =>
      apply prefixVerdict_eq_violated_iff.mpr
      intro w
      rw [ωSequence.append_append_ωSequence]
      exact prefixVerdict_eq_violated_iff.mp hv (v ++ω w)
  | inconclusive => exact (h hv).elim

/-- **Monitorability.** A formula is monitorable if every finite prefix $u$ has some finite
extension $uv$ whose verdict is definite. It is not required that every infinite continuation
reach a definite verdict. -/
def Monitorable (valuation : Symbol → Atom → Prop) (φ : Formula Atom) : Prop :=
  ∀ u : List Symbol, ∃ v : List Symbol, prefixVerdict valuation (u ++ v) φ ≠ .inconclusive

end Cslib.LTL.Word
