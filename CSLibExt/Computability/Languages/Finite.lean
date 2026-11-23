/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Languages.RegularLanguage
public import Mathlib.Data.Set.Finite.List

/-!
# Finite languages are regular

Every finite language is regular, since singleton word languages are regular
(`IsRegular.singleton_word`) and regular languages are closed under union.
Over a finite alphabet this implies that bounded-length languages are regular
(`IsRegular.of_length_le`), via Mathlib's `List.finite_length_le`.

## Main results

* `Cslib.Language.IsRegular.singleton_word`: a language containing a single word is regular.
* `Cslib.Language.IsRegular.of_finite`: every finite language is regular.
* `Cslib.Language.IsRegular.of_length_le`: over a finite alphabet, a language whose words
  all have length at most `n` is regular.
-/

@[expose] public section

namespace Cslib.Language

variable {Symbol : Type*}

/-- **Single-word languages are regular.** For every word $w$ over any alphabet, the language
whose only word is $w$ is regular. -/
@[simp]
theorem IsRegular.singleton_word (w : List Symbol) : ({w} : Language Symbol).IsRegular := by
  induction w with
  | nil =>
    have h : ({[]} : Language Symbol) = 1 := by
      ext x
      simp only [Language.mem_singleton, Language.mem_one]
    rw [h]
    exact IsRegular.one
  | cons a w ih =>
    have h : ({a :: w} : Language Symbol) = {[a]} * {w} := by
      ext x
      simp only [Language.mem_singleton, Language.mem_mul]
      constructor
      · intro hx
        exact ⟨[a], rfl, w, rfl, by simp [hx]⟩
      · rintro ⟨y, rfl, z, rfl, h⟩
        exact h.symm
    rw [h]
    exact IsRegular.mul (IsRegular.char a) ih

/-- **Finite languages are regular.** Every finite language over any alphabet is regular. -/
theorem IsRegular.of_finite {l : Language Symbol} (h : Set.Finite l) : l.IsRegular := by
  refine Set.Finite.induction_on l h ?_ ?_
  · change (0 : Language Symbol).IsRegular
    exact IsRegular.zero
  · intro a s _ _ ih
    rw [Set.insert_eq]
    exact IsRegular.add (IsRegular.singleton_word a) ih

/-- **Languages of bounded word length are regular.** Over a finite alphabet, if every word of a
language $L$ has length at most $n$, for some natural number $n$, then $L$ is regular. -/
theorem IsRegular.of_length_le [Finite Symbol] {l : Language Symbol} (n : ℕ)
    (h : ∀ w ∈ l, w.length ≤ n) : l.IsRegular := by
  apply IsRegular.of_finite
  refine (List.finite_length_le Symbol n).subset ?_
  intro w hw
  exact h w hw

end Cslib.Language
