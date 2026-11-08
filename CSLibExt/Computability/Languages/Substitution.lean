/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Substitution of languages for letters
-/
module

public import Mathlib.Computability.Language

/-!
# Substitution of languages for letters

A substitution replaces each letter `a` of a word by any word of a language `s a`:
`substitution L s` consists of the words `y₁ ⋯ yₙ` with `a₁ ⋯ aₙ ∈ L` and `yᵢ ∈ s aᵢ`, that is
`y ∈ (x.map s).prod` for some `x ∈ L`. Closure results: `IsContextFree.substitution`
(`ContextFree/Substitution.lean`) and `IsRegular.substitution` (`RegularSubstitution.lean`).
-/

@[expose] public section

namespace Cslib.Language

variable {T T' : Type*}

/-- The substitution of languages for letters: replace each letter `a` of a word of `L` by some
word of `s a`. -/
def substitution (L : Language T) (s : T → Language T') : Language T' :=
  {y | ∃ x ∈ L, y ∈ (x.map s).prod}

theorem mem_substitution {L : Language T} {s : T → Language T'} {y : List T'} :
    y ∈ substitution L s ↔ ∃ x ∈ L, y ∈ (x.map s).prod :=
  Iff.rfl

theorem substitution_mono {L M : Language T} (h : L ≤ M) (s : T → Language T') :
    substitution L s ≤ substitution M s :=
  fun _ ⟨x, hx, hy⟩ => ⟨x, h hx, hy⟩

theorem substitution_mul (L M : Language T) (s : T → Language T') :
    substitution (L * M) s = substitution L s * substitution M s := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Language.mem_mul.1 hx
    rw [List.map_append, List.prod_append] at hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Language.mem_mul.1 hy
    exact Language.mem_mul.2 ⟨y₁, ⟨x₁, hx₁, hy₁⟩, y₂, ⟨x₂, hx₂, hy₂⟩, rfl⟩
  · intro hy
    obtain ⟨y₁, ⟨x₁, hx₁, hy₁⟩, y₂, ⟨x₂, hx₂, hy₂⟩, rfl⟩ := Language.mem_mul.1 hy
    refine ⟨x₁ ++ x₂, Language.mem_mul.2 ⟨x₁, hx₁, x₂, hx₂, rfl⟩, ?_⟩
    rw [List.map_append, List.prod_append]
    exact Language.mem_mul.2 ⟨y₁, hy₁, y₂, hy₂, rfl⟩

theorem substitution_one (s : T → Language T') : substitution (1 : Language T) s = 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    rw [Language.mem_one] at hx
    subst hx
    exact hy
  · intro hy
    exact ⟨[], (Language.mem_one _).2 rfl, hy⟩

theorem substitution_letter (a : T) (s : T → Language T') :
    substitution ({[a]} : Language T) s = s a := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    rw [Set.mem_singleton_iff.1 hx] at hy
    simpa using hy
  · intro hy
    exact ⟨[a], rfl, by simpa using hy⟩

end Cslib.Language
