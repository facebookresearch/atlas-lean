/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.NonClosure
public import CSLibExt.Computability.Languages.ContextFree.Ambiguity

/-!
# The canonical inherently ambiguous context-free language

The language `{a ^ i b ^ j c ^ k | i = j or j = k}` over a three-letter alphabet is the
standard example of an inherently ambiguous context-free language: it is context-free, as
the union of the context-free languages `{a ^ n b ^ n c ^ *}` and `{a ^ * b ^ n c ^ n}`,
but every context-free grammar generating it is ambiguous. The context-free half is proved
here. The inherent-ambiguity half, which needs the derivation-tree pumping argument (any
grammar for the language must give two different parse trees to some word of the form
`a ^ n b ^ n c ^ n`), is not proved here.

## Main results

* `Cslib.Language.inherentlyAmbiguousLang`: the language
  `{a ^ i b ^ j c ^ k | i = j or j = k}` over `Fin 3`.
* `Cslib.Language.IsInherentlyAmbiguous`: a language is inherently ambiguous when it is
  context-free and every grammar generating it is ambiguous.
* `Cslib.Language.inherentlyAmbiguousLang_isContextFree`: the example language is
  context-free.
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*}

/-- The language `{a ^ i b ^ j c ^ k | i = j or j = k}` over the alphabet `Fin 3`
(`0, 1, 2` for `a, b, c`): the standard inherently ambiguous context-free language.
Source: S. Ginsburg, The Mathematical Theory of Context-Free Languages, McGraw-Hill, 1966;
J. E. Hopcroft and J. D. Ullman, Introduction to Automata Theory, Languages, and
Computation, Addison-Wesley, 1979, Chapter 7. -/
def inherentlyAmbiguousLang : Language (Fin 3) :=
  {w | ∃ i j k, (i = j ∨ j = k) ∧
    w = List.replicate i 0 ++ List.replicate j 1 ++ List.replicate k 2}

/-- A language is inherently ambiguous when it is context-free and every grammar
generating it is ambiguous. -/
def IsInherentlyAmbiguous (L : Language T) : Prop :=
  L.IsContextFree ∧ ∀ g : ContextFreeGrammar T, g.language = L → IsAmbiguous g

/-- The example language is the union of `a ^ n b ^ n c ^ *` and `a ^ * b ^ n c ^ n`. -/
theorem inherentlyAmbiguousLang_eq :
    inherentlyAmbiguousLang =
      eqPowLang (0 : Fin 3) 1 * KStar.kstar ({[(2 : Fin 3)]} : Language (Fin 3)) +
        (KStar.kstar ({[(0 : Fin 3)]} : Language (Fin 3)) * eqPowLang (1 : Fin 3) 2) := by
  ext w
  constructor
  · rintro ⟨i, j, k, hijk, rfl⟩
    rcases hijk with rfl | rfl
    · rw [Language.mem_add]
      left
      rw [Language.mem_mul]
      exact ⟨List.replicate i 0 ++ List.replicate i 1, ⟨i, rfl⟩,
        List.replicate k 2, mem_kstar_singleton.mpr ⟨k, rfl⟩, rfl⟩
    · rw [Language.mem_add]
      right
      rw [Language.mem_mul]
      exact ⟨List.replicate i 0, mem_kstar_singleton.mpr ⟨i, rfl⟩,
        List.replicate j 1 ++ List.replicate j 2, ⟨j, rfl⟩,
        (List.append_assoc _ _ _).symm⟩
  · intro h
    rw [Language.mem_add] at h
    rcases h with h | h
    · obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Language.mem_mul.mp h
      obtain ⟨n, rfl⟩ : ∃ n, w₁ = List.replicate n 0 ++ List.replicate n 1 := hw₁
      obtain ⟨k, rfl⟩ := mem_kstar_singleton.mp hw₂
      exact ⟨n, n, k, Or.inl rfl, rfl⟩
    · obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Language.mem_mul.mp h
      obtain ⟨i, rfl⟩ := mem_kstar_singleton.mp hw₁
      obtain ⟨n, rfl⟩ : ∃ n, w₂ = List.replicate n 1 ++ List.replicate n 2 := hw₂
      exact ⟨i, n, n, Or.inr rfl, (List.append_assoc _ _ _).symm⟩

/-- **The example language is context-free.** -/
theorem inherentlyAmbiguousLang_isContextFree : inherentlyAmbiguousLang.IsContextFree := by
  rw [inherentlyAmbiguousLang_eq]
  exact IsContextFree.add
    (IsContextFree.mul (eqPowLang_isContextFree _ _)
      (IsContextFree.kstar (IsContextFree.singleton_word _)))
    (IsContextFree.mul (IsContextFree.kstar (IsContextFree.singleton_word _))
      (eqPowLang_isContextFree _ _))

end Cslib.Language
