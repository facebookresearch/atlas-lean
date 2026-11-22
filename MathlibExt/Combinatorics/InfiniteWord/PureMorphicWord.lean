/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.List.Basic

/-!
Pure morphic words after Huova and Durand.

Concept `jis_sem_817d955b6393d48d72476d2d` with source statements
`jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`.
Finite words are modelled by `List A`; infinite words by `Nat → A`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The extension of a letter map to finite words by concatenation: every
letter of the input word is replaced by its image and the images are joined
in order (concept `jis_sem_817d955b6393d48d72476d2d`, clause `word_morphism`;
statements `jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`). -/
public def morphExtend {A : Type*} (f : A → List A) (w : List A) : List A :=
  w.flatMap f

/-- Finite iterates of the extended letter map applied to a finite word, with
the zeroth iterate the identity (concept `jis_sem_817d955b6393d48d72476d2d`,
clause `word_morphism`; statements `jis_59581da9ed7395999b79fb6c`,
`jis_686fde4820b8be0b1543930a`, `jis_83acfc0f995c923dbbbed9e5`,
`jis_95467c21193bf40b4aae1281`, `jis_e5dacb15b7f36a3e2d33683c`,
`jis_f0ae0eecd29e48e7e5a45717`). -/
public def morphIterate {A : Type*} (f : A → List A) : Nat → List A → List A
  | 0, w => w
  | n + 1, w => morphExtend f (morphIterate f n w)

/-- The extended letter map preserves concatenation of finite words (concept
`jis_sem_817d955b6393d48d72476d2d`, clause `word_morphism`; statements
`jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`). -/
public theorem morphExtend_append {A : Type*} (f : A → List A) (u v : List A) :
    morphExtend f (u ++ v) = morphExtend f u ++ morphExtend f v := by
  induction u with
  | nil => rfl
  | cons b bs hb =>
    have e1 : morphExtend f ((b :: bs) ++ v)
        = f b ++ morphExtend f (bs ++ v) := rfl
    have e2 : morphExtend f (b :: bs)
        = f b ++ morphExtend f bs := rfl
    rw [e1, e2, hb, List.append_assoc]

/-- Iterating a letter map whose images all have length `k` multiplies word length by `k`
at each step. -/
public theorem morphIterate_length_of_uniform {A : Type*} {k : Nat} {f : A → List A}
    (hlen : ∀ x, (f x).length = k) (n : Nat) (w : List A) :
    (morphIterate f n w).length = k ^ n * w.length := by
  have hext : ∀ v : List A, (morphExtend f v).length = k * v.length := by
    intro v
    induction v with
    | nil => rfl
    | cons x xs ih =>
      change (f x ++ morphExtend f xs).length = _
      rw [List.length_append, ih, hlen, List.length_cons, Nat.mul_succ, Nat.add_comm]
  induction n with
  | zero => simp [morphIterate]
  | succ n ih =>
    rw [morphIterate, hext, ih, Nat.pow_succ]
    ac_rfl

/-- A letter map is non-erasing when every letter image is a nonempty finite
word (concept `jis_sem_817d955b6393d48d72476d2d`, clause `non_erasing`;
statements `jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`). -/
public def IsNonErasing {A : Type*} (f : A → List A) : Prop :=
  ∀ a : A, f a ≠ []

/-- A letter map is prefix-preserving (prolongable) at a letter when its image
starts with that letter and every iterate of the remaining suffix stays
nonempty (concept `jis_sem_817d955b6393d48d72476d2d`, clause
`prefix_preserving`; statements `jis_59581da9ed7395999b79fb6c`,
`jis_686fde4820b8be0b1543930a`, `jis_83acfc0f995c923dbbbed9e5`,
`jis_95467c21193bf40b4aae1281`, `jis_e5dacb15b7f36a3e2d33683c`,
`jis_f0ae0eecd29e48e7e5a45717`). -/
public def IsPrefixPreserving {A : Type*} (f : A → List A) (a : A) : Prop :=
  ∃ α : List A, f a = a :: α ∧ ∀ n : Nat, morphIterate f n α ≠ []

/-- The infinite word is the limit of the finite iterates at a letter: the
lengths of the iterates are unbounded and every position defined by an
iterate carries the same letter as the infinite word (concept
`jis_sem_817d955b6393d48d72476d2d`, clause `omega_limit`; statements
`jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`). -/
public def IsOmegaLimit {A : Type*} (f : A → List A) (a : A) (w : Nat → A) : Prop :=
  (∀ M : Nat, ∃ n : Nat, M ≤ (morphIterate f n [a]).length) ∧
    ∀ n : Nat, ∀ i : Nat, ∀ h : i < (morphIterate f n [a]).length,
      GetElem.getElem (morphIterate f n [a]) i h = w i

/-- An infinite word over a finite alphabet is pure morphic when some
prolongable letter map generates it as such an infinite limit, with no outer
coding and no global non-erasing hypothesis (concept
`jis_sem_817d955b6393d48d72476d2d`, clause `pure_morphic_word`; statements
`jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`). -/
@[nolint unusedArguments]
public def IsPureMorphic {A : Type*} [Finite A] (w : Nat → A) : Prop :=
  ∃ (f : A → List A) (a : A), IsPrefixPreserving f a ∧ IsOmegaLimit f a w

end

end MetaMathlibExt
