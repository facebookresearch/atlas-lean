/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finite.Defs
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

/-- **Extension of a letter map to finite words.** Given a map $f$ sending each letter of an
alphabet $A$ to a finite word over $A$, its extension to finite words sends a word
$a_1 a_2 \cdots a_m$ over $A$ to the concatenation $f(a_1) f(a_2) \cdots f(a_m)$ of the images
of its letters in order; the empty word is sent to the empty word.

Source: concept `jis_sem_817d955b6393d48d72476d2d`, clause `word_morphism`; statements
`jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`. -/
public def morphExtend {A : Type*} (f : A → List A) (w : List A) : List A :=
  w.flatMap f

/-- **Iterates of a letter map.** Let $f$ send each letter of an alphabet $A$ to a finite word
over $A$, extended to finite words by concatenation. The iterates of $f$ on finite words over
$A$ are defined by $f^0(w) = w$ and $f^{n+1}(w) = f(f^n(w))$ for every finite word $w$ over $A$
and every natural number $n$.

Source: concept `jis_sem_817d955b6393d48d72476d2d`, clause `word_morphism`; statements
`jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`. -/
public def morphIterate {A : Type*} (f : A → List A) : Nat → List A → List A
  | 0, w => w
  | n + 1, w => morphExtend f (morphIterate f n w)

/-- **Extended letter maps preserve concatenation.** Let $f$ send each letter of an alphabet $A$
to a finite word over $A$, extended to finite words by concatenation. Then $f(uv) = f(u)f(v)$
for all finite words $u$ and $v$ over $A$.

Source: concept `jis_sem_817d955b6393d48d72476d2d`, clause `word_morphism`; statements
`jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`. -/
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

/-- **Length of iterates of a uniform letter map.** Let $k$ be a natural number and let $f$ send
each letter of an alphabet $A$ to a word of length exactly $k$ over $A$, extended to finite
words by concatenation, with iterates $f^n$ (where $f^0$ is the identity). Then for every
natural number $n$ and every finite word $w$ over $A$, the word $f^n(w)$ has length $k^n$ times
the length of $w$. -/
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

/-- **Non-erasing letter maps.** A map $f$ sending each letter of an alphabet $A$ to a finite
word over $A$ is non-erasing when the word $f(a)$ is nonempty for every letter $a \in A$.

Source: concept `jis_sem_817d955b6393d48d72476d2d`, clause `non_erasing`; statements
`jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`. -/
public def IsNonErasing {A : Type*} (f : A → List A) : Prop :=
  ∀ a : A, f a ≠ []

/-- **Prolongable letter maps.** Let $f$ send each letter of an alphabet $A$ to a finite word
over $A$, extended to finite words by concatenation, with iterates $f^n$ (where $f^0$ is the
identity). Then $f$ is prefix-preserving (prolongable) at a letter $a \in A$ when
$f(a) = a\alpha$ for some finite word $\alpha$ over $A$ such that the word $f^n(\alpha)$ is
nonempty for every natural number $n$, including $n = 0$.

Source: concept `jis_sem_817d955b6393d48d72476d2d`, clause `prefix_preserving`; statements
`jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`. -/
public def IsPrefixPreserving {A : Type*} (f : A → List A) (a : A) : Prop :=
  ∃ α : List A, f a = a :: α ∧ ∀ n : Nat, morphIterate f n α ≠ []

/-- **Infinite word as the limit of iterates.** Let $f$ send each letter of an alphabet $A$ to a
finite word over $A$, extended to finite words by concatenation, with iterates $f^n$ (where $f^0$
is the identity), let $a \in A$, and let $w = w_0 w_1 w_2 \cdots$ be an infinite word over $A$.
Then $w$ is the limit of the iterates of $f$ at $a$ when the lengths of the words $f^n(a)$
(iterates applied to the one-letter word $a$) are unbounded as $n$ ranges over the natural
numbers, and for every $n$ and every position $i$ of $f^n(a)$, counted from $0$, the letter of
$f^n(a)$ at position $i$ is $w_i$.

Source: concept `jis_sem_817d955b6393d48d72476d2d`, clause `omega_limit`; statements
`jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`. -/
public def IsOmegaLimit {A : Type*} (f : A → List A) (a : A) (w : Nat → A) : Prop :=
  (∀ M : Nat, ∃ n : Nat, M ≤ (morphIterate f n [a]).length) ∧
    ∀ n : Nat, ∀ i : Nat, ∀ h : i < (morphIterate f n [a]).length,
      GetElem.getElem (morphIterate f n [a]) i h = w i

/-- **Pure morphic words.** An infinite word $w$ over a finite alphabet $A$ is pure morphic when
there are a map $f$ sending each letter of $A$ to a finite word over $A$ and a letter $a \in A$
such that $f$ is prolongable at $a$ and $w$ is the limit of the iterates of $f$ at $a$.

No coding is applied to the limit, and $f$ is not required to be non-erasing on every letter.

Source: concept `jis_sem_817d955b6393d48d72476d2d`, clause `pure_morphic_word`; statements
`jis_59581da9ed7395999b79fb6c`, `jis_686fde4820b8be0b1543930a`,
`jis_83acfc0f995c923dbbbed9e5`, `jis_95467c21193bf40b4aae1281`,
`jis_e5dacb15b7f36a3e2d33683c`, `jis_f0ae0eecd29e48e7e5a45717`. -/
public def IsPureMorphic {A : Type*} [Finite A] (w : Nat → A) : Prop :=
  ∃ (f : A → List A) (a : A), IsPrefixPreserving f a ∧ IsOmegaLimit f a w

end

end MetaMathlibExt
