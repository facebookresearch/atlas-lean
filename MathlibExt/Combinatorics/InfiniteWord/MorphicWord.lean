/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord

namespace MetaMathlibExt

@[expose] public section

/-- **Morphic words via a coding.** Let $A$ be a finite alphabet, $B$ any alphabet, $u$ an
infinite word over $A$, $\tau : A \to B$ a map (a coding) and $w$ an infinite word over $B$.
Then $w$ is morphic with generator $u$ and coding $\tau$ if $u$ is a pure morphic word and
$w(n) = \tau(u(n))$ for every $n \in \mathbb{N}$.

Source: concept `jis_sem_8aa01797a09c6951299c4a2d`; statements `jis_305f669a0778b2b0011670ec`,
`jis_59581da9ed7395999b79fb6c`, `jis_d868c1fc64073e778b524189`, and
`jis_de6cb6fe1f9e977bace8a77d`. -/
public def IsMorphic {A B : Type*} [Finite A] (u : Nat → A) (coding : A → B) (w : Nat → B) : Prop :=
  IsPureMorphic u ∧ ∀ n, w n = coding (u n)

/-- **Building a morphic word from its generator.** Let $A$ be a finite alphabet, $u$ a pure
morphic infinite word over $A$, $\tau : A \to B$ a map and $w$ an infinite word over $B$. If
$w(n) = \tau(u(n))$ for every $n \in \mathbb{N}$, then $w$ is morphic with generator $u$ and
coding $\tau$.

Source: concept `jis_sem_8aa01797a09c6951299c4a2d`; statements `jis_305f669a0778b2b0011670ec`,
`jis_59581da9ed7395999b79fb6c`, `jis_d868c1fc64073e778b524189`, and
`jis_de6cb6fe1f9e977bace8a77d`. -/
public theorem IsMorphic.intro {A B : Type*} [Finite A] {u : Nat → A} {coding : A → B}
    {w : Nat → B} (hPure : IsPureMorphic u)
    (hCode : ∀ n, w n = coding (u n)) : IsMorphic u coding w :=
  ⟨hPure, hCode⟩

/-- **The generator of a morphic word is pure morphic.** Let $A$ be a finite alphabet, $u$ an
infinite word over $A$, $\tau : A \to B$ a map and $w$ an infinite word over $B$. If $w$ is
morphic with generator $u$ and coding $\tau$, then $u$ is a pure morphic word.

Source: concept `jis_sem_8aa01797a09c6951299c4a2d`; statements `jis_305f669a0778b2b0011670ec`,
`jis_59581da9ed7395999b79fb6c`, `jis_d868c1fc64073e778b524189`, and
`jis_de6cb6fe1f9e977bace8a77d`. -/
public theorem IsMorphic.pure {A B : Type*} [Finite A] {u : Nat → A} {coding : A → B}
    {w : Nat → B} (h : IsMorphic u coding w) : IsPureMorphic u :=
  h.1

/-- **A morphic word is the coding of its generator.** Let $A$ be a finite alphabet, $u$ an
infinite word over $A$, $\tau : A \to B$ a map and $w$ an infinite word over $B$. If $w$ is
morphic with generator $u$ and coding $\tau$, then $w(n) = \tau(u(n))$ for every
$n \in \mathbb{N}$.

Source: concept `jis_sem_8aa01797a09c6951299c4a2d`; statements `jis_305f669a0778b2b0011670ec`,
`jis_59581da9ed7395999b79fb6c`, `jis_d868c1fc64073e778b524189`, and
`jis_de6cb6fe1f9e977bace8a77d`. -/
public theorem IsMorphic.coding_eq {A B : Type*} [Finite A] {u : Nat → A} {coding : A → B}
    {w : Nat → B} (h : IsMorphic u coding w) (n : Nat) : w n = coding (u n) :=
  h.2 n

/-- **Pure morphic words are morphic.** Let $A$ be a finite alphabet and $u$ a pure morphic
infinite word over $A$. Then $u$ is morphic with generator $u$ and the identity coding of $A$.

Source: concept `jis_sem_8aa01797a09c6951299c4a2d`; statements `jis_305f669a0778b2b0011670ec`,
`jis_59581da9ed7395999b79fb6c`, `jis_d868c1fc64073e778b524189`, and
`jis_de6cb6fe1f9e977bace8a77d`. -/
public theorem IsMorphic.ofPureMorphic {A : Type*} [Finite A] {u : Nat → A}
    (hu : IsPureMorphic u) : IsMorphic u id u :=
  ⟨hu, fun _ => rfl⟩

end

end MetaMathlibExt
