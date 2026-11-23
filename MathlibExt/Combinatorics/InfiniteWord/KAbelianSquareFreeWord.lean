/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

namespace MetaMathlibExt

@[expose] public section

/-!
# k-abelian square-free words

Source: T. Huova and A. Saarela, *Strongly k-abelian repetitions*, Journal of Integer
Sequences 16 (2013),
[`huova2.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL16/Huova/huova2.tex).
-/

/-- **Number of occurrences of a factor.** For words $w$ and $t$ over an alphabet with $t$
nonempty, the factor count of $t$ in $w$ is the number of positions of $w$ at which an occurrence
of $t$ starts, overlapping occurrences all being counted. The factor count of the empty word is
$0$. -/
public def wordFactorCount {α : Type*} [DecidableEq α] (w t : List α) : ℕ :=
  if t = [] then 0
  else
    match w with
    | [] => 0
    | _ :: ws => (if w.take t.length = t then 1 else 0) + wordFactorCount ws t

/-- **$k$-abelian equivalence.** For a natural number $k$, two words $u$ and $v$ over an alphabet
are $k$-abelian equivalent when $k \ge 1$, both $u$ and $v$ are nonempty, $u$ and $v$ have the
same prefix of length $k - 1$ and the same suffix of length $k - 1$ (a word shorter than
$k - 1$ counting as its own prefix and suffix), and every word $t$ of length $k$ occurs as a
factor of $u$, counting overlapping occurrences, exactly as often as it occurs in $v$. -/
public def IsKAbelianEquivalent {α : Type*} [DecidableEq α]
    (k : ℕ) (u v : List α) : Prop :=
  1 ≤ k ∧ u ≠ [] ∧ v ≠ [] ∧
    u.take (k - 1) = v.take (k - 1) ∧
    u.drop (u.length - (k - 1)) = v.drop (v.length - (k - 1)) ∧
    ∀ t : List α, t.length = k → wordFactorCount u t = wordFactorCount v t

/-- **$k$-abelian squares.** For a natural number $k$, a word $w$ is a $k$-abelian square when
$w = uv$ for two nonempty words $u$ and $v$ that are $k$-abelian equivalent. -/
public def IsKAbelianSquare {α : Type*} [DecidableEq α]
    (k : ℕ) (w : List α) : Prop :=
  ∃ u v : List α, w = u ++ v ∧ IsKAbelianEquivalent k u v

/-- **$k$-abelian square-free words.** For a natural number $k$, a finite word $w$ is
$k$-abelian square-free when $k \ge 1$ and no factor of $w$ (a word $x$ with $w = pxs$ for some
words $p$ and $s$) is a $k$-abelian square. -/
public def IsKAbelianSquareFree {α : Type*} [DecidableEq α]
    (k : ℕ) (w : List α) : Prop :=
  1 ≤ k ∧ ∀ pre factor suf : List α,
    w = pre ++ factor ++ suf → ¬ IsKAbelianSquare k factor

/-- **$3$-abelian equivalence of ternary words.** Two words $u$ and $v$ over the alphabet
$\{0, 1, 2\}$ are $3$-abelian equivalent when they are $k$-abelian equivalent for $k = 3$: both
are nonempty, they have the same prefix and the same suffix of length $2$ (a shorter word
counting as its own prefix and suffix), and every word of length $3$ occurs as a factor of $u$,
counting overlapping occurrences, exactly as often as it occurs in $v$. -/
public def IsThreeAbelianEquivalent (u v : List (Fin 3)) : Prop :=
  IsKAbelianEquivalent 3 u v

/-- **$3$-abelian squares over a ternary alphabet.** A word $w$ over the alphabet $\{0, 1, 2\}$ is
a $3$-abelian square when $w = uv$ for two nonempty words $u$ and $v$ that are $3$-abelian
equivalent. -/
public def IsThreeAbelianSquare (w : List (Fin 3)) : Prop :=
  IsKAbelianSquare 3 w

/-- **$3$-abelian square-free ternary words.** A finite word $w$ over the alphabet $\{0, 1, 2\}$
is $3$-abelian square-free when no factor of $w$ (a word $x$ with $w = pxs$ for some words $p$
and $s$) is a $3$-abelian square. -/
public def IsThreeAbelianSquareFree (w : List (Fin 3)) : Prop :=
  IsKAbelianSquareFree 3 w

end

end MetaMathlibExt
