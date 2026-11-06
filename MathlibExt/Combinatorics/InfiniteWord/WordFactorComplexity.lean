/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfiniteWord.Factor
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt

/-- **Factor complexity of an infinite word.** Let $w = w_0 w_1 w_2 \cdots$ be an infinite word
over a finite alphabet $A$. For $n \ge 0$ and a position $i \ge 0$, the factor of $w$ of length
$n$ at position $i$ is the word $w_i w_{i+1} \cdots w_{i+n-1}$. The factor complexity $p_w(n)$ is
the number of distinct factors of $w$ of length $n$, each word being counted once however often it
occurs in $w$.

Source: Fabien Durand, Julien Leroy, and Gwenaël Richomme, *Do the
Properties of an S-adic Representation Determine Factor Complexity?*,
Journal of Integer Sequences 16 (2013), Article 13.2.6, complexity-function
definition, lines 117–128,
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Durand/durand2.tex>. -/
noncomputable def wordFactorComplexity {A : Type*} [Finite A]
    (w : ℕ → A) (n : ℕ) : ℕ :=
  Set.ncard (InfiniteWord.factorSet w n)

/-- **Factor complexity at length zero.** For every infinite word $w$ over a finite alphabet,
the factor complexity of $w$ at length $0$ equals $1$, that is, $p_w(0) = 1$: the empty word is
the only factor of $w$ of length $0$. -/
theorem wordFactorComplexity_zero {A : Type*} [Finite A]
    (w : ℕ → A) : wordFactorComplexity w 0 = 1 := by
  unfold wordFactorComplexity InfiniteWord.factorSet
  have hsingle : Set.range (InfiniteWord.factor w 0) =
      {InfiniteWord.factor w 0 0} := by
    ext f
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨i, rfl⟩ := h
      exact funext fun j => nomatch j
    · intro h
      rw [h]
      exact ⟨0, rfl⟩
  rw [hsingle, Set.ncard_singleton]

end MetaMathlibExt
