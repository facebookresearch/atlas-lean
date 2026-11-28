/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Rayleigh

/-!
# Moves of Beatty octal games

A heap can be removed entirely exactly when it is nonempty and its size is a positive-index term
of the first Beatty sequence.
A positive-index term of the second sequence can be removed from a strictly larger heap,
provided the number removed is positive. All moves strictly decrease the heap size.

## References

* Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with
  Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, pp. 1–38, Sections 1.1 and 2–4.
* R. K. Guy and C. A. B. Smith, *The g-values of various games*, Proceedings of the Cambridge
  Philosophical Society 52 (1956), pp. 514–526 (octal codes).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Moves of the Beatty octal game.** Let $\alpha$ and $\beta$ be real numbers. In the Beatty
octal game for $\alpha$ and $\beta$, a move takes a heap of $n$ tokens to a heap of $m$ tokens
exactly when one of the following holds: $n \ge 1$, $n = \lfloor k\alpha \rfloor$ for some
integer $k \ge 1$, and $m = 0$ (the whole heap is removed); or $m = n - i$ for some natural
number $i$ with $1 \le i < n$ and $i = \lfloor k\beta \rfloor$ for some integer $k \ge 1$
(removing $i$ tokens leaves a nonempty heap).

When $\alpha$ and $\beta$ are complementary, so that every $i \ge 1$ lies in exactly one of the
Beatty sequences $\{\lfloor k\alpha \rfloor : k \ge 1\}$ and
$\{\lfloor k\beta \rfloor : k \ge 1\}$, this is the octal game with code
$0{\cdot}d_1 d_2 d_3 \ldots$, where $d_i = 1$ if $i$ lies in the first sequence and $d_i = 2$ if
$i$ lies in the second.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 1.1 (octal codes) and
the codes of the gold, silver and bronze games in Sections 2, 3, 4. -/
def beattyOctalMove (α β : ℝ) (n m : ℕ) : Prop :=
  (0 < n ∧ (∃ k : ℤ, 0 < k ∧ beattySeq α k = n) ∧ m = 0) ∨
    ∃ i : ℕ, (∃ k : ℤ, 0 < k ∧ beattySeq β k = i) ∧ 0 < i ∧ i < n ∧ m = n - i

/-- **Moves of a Beatty octal game decrease the heap.** For all real numbers $\alpha$, $\beta$
and all natural numbers $n$, $m$: if a move of the Beatty octal game for $\alpha$ and $\beta$
takes a heap of $n$ tokens to a heap of $m$ tokens, then $m < n$.

Consequently every play of the game terminates.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 1.1. -/
theorem beattyOctalMove_lt {α β : ℝ} {n m : ℕ} (h : beattyOctalMove α β n m) : m < n := by
  rcases h with ⟨hn, -, rfl⟩ | ⟨i, -, hi, hin, rfl⟩ <;> omega

/-- A move to the empty heap is legal exactly when the heap is nonempty and its size is a
positive-index term of the first Beatty sequence. -/
theorem beattyOctalMove_zero_iff {α β : ℝ} {n : ℕ} :
    beattyOctalMove α β n 0 ↔ 0 < n ∧ ∃ k : ℤ, 0 < k ∧ beattySeq α k = n := by
  constructor
  · rintro (⟨hn, hk, -⟩ | ⟨i, -, -, hin, hi⟩)
    · exact ⟨hn, hk⟩
    · omega
  · rintro ⟨hn, hk⟩
    exact Or.inl ⟨hn, hk, rfl⟩

/-- A move to a nonempty heap is legal exactly when it strictly decreases the heap and the
number of tokens removed is a positive-index term of the second Beatty sequence. -/
theorem beattyOctalMove_pos_iff {α β : ℝ} {n m : ℕ} (hm : 0 < m) :
    beattyOctalMove α β n m ↔ m < n ∧ ∃ k : ℤ, 0 < k ∧ beattySeq β k = (↑(n - m) : ℤ) := by
  constructor
  · intro h
    refine ⟨beattyOctalMove_lt h, ?_⟩
    rcases h with ⟨-, -, hzero⟩ | ⟨i, hi, -, hin, heq⟩
    · omega
    · rwa [show n - m = i by omega]
  · rintro ⟨hlt, hk⟩
    exact Or.inr ⟨n - m, hk, by omega, by omega, by omega⟩

end

end MetaMathlibExt
