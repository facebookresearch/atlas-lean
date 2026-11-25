/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card

namespace MetaMathlibExt

@[expose] public section

/-- **Regular fractal sequence.** A regular fractal sequence is a sequence $(x_n)_{n \ge 0}$ of
positive integers together with a position array $(p_i(j))_{i, j \ge 0}$ of natural numbers such
that: for every $i \ge 0$, the strictly increasing sequence $p_i(0) < p_i(1) < \cdots$ lists
exactly the positions $n$ with $x_n = i + 1$ (so every positive integer occurs infinitely often);
for all $i$ and $n$ with $x_n = i + 2$, some $m < n$ has $x_m = i + 1$; for all $h$, $i$ and $j$
with $h < i$, exactly one $k$ satisfies $p_i(j) < p_h(k) < p_i(j + 1)$; and for every $j$,
$p_i(j)$ is strictly increasing in $i$.

Source JIS VOL25/Kimberling,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Kimberling/kimber16.tex>, lines 103–219;
concept `jis_term_9b50b937a4f55a665e8d81fb`.

Source positive value `i + 1` is represented directly as the natural `i + 1`,
and `pos i j` is the zero-based position of its `j`-th occurrence. -/
public structure FractalSequence where
  /-- The positive-valued sequence. -/
  seq : ℕ → ℕ
  seq_pos : ∀ n, 0 < seq n
  /-- `pos i j` is the zero-based index of the `j`-th occurrence of value `i + 1`. -/
  pos : ℕ → ℕ → ℕ
  /-- Occurrence positions for a fixed value increase strictly. -/
  pos_strict : ∀ i, StrictMono (pos i)
  /-- Every recorded occurrence position contains the corresponding value. -/
  pos_sound : ∀ i j, seq (pos i j) = i + 1
  /-- Every occurrence of a value appears in its position row. -/
  pos_complete : ∀ i n, seq n = i + 1 → ∃ j, pos i j = n
  /-- Source condition (F2), shifted to zero-based value indices. -/
  cond_F2 : ∀ n i, seq n = i + 2 → ∃ m, m < n ∧ seq m = i + 1
  /-- Source condition (F3): exactly one smaller-value position lies strictly
  between consecutive positions of a larger value. -/
  cond_F3 : ∀ h i j, h < i → ∃! k, pos i j < pos h k ∧ pos h k < pos i (j + 1)
  /-- Regularity: every column of the position array increases strictly. -/
  pos_column_strict : ∀ j, StrictMono (fun i => pos i j)

/-- **Occurrence positions are distinct.** In a regular fractal sequence with position array
$p$, for every $i \ge 0$ the map $j \mapsto p_i(j)$, sending $j$ to the position of the $j$-th
occurrence of $i + 1$ (counting from $j = 0$), is injective. -/
public theorem FractalSequence.pos_injective (X : FractalSequence) (i : ℕ) :
    Function.Injective (X.pos i) :=
  (X.pos_strict i).injective

/-- **Every value occurs infinitely often in a regular fractal sequence.** Let $(x_n)_{n \ge 0}$
be a regular fractal sequence. Then for every positive integer $k$ there are infinitely many $n$
with $x_n = k$. -/
public theorem FractalSequence.infinite_occurrences (X : FractalSequence) (i : ℕ) :
    Set.Infinite {n | X.seq n = i + 1} := by
  have hf : Function.Injective
      (fun j => (⟨X.pos i j, X.pos_sound i j⟩ : {n // X.seq n = i + 1})) := by
    intro a b hab
    have hpos : X.pos i a = X.pos i b := congrArg Subtype.val hab
    exact (X.pos_strict i).injective hpos
  exact Set.infinite_coe_iff.mp (Infinite.of_injective _ hf)

end


end MetaMathlibExt
