/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Symmetric peaks and valleys in compositions

A symmetric peak or valley has equal outer parts. For three-part compositions with a
valley, indexing by the middle part gives a formula for the sum of the depths.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of symmetric peaks.** For a finite word $w = w_1 w_2 \cdots w_m$ of natural
numbers, a symmetric peak is a factor $w_i w_{i+1} w_{i+2}$ of three consecutive letters with
$w_i = w_{i+2} < w_{i+1}$. The number of symmetric peaks of $w$ is the number of indices $i$
with $1 \le i \le m - 2$ at which $w$ has a symmetric peak (overlapping peaks all count); it
is $0$ when $m < 3$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Section 1 (symmetric peaks). -/
def symmetricPeakCount : List ℕ → ℕ
  | a :: b :: c :: t => (if a = c ∧ a < b then 1 else 0) + symmetricPeakCount (b :: c :: t)
  | _ => 0

/-- **Sum of the heights of symmetric peaks.** For a finite word $w = w_1 w_2 \cdots w_m$ of
natural numbers, a symmetric peak is a factor $w_i w_{i+1} w_{i+2}$ of three consecutive
letters with $w_i = w_{i+2} < w_{i+1}$, and its height is $w_{i+1} - w_i$. The symmetric peak
height sum of $w$ is the sum of the heights of the symmetric peaks of $w$ over all indices $i$
with $1 \le i \le m - 2$ at which one occurs; it is $0$ when $m < 3$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Section 1 (heights of symmetric peaks). -/
def symmetricPeakHeightSum : List ℕ → ℕ
  | a :: b :: c :: t =>
      (if a = c ∧ a < b then b - a else 0) + symmetricPeakHeightSum (b :: c :: t)
  | _ => 0

/-- **Number of symmetric valleys of a word.** For a word $w = w_1 w_2 \cdots w_\ell$ of natural
numbers, a symmetric valley is a position $i$ with $1 < i < \ell$ such that $w_{i-1} = w_{i+1}$
and $w_i < w_{i-1}$, that is, a factor $a\,b\,a$ with $b < a$. The symmetric valley count of $w$
is the number of such positions; in particular it is $0$ when $\ell < 3$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Section 1 (symmetric valleys). -/
def symmetricValleyCount : List ℕ → ℕ
  | a :: b :: c :: t => (if a = c ∧ b < a then 1 else 0) + symmetricValleyCount (b :: c :: t)
  | _ => 0

/-- **Total depth of the symmetric valleys of a word.** For a word $w = w_1 w_2 \cdots w_\ell$ of
natural numbers, a symmetric valley is a position $i$ with $1 < i < \ell$ such that
$w_{i-1} = w_{i+1}$ and $w_i < w_{i-1}$; its depth is $w_{i-1} - w_i$. The symmetric valley depth
sum of $w$ is the sum of the depths of all its symmetric valleys; in particular it is $0$ when
$\ell < 3$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Section 1 (depths of symmetric valleys). -/
def symmetricValleyDepthSum : List ℕ → ℕ
  | a :: b :: c :: t =>
      (if a = c ∧ b < a then a - b else 0) + symmetricValleyDepthSum (b :: c :: t)
  | _ => 0

/-- **Symmetric peak examples among the compositions of 5.** The symmetric peak height sums of
the words $1\,3\,1$, $1\,2\,1\,1$, $1\,1\,2\,1$ and $1\,1\,1\,1\,1$ are $2$, $1$, $1$ and $0$
respectively, and the word $1\,3\,1$ has exactly one symmetric peak.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
example after Corollary 1. -/
theorem symmetricPeakHeightSum_examples :
    symmetricPeakHeightSum [1, 3, 1] = 2 ∧ symmetricPeakHeightSum [1, 2, 1, 1] = 1 ∧
      symmetricPeakHeightSum [1, 1, 2, 1] = 1 ∧ symmetricPeakHeightSum [1, 1, 1, 1, 1] = 0 ∧
      symmetricPeakCount [1, 3, 1] = 1 := by
  decide

/-- **Symmetric valleys in three compositions of eight.** The word $2\,1\,2\,1\,2$ has two
symmetric valleys and total symmetric valley depth $2$, the word $3\,1\,3\,1$ has total symmetric
valley depth $2$, and the word $3\,2\,3$ has total symmetric valley depth $1$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
example after Corollary 2. -/
theorem symmetricValleyDepthSum_examples :
    symmetricValleyDepthSum [2, 1, 2, 1, 2] = 2 ∧ symmetricValleyCount [2, 1, 2, 1, 2] = 2 ∧
      symmetricValleyDepthSum [3, 1, 3, 1] = 2 ∧ symmetricValleyDepthSum [3, 2, 3] = 1 := by
  decide

/-- **Total depth of symmetric valleys over compositions with three parts.** For every natural
number $n$, the sum, over all compositions $c$ of $n$ with exactly three parts, of the total
depth of the symmetric valleys of the sequence of parts of $c$ equals
$\sum_{m=1}^{\lfloor (n-2)/3 \rfloor} d_m$, where $d_m = (n-3m)/2$ if $n - m$ is even and
$d_m = 0$ otherwise.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Theorem 4(b) (`integers-2026-A65-thm-4`). -/
theorem symmetricValleyDepthSum_compositions_length_three (n : ℕ) :
    ∑ c ∈ Finset.univ.filter (fun c : Composition n => c.length = 3),
        symmetricValleyDepthSum c.blocks =
      ∑ m ∈ Finset.Icc 1 ((n - 2) / 3), if Even (n - m) then (n - 3 * m) / 2 else 0 := by
  rw [← Finset.sum_filter (fun m => Even (n - m))]
  let middles := (Finset.Icc 1 ((n - 2) / 3)).filter (fun m => Even (n - m))
  -- A middle part determines both outer parts.
  let valley (m : ℕ) (hm : m ∈ middles) : Composition n := by
    have hbounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    refine ⟨[(n - m) / 2, m, (n - m) / 2], ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> omega
    · obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hm).2
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
  symm
  refine Finset.sum_bij_ne_zero (fun m hm _ => valley m hm) ?_ ?_ ?_ ?_
  · intro m hm _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · intro m hm _ k hk _ h
    exact Option.some.inj (congrArg (fun c : Composition n => c.blocks[1]?) h)
  · intro c hc hd
    obtain ⟨a, m, b, hblocks⟩ := List.length_eq_three.mp (Finset.mem_filter.mp hc).2
    by_cases hv : a = b ∧ m < a
    · obtain ⟨rfl, hma⟩ := hv
      have hm : 0 < m := c.blocks_pos (by simp [hblocks])
      have hn := c.blocks_sum
      simp only [hblocks, List.sum_cons, List.sum_nil, Nat.add_zero] at hn
      have hmem : m ∈ middles := by
        simp only [middles, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hm, by omega⟩, a, by omega⟩
      refine ⟨m, hmem, by omega, Composition.ext ?_⟩
      have ha : (n - m) / 2 = a := by omega
      simp [valley, hblocks, ha]
    · simp [hblocks, symmetricValleyDepthSum, hv] at hd
  · intro m hm _
    obtain ⟨hm₁, hm₂⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    have hlt : m < (n - m) / 2 := by omega
    simp [valley, symmetricValleyDepthSum, hlt]
    omega

end

end MetaMathlibExt
