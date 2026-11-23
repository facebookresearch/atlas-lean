/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Ideal period words and their block counts

Jaap de Jonge's *Intervals of N-Expansions with Many Gaps* (INTEGERS 26 (2026), Article A75)
defines in Definition 7 the ideal period words `d_n`: finite lists of blocks of partial quotients,
each block being `a = 2, 1, 1` or `b = 2, 2`. This file holds their definition, two computed
values and Lemma 8, which counts the blocks of each kind. The paper's other statements are in
`WantedExt.Dynamics.NExpansionGapsWanted`.

## Main declarations

* `MetaMathlibExt.idealPeriodWord`: the ideal period word `d_n`, a list of blocks.
* `MetaMathlibExt.idealPeriodWord_count_blocks` (Lemma 8): for `n ≥ 1`, `d_n` has `2^(n-1)`
  blocks `2, 2`, and its number `c_n` of blocks `2, 1, 1` satisfies `3 c_n = 2^n - (-1)^n`.

## Proof outline

Write lists of blocks as in Definition 7. From `n = 4` on, `d_n = [j, abb]` for some list `j`
when `n` is even, and `d_n = [j, ab, ab]` when `n` is odd. In the first case the recursion gives
`d_(n+1) = [j, abb, j, ab, ab]`, in the second `d_(n+1) = [j, ab, ab, j, abb]`, so the pattern
carries over to `n + 1`. In both cases the number of blocks `2, 2` doubles, and the number of
blocks `2, 1, 1` goes from `c_n` to `2 c_n + (-1)^n`, the recursion of `(2^n - (-1)^n) / 3`.
The words `d_1`, `d_2`, `d_3` and `d_4` are checked by computation.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Ideal period words.** For $n \ge 1$, the ideal period word $d_n$ is a finite list of blocks
of partial quotients, each block being $a = 2, 1, 1$ or $b = 2, 2$. Writing lists of blocks by
juxtaposition, with commas between parts, $d_1 = [ab]$, $d_2 = [abb]$, $d_3 = [abb, ab, ab]$ and
$d_4 = [abb, ab, ab, abb, abb]$; for $n \ge 5$, if $d_{n-1} = [j, ab, ab]$ for a list $j$ then
$d_n = [j, ab, ab, j, abb]$, and if $d_{n-1} = [j, abb]$ then $d_n = [j, abb, j, ab, ab]$. The
digit string of $d_n$ is the concatenation of its blocks. For $n = 0$ the list is empty, a
placeholder.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 7. -/
public def idealPeriodWord : ℕ → List (List ℕ)
  | 0 => []
  | 1 => [[2, 1, 1], [2, 2]]
  | 2 => [[2, 1, 1], [2, 2], [2, 2]]
  | 3 => [[2, 1, 1], [2, 2], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]
  | 4 => [[2, 1, 1], [2, 2], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2],
      [2, 2], [2, 1, 1], [2, 2], [2, 2]]
  | n + 5 =>
    let w := idealPeriodWord (n + 4)
    if w.drop (w.length - 4) = [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] then
      w ++ w.take (w.length - 4) ++ [[2, 1, 1], [2, 2], [2, 2]]
    else if w.drop (w.length - 3) = [[2, 1, 1], [2, 2], [2, 2]] then
      w ++ w.take (w.length - 3) ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]
    else w

/-- **The fifth ideal period word.** Writing $a$ for the block $2, 1, 1$ and $b$ for the block
$2, 2$ of partial quotients, the ideal period word $d_5$ is $d_4$ followed by the blocks
$abb\,ab\,ab\,abb\,ab\,ab$, in this order.

This is the second recursion rule applied to $d_4 = [j, abb]$ with $j = [abb, ab, ab, abb]$.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 7. -/
public theorem idealPeriodWord_five :
    idealPeriodWord 5 = idealPeriodWord 4 ++
      [[2, 1, 1], [2, 2], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2], [2, 2],
        [2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := by
  decide

/-- **Lengths of the first ideal period words.** The digit strings of the ideal period words
$d_1, d_2, d_3, d_4, d_5$ have lengths $5, 7, 17, 31, 65$ respectively.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Definition 7. -/
public theorem idealPeriodWord_flatten_length_small :
    ((List.range 5).map fun n => (idealPeriodWord (n + 1)).flatten.length) =
      [5, 7, 17, 31, 65] := by
  decide

/-- The recursion step of the ideal period words, unfolded for an index `n + 5`. -/
private theorem idealPeriodWord_add_five (n : ℕ) :
    idealPeriodWord (n + 5) =
      let w := idealPeriodWord (n + 4)
      if w.drop (w.length - 4) = [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] then
        w ++ w.take (w.length - 4) ++ [[2, 1, 1], [2, 2], [2, 2]]
      else if w.drop (w.length - 3) = [[2, 1, 1], [2, 2], [2, 2]] then
        w ++ w.take (w.length - 3) ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]
      else w :=
  rfl

/-- If the ideal period word $d_{n+4}$ is $[j, ab, ab]$, then $d_{n+5} = [j, ab, ab, j, abb]$. -/
private theorem idealPeriodWord_add_five_of_abab {n : ℕ} {j : List (List ℕ)}
    (h : idealPeriodWord (n + 4) = j ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]) :
    idealPeriodWord (n + 5) = idealPeriodWord (n + 4) ++ j ++ [[2, 1, 1], [2, 2], [2, 2]] := by
  rw [idealPeriodWord_add_five]
  simp [h]

/-- If the ideal period word $d_{n+4}$ is $[j, abb]$, then $d_{n+5} = [j, abb, j, ab, ab]$. -/
private theorem idealPeriodWord_add_five_of_abb {n : ℕ} {j : List (List ℕ)}
    (h : idealPeriodWord (n + 4) = j ++ [[2, 1, 1], [2, 2], [2, 2]]) :
    idealPeriodWord (n + 5) =
      idealPeriodWord (n + 4) ++ j ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := by
  -- The last four blocks are `[x, a, b, b]` (or there are only three), never `[a, b, a, b]`.
  have h4 : (idealPeriodWord (n + 4)).drop ((idealPeriodWord (n + 4)).length - 4) ≠
      [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := by
    rw [h]
    rcases List.eq_nil_or_concat j with rfl | ⟨L, x, rfl⟩
    · decide
    · simp
  rw [idealPeriodWord_add_five]
  simp only [h4, ite_false]
  simp [h]

/-- From $d_4$ on, the ideal period word $d_{k+4}$ ends with the blocks $abb$ when $k$ is even
and with the blocks $ab, ab$ when $k$ is odd. -/
private theorem idealPeriodWord_add_four_shape (k : ℕ) :
    (Even k → ∃ j, idealPeriodWord (k + 4) = j ++ [[2, 1, 1], [2, 2], [2, 2]]) ∧
      (Odd k → ∃ j, idealPeriodWord (k + 4) = j ++ [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]]) := by
  induction k with
  | zero =>
    exact ⟨fun _ => ⟨[[2, 1, 1], [2, 2], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1], [2, 2], [2, 1, 1],
      [2, 2], [2, 2]], rfl⟩, fun h => absurd h (by decide)⟩
  | succ k ih =>
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨j, hj⟩ := ih.2 (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hk))
      exact ⟨idealPeriodWord (k + 4) ++ j, idealPeriodWord_add_five_of_abab hj⟩
    · obtain ⟨j, hj⟩ := ih.1 (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hk))
      exact ⟨idealPeriodWord (k + 4) ++ j, idealPeriodWord_add_five_of_abb hj⟩

/-- From $d_4$ to $d_5$ and onwards, the number of blocks $2, 2$ doubles, and the number $c$ of
blocks $2, 1, 1$ of $d_{k+4}$ becomes $2c + (-1)^k$ in $d_{k+5}$. -/
private theorem idealPeriodWord_add_five_count (k : ℕ) :
    (idealPeriodWord (k + 5)).count [2, 2] = 2 * (idealPeriodWord (k + 4)).count [2, 2] ∧
      ((idealPeriodWord (k + 5)).count [2, 1, 1] : ℤ) =
        2 * (idealPeriodWord (k + 4)).count [2, 1, 1] + (-1) ^ k := by
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨j, hj⟩ := (idealPeriodWord_add_four_shape k).1 hk
    rw [idealPeriodWord_add_five_of_abb hj, hj, hk.neg_one_pow]
    simp
    omega
  · obtain ⟨j, hj⟩ := (idealPeriodWord_add_four_shape k).2 hk
    rw [idealPeriodWord_add_five_of_abab hj, hj, hk.neg_one_pow]
    simp
    omega

/-- The block counts of the ideal period word $d_{k+4}$. -/
private theorem idealPeriodWord_add_four_count (k : ℕ) :
    (idealPeriodWord (k + 4)).count [2, 2] = 2 ^ (k + 3) ∧
      3 * ((idealPeriodWord (k + 4)).count [2, 1, 1] : ℤ) = 2 ^ (k + 4) - (-1) ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨hb, ha⟩ := idealPeriodWord_add_five_count k
    refine ⟨?_, ?_⟩
    · rw [show k + 1 + 4 = k + 5 from rfl, hb, ih.1]
      ring
    · rw [show k + 1 + 4 = k + 5 from rfl, ha]
      linear_combination 2 * ih.2

/-- **Block counts of the ideal period words.** For every $n \ge 1$, the ideal period word $d_n$
contains exactly $2^{n-1}$ blocks $2, 2$, and the number $c_n$ of its blocks $2, 1, 1$ satisfies
$3 c_n = 2^n - (-1)^n$; that is, $c_n = (2^n + 1)/3$ for odd $n$ and $c_n = (2^n - 1)/3$ for even
$n$.

In this lemma the source names the blocks $a = 2, 2$ and $b = 2, 1, 1$, the reverse of its
Definition 7; the counts are stated by block, so the naming does not matter.

Source: Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article
A75, Lemma 8 (`integers-2026-A75-lem-8`). -/
public theorem idealPeriodWord_count_blocks {n : ℕ} (hn : 1 ≤ n) :
    (idealPeriodWord n).count [2, 2] = 2 ^ (n - 1) ∧
      3 * ((idealPeriodWord n).count [2, 1, 1] : ℤ) = 2 ^ n - (-1) ^ n := by
  match n, hn with
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | k + 4, _ =>
    obtain ⟨hb, ha⟩ := idealPeriodWord_add_four_count k
    refine ⟨hb, ?_⟩
    rw [ha]
    ring

end

end MetaMathlibExt
