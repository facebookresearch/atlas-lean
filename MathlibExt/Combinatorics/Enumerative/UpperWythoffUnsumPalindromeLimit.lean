/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.UpperWythoffUnsumPalindrome
import all MathlibExt.Combinatorics.Enumerative.UpperWythoffUnsumPalindrome

/-!
# Limit of the upper Wythoff unsum gap words

The words between successive pairs of markers converge letter by letter to a leading three
followed by the Fibonacci word coded by zero to five and one to three.
-/

namespace MetaMathlibExt

namespace upperWythoffUnsumPalindrome_tendsto

open upperWythoffUnsumPalindrome_reverse

-- At level n + 1 the last block is W_{n+3}, a central word flanked by threes.
private theorem palindrome_eq_enclosed (n : ℕ) :
    upperWythoffUnsumPalindrome (n + 3) = enclosed (central (n + 1)) := by
  have hj : 2 * n + 4 < (blocks (n + 1)).length := by rw [blocks_length]; omega
  rw [upperWythoffUnsumPalindrome, show 2 * (n + 3) - 2 = 2 * n + 4 by omega, word_eq_block hj]
  have hs : (blocks n).length ≤ 2 * n + 4 := by rw [blocks_length]; omega
  simp [blocks, List.getElem_append_right hs, blocks_length,
    show 2 * n + 4 - (2 * n + 3) = 1 by omega]

-- The center of W_{n+4} starts with the entire coded (n + 2)-nd Fibonacci word.
private theorem digit (n k : ℕ) (hk : k < (fibWord (n + 2)).length) :
    (upperWythoffUnsumPalindrome (n + 4))[k + 1]? = some (if fibInf k then 3 else 5) := by
  have hlen : k < (letters (n + 2)).length := by simpa [letters] using hk
  have hbit : (fibWord (n + 2))[k] = fibInf k := by simpa [hk] using fibInf_agrees _ _ hk
  rw [palindrome_eq_enclosed (n + 1)]
  simp only [enclosed, central, List.cons_append, List.getElem?_cons_succ, List.append_assoc,
    List.getElem?_append_left hlen]
  simp [letters, hk, hbit]

end upperWythoffUnsumPalindrome_tendsto

/-- **The words $W_i$ converge to $3$ followed by the coded Fibonacci word.** Let
$u_0 u_1 u_2 \cdots$ be the infinite Fibonacci word over $\{0, 1\}$, indexed from $0$, and let
$\mathbf{V}$ be the infinite word obtained from it by replacing each $0$ by $5$ and each
$1$ by $3$. Then the words $W_i$ of the unsum gap sequence converge to the infinite word
$3\mathbf{V}$: for every $k \ge 0$ there is $N$ such that for every $i \ge N$ the word $W_i$ has
more than $k$ digits and its digit at position $k$ (counted from zero) is the digit of
$3\mathbf{V}$ at position $k$, that is, $3$ if $k = 0$, and for $k \ge 1$ it is $3$ if
$u_{k-1} = 1$ and $5$ if $u_{k-1} = 0$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 9 (`jis-2025-25.3.8-lem-9`). -/
public theorem upperWythoffUnsumPalindrome_tendsto (k : ℕ) :
    ∃ N, ∀ i, N ≤ i → (upperWythoffUnsumPalindrome i)[k]? =
      some (if k = 0 then 3 else if fibInf (k - 1) = true then 3 else 5) := by
  cases k with
  | zero =>
    refine ⟨1, fun i hi => ?_⟩
    simpa [List.head?_eq_getElem?] using (upperWythoffUnsumPalindrome_head_getLast hi).1
  | succ k =>
    refine ⟨k + 4, fun i hi => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 4 := ⟨i - 4, by omega⟩
    have hlen := fibWord_length (n + 2)
    simpa using upperWythoffUnsumPalindrome_tendsto.digit n k (by omega)

end MetaMathlibExt
