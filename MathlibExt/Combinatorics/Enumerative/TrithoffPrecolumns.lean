/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.TrithoffRowDifference

/-!
# Precolumns of the Trithoff array

The three entries preceding a first-column entry can be read from its Tribonacci digits.
-/

namespace MetaMathlibExt

namespace trithoff_precolumns

/-- Removing the three low digits leaves a sum whose weights satisfy the Tribonacci rule. -/
private theorem value_three_cons (x y z : ℕ) (w : List ℕ) :
    tribonacciValue (x :: y :: z :: w) =
      tribonacciValue (y :: z :: w) + tribonacciValue (z :: w) +
        tribonacciValue w + x + y + z := by
  have hrec (i : ℕ) : tribonacci (i + 6) =
      tribonacci (i + 5) + tribonacci (i + 4) + tribonacci (i + 3) := tribonacci.eq_4 _
  simp only [tribonacciValue, List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
    List.getD_cons_zero, Nat.add_assoc, Nat.reduceAdd, hrec, Nat.mul_add, Finset.sum_add_distrib,
    show tribonacci 3 = 1 from rfl, show tribonacci 4 = 2 from rfl, show tribonacci 5 = 4 from rfl]
  omega

end trithoff_precolumns

/-- **Precolumns of the Trithoff array.** Write $[u]_T$ for the Tribonacci value of a digit
word $u$, written most significant digit first. Let $n$ have Tribonacci representation $abc1$,
where $a$ is a digit word and $b$, $c$ are digits. Let $\mathrm{out}(n) = [abc10]_T$ and
$\mathrm{out}^2(n) = [abc100]_T$ be the next two entries of the Trithoff row of $n$, and extend
the row to the left by the Tribonacci rule: in the integers, the wall is
$W = \mathrm{out}^2(n) - \mathrm{out}(n) - n$ and the seed is $S = \mathrm{out}(n) - n - W$.
Then $W = [abc]_T + 1$, $S = [ab]_T + c$, and the pre-seed $n - W - S$ equals $[a]_T + b$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 13 (`jis-2025-25.5.4-lem-13`). -/
public theorem trithoff_precolumns (a : List ℕ) (b c n : ℕ)
    (h : IsTribonacciRepr (1 :: c :: b :: a) n) :
    let g₂ : ℤ := tribonacciValue (0 :: 1 :: c :: b :: a)
    let g₃ : ℤ := tribonacciValue (0 :: 0 :: 1 :: c :: b :: a)
    let wall := g₃ - g₂ - n
    let seed := g₂ - n - wall
    wall = tribonacciValue (c :: b :: a) + 1 ∧ seed = tribonacciValue (b :: a) + c ∧
      (n : ℤ) - wall - seed = tribonacciValue a + b := by
  have hn : tribonacciValue (1 :: c :: b :: a) = n := h.2.2
  have hwall := trithoff_precolumns.value_three_cons 0 0 1 (c :: b :: a)
  have hseed := trithoff_precolumns.value_three_cons 0 1 c (b :: a)
  have hpreseed := trithoff_precolumns.value_three_cons 1 c b a
  dsimp only
  omega

end MetaMathlibExt
