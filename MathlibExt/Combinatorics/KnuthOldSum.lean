/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import MathlibExt.Combinatorics.ParityProduct

/-!
# Counting words with an even number of occurrences of a letter

Give the distinguished letter sign `-1` and each other letter sign `1`. The sum of the
signs of all length-`n` words is `2 ^ n`. Adding the total number of words counts each
word with an even number of distinguished letters twice.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.KnuthOldSumWanted

/-- **Weight in Knuth's old sum.** For a natural number $m$, the weight $w(m)$ is the rational
number $(4^m + 2^m)/2$, which equals $(2^m + 1) 2^{m-1}$.

It is the number of words of length $m$ over a four-letter alphabet in which a fixed letter
occurs an even number of times. -/
def knuthOldSumWeight (m : ℕ) : ℚ := ((4 : ℚ) ^ m + (2 : ℚ) ^ m) / 2

/-- **Counting words with an even number of $a$'s.** For every natural number $n$, the number of
words of length $n$ over the four-letter alphabet $\{a, b, c, d\}$ in which the letter $a$ occurs
an even number of times is $(4^n + 2^n)/2$.

Source: Akalu Tefera and Aklilu Zeleke, "Combinatorial Identities
Inspired by Knuth's Old Sum", Lemma 1. -/
theorem card_evenACount_words (n : ℕ) :
    Nat.card {w : Fin n → Fin 4 //
      Even (Finset.univ.filter (fun i => w i = 0)).card} =
        (4 ^ n + 2 ^ n) / 2 := by
  let count (w : Fin n → Fin 4) := (Finset.univ.filter (fun i => w i = 0)).card
  let sign (a : Fin 4) : ℤ := if a = 0 then -1 else 1
  have signedSum : ∑ w : Fin n → Fin 4, (-1 : ℤ) ^ count w = 2 ^ n := by
    calc
      _ = ∑ w : Fin n → Fin 4, ∏ i, sign (w i) := by
        apply Finset.sum_congr rfl
        intro w _
        simp only [sign, ← Finset.prod_filter, Finset.prod_const, count]
      _ = 2 ^ n := by rw [← Fintype.sum_pow, show ∑ a, sign a = 2 by decide]
  have doubled : (4 : ℤ) ^ n + 2 ^ n =
      2 * (Finset.univ.filter (fun w => Even (count w))).card := by
    calc
      _ = ∑ w : Fin n → Fin 4, (1 + (-1 : ℤ) ^ count w) := by
        rw [Finset.sum_add_distrib, signedSum]
        simp
      _ = _ := by
        simp_rw [← ParityProduct.two_mul_evenIndicator, ← Finset.mul_sum]
        simp [ParityProduct.evenIndicator]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  symm
  apply Nat.div_eq_of_eq_mul_right Nat.zero_lt_two
  exact_mod_cast doubled

end MathlibExt.Combinatorics.KnuthOldSumWanted
