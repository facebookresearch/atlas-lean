/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! # The binomial-sum formula for the Lucas sequence of the first kind -/

namespace MetaMathlibExt

-- Index the summands for `lucasU P (n + 1)` by `n`, not `n + 1`.
private def lucasChooseTerm (P : LucasSequenceParams) (n i : ℕ) : ℤ :=
  (-P.q) ^ i * ((n - i).choose i : ℤ) * P.p ^ (n - 2 * i)

private def lucasChooseSum (P : LucasSequenceParams) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n / 2 + 1), lucasChooseTerm P n i

private theorem lucasChooseTerm_zero (P : LucasSequenceParams) (n : ℕ) :
    lucasChooseTerm P n 0 = P.p ^ n := by
  simp [lucasChooseTerm]

private theorem lucasChooseTerm_eq_zero (P : LucasSequenceParams) {n i : ℕ} (h : n < 2 * i) :
    lucasChooseTerm P n i = 0 := by
  simp [lucasChooseTerm, Nat.choose_eq_zero_of_lt (show n - i < i by omega)]

private theorem lucasChooseTerm_succ (P : LucasSequenceParams) (n i : ℕ) :
    lucasChooseTerm P (n + 2) (i + 1) =
      P.p * lucasChooseTerm P (n + 1) (i + 1) + (-P.q) * lucasChooseTerm P n i := by
  by_cases h : n < 2 * i
  · rw [lucasChooseTerm_eq_zero P (n := n + 2) (i := i + 1) (by omega),
      lucasChooseTerm_eq_zero P (n := n + 1) (i := i + 1) (by omega),
      lucasChooseTerm_eq_zero P h]
    simp
  · have hPascal : (n + 2 - (i + 1)).choose (i + 1) =
        (n - i).choose i + (n - i).choose (i + 1) := by
      rw [show n + 2 - (i + 1) = n - i + 1 by omega, Nat.choose_succ_succ']
    unfold lucasChooseTerm
    rw [hPascal, Nat.cast_add, show n + 1 - (i + 1) = n - i by omega,
      show n + 2 - 2 * (i + 1) = n - 2 * i by omega, pow_succ (-P.q) i]
    by_cases hi : 2 * i < n
    · rw [show n - 2 * i = (n + 1 - 2 * (i + 1)) + 1 by omega, pow_succ P.p]
      ring
    · -- At the even boundary only the shifted second sum contributes.
      rw [Nat.choose_eq_zero_of_lt (show n - i < i + 1 by omega), Nat.cast_zero]
      ring

private theorem lucasChooseSum_add_two (P : LucasSequenceParams) (n : ℕ) :
    lucasChooseSum P (n + 2) = P.p * lucasChooseSum P (n + 1) + (-P.q) * lucasChooseSum P n := by
  -- Pad the shorter sum so both can split off the leading term at index zero.
  have extend : lucasChooseSum P (n + 1) =
      ∑ i ∈ Finset.range ((n + 2) / 2 + 1), lucasChooseTerm P (n + 1) i := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i _ hi
    rw [Finset.mem_range] at hi
    exact lucasChooseTerm_eq_zero P (by omega)
  unfold lucasChooseSum at extend ⊢
  rw [extend, Finset.sum_range_succ' (lucasChooseTerm P (n + 2)),
    Finset.sum_range_succ' (lucasChooseTerm P (n + 1))]
  simp only [lucasChooseTerm_succ, Finset.sum_add_distrib, ← Finset.mul_sum, lucasChooseTerm_zero]
  rw [show (n + 2) / 2 = n / 2 + 1 by omega, show n + 2 = (n + 1) + 1 by rfl,
    pow_succ P.p (n + 1)]
  ring

private theorem lucasU_succ_eq_lucasChooseSum (P : LucasSequenceParams) (n : ℕ) :
    lucasU P (n + 1) = lucasChooseSum P n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lucasU, lucasChooseSum, lucasChooseTerm_zero]
  | one => simp [lucasU, lucasChooseSum, lucasChooseTerm_zero]
  | more n ih₀ ih₁ =>
    rw [show n + 2 + 1 = (n + 1) + 2 by rfl, lucasU_add_two, ih₀, ih₁]
    rw [lucasChooseSum_add_two, neg_mul, sub_eq_add_neg]

/-- **Binomial-sum formula for the Lucas sequence $U$.** Let $x$ and $y \neq 0$ be integers and
let $(U_n)$ be the Lucas sequence with parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and
$U_{n+2} = x U_{n+1} - y U_n$. Then for every $r \geq 1$,
$$
U_r = \sum_{i=0}^{\lfloor (r-1)/2 \rfloor} (-y)^i \binom{r-i-1}{i} x^{r-2i-1}.
$$

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (vii) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem lucasU_eq_sum_choose (P : LucasSequenceParams) {r : ℕ} (hr : 1 ≤ r) :
    lucasU P r = ∑ i ∈ Finset.range ((r - 1) / 2 + 1),
      (-P.q) ^ i * ((r - i - 1).choose i : ℤ) * P.p ^ (r - 2 * i - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have sub_succ (k : ℕ) : n + 1 - k - 1 = n - k := by omega
  simpa only [lucasChooseSum, lucasChooseTerm, sub_succ, Nat.succ_sub_one] using
    lucasU_succ_eq_lucasChooseSum P n

end MetaMathlibExt
