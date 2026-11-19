/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.MonotonePowerSumInequalities

/-!
# Tests for power sum inequalities for monotone sequences

* The power sum results on the two-term sequence `x = (1, 2)` with integer
  exponents, where every inequality becomes a numerical one; the lower bound of
  Theorem 2 is an equality on the constant sequence `(3, 3)`, so it is sharp.
* The hypothesis `∀ i, 1 ≤ x i` of Theorem 2(ii) cannot be dropped: the
  constant sequence `(1/4, 1/4)` violates the second inequality.
* The Fibonacci identities of Lemma 1 and `∑_{k=1}^n F_k ^ 2 = F_n F_{n+1}`
  at concrete `n`, checked against direct evaluation by `decide`.
* Theorem 1 at `n = 2` (equality for `r = 5, s = -1`) and at `n = 3`
  (equality for `r = s = 2`, strict inequality for `r = 3, s = 1`).
* The helper inequalities (Lagrange's identity, strict Cauchy–Schwarz,
  weighted Chebyshev) on small inputs.
-/

@[expose] public section

namespace MetaMathlibExtTest.MonotonePowerSumInequalities

open MetaMathlibExt Finset

/-! ### Power sums on concrete sequences -/

/-- Proposition 1 with `α = 2`, `β = 1` on `(1, 2)`: `√5 ≤ 3`. -/
example : √5 ≤ 3 := by
  have h := power_sum_rpow_one_div_le ![(1 : ℝ), 2]
    (fun i => by fin_cases i <;> norm_num) one_pos one_lt_two
  norm_num [Fin.sum_univ_two, ← Real.sqrt_eq_rpow] at h
  exact h

/-- Theorem 2(i) with `α = 2`, `β = 1` on `(1, 2)`: `1 + 4 ≤ (1 + 2) ^ 2`. -/
example : (1 : ℝ) + 4 ≤ (1 + 2) ^ 2 := by
  have h := power_sum_le_rpow_of_le ![(1 : ℝ), 2]
    (fun i => by fin_cases i <;> norm_num) one_pos one_le_two
  norm_num [Fin.sum_univ_two] at h ⊢

/-- The lower bound of Theorem 2 with `r = s = 2` on `(1, 2)`:
`5 * 5 / max (2 * 3) (2 * 3) ≤ 5`. -/
example : (5 : ℝ) * 5 / max (2 * 3) (2 * 3) ≤ 5 := by
  have h := power_sum_mul_div_max_le (n := 1) ![(1 : ℝ), 2]
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    (by norm_num) two_pos two_pos
  norm_num [Fin.sum_univ_two] at h ⊢

/-- The lower bound of Theorem 2 is sharp: on the constant sequence `(3, 3)`
with `r = s = 2` both sides equal `18`. -/
example :
    (∑ i, (![3, 3] : Fin 2 → ℝ) i ^ (2 : ℝ)) *
          (∑ i, (![3, 3] : Fin 2 → ℝ) i ^ (2 : ℝ)) /
        max ((3 : ℝ) ^ ((2 : ℝ) / 2) *
            ∑ i, (![3, 3] : Fin 2 → ℝ) i ^ ((2 : ℝ) / 2))
          ((3 : ℝ) ^ ((2 : ℝ) / 2) *
            ∑ i, (![3, 3] : Fin 2 → ℝ) i ^ ((2 : ℝ) / 2)) =
      ∑ i, (![3, 3] : Fin 2 → ℝ) i ^ (((2 : ℝ) + 2) / 2) := by
  norm_num [Fin.sum_univ_two]

/-- Theorem 2(ii) with `α = 1`, `β = 2` on `(1, 2)`:
`3 ≤ 2 √(5 / 2) ≤ 5`. -/
example : (3 : ℝ) ≤ 2 * √(5 / 2) ∧ 2 * √(5 / 2) ≤ 5 := by
  have h := power_sum_le_card_mul_rpow_of_lt (n := 1) ![(1 : ℝ), 2]
    (fun i => by fin_cases i <;> norm_num) one_pos one_lt_two
  have h1 : ∀ i, 1 ≤ (![(1 : ℝ), 2] : Fin 2 → ℝ) i := fun i => by
    fin_cases i <;> norm_num
  refine ⟨?_, ?_⟩
  · have := h.1
    norm_num [Fin.sum_univ_succ, ← Real.sqrt_eq_rpow] at this ⊢
    linarith
  · have := h.2 h1
    norm_num [Fin.sum_univ_succ, ← Real.sqrt_eq_rpow] at this ⊢
    linarith

/-- The hypothesis `∀ i, 1 ≤ x i` in the second part of Theorem 2(ii) is
needed: for `x = (1/4, 1/4)`, `α = 1` and `β = 2`,
`2 ((1/16 + 1/16) / 2) ^ (1 / 2) = 1/2 > 1/8 = 1/16 + 1/16`. -/
example :
    ¬ ((1 : ℝ) + 1) * (((1 / 4 : ℝ) ^ (2 : ℝ) + (1 / 4 : ℝ) ^ (2 : ℝ)) /
        ((1 : ℝ) + 1)) ^ ((1 : ℝ) / 2) ≤
      (1 / 4 : ℝ) ^ (2 : ℝ) + (1 / 4 : ℝ) ^ (2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  norm_num
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- Theorem 4(ii) with weights `(1, 2)`, `α = 1`, `β = 2` on `(1, 2)`:
`5 ≤ 3 √3 ≤ 9`. -/
example : (5 : ℝ) ≤ 3 * √3 ∧ 3 * √3 ≤ 9 := by
  have h := weighted_power_sum_le_mul_rpow_of_lt (n := 1) ![(1 : ℝ), 2]
    ![1, 2] (fun i => by fin_cases i <;> norm_num)
    (fun i => by fin_cases i <;> norm_num) one_pos one_lt_two
  have h1 : ∀ i, 1 ≤ (![(1 : ℝ), 2] : Fin 2 → ℝ) i := fun i => by
    fin_cases i <;> norm_num
  refine ⟨?_, ?_⟩
  · have := h.1
    norm_num [Fin.sum_univ_succ, ← Real.sqrt_eq_rpow] at this ⊢
    linarith
  · have := h.2 h1
    norm_num [Fin.sum_univ_succ, ← Real.sqrt_eq_rpow] at this ⊢
    linarith

/-! ### Fibonacci sums -/

example : ∑ k ∈ Icc 1 10, Nat.fib k ^ 2 = 4895 := by
  rw [Nat.sum_Icc_fib_sq]
  decide

example : ∑ k ∈ Icc 1 10, Nat.fib k ^ 2 = Nat.fib 10 * Nat.fib 11 := by
  decide

/-- Lemma 1 at `n = 6`, with the right sides evaluated. -/
example :
    (∑ i ∈ Icc (1 : ℕ) 6, (Nat.fib (2 * i - 1) : ℤ)) = 144 ∧
    (∑ i ∈ Icc (1 : ℕ) 6, (Nat.fib (2 * i) : ℤ)) = 232 ∧
    (∑ i ∈ Icc (1 : ℕ) 6, (i : ℤ) * Nat.fib i) = 94 ∧
    (∑ i ∈ Icc (1 : ℕ) 6, (Nat.fib i : ℤ) * Nat.fib (3 * i)) = 24232 ∧
    (∑ i ∈ Icc (1 : ℕ) 6, ((6 : ℕ).choose i : ℤ) * Nat.fib i) = 144 := by
  obtain ⟨hb, hc, hd, he, hg⟩ := fib_power_sum_identities (n := 6) (by norm_num)
  have h12 : Nat.fib 12 = 144 := by decide
  have h13 : Nat.fib 13 = 233 := by decide
  have h8 : Nat.fib 8 = 21 := by decide
  have h9 : Nat.fib 9 = 34 := by decide
  have h6 : Nat.fib 6 = 8 := by decide
  have h7 : Nat.fib 7 = 13 := by decide
  rw [h12] at hb hg
  rw [h13] at hc
  rw [h8, h9] at hd
  rw [h6, h7, h13] at he
  exact ⟨hb, by rw [hc]; norm_num, by rw [hd]; norm_num, by rw [he]; norm_num,
    hg⟩

/-- Direct evaluation of Lemma 1 (b)–(e), (g) at `n = 6`. -/
example :
    ∑ i ∈ Icc 1 6, Nat.fib (2 * i - 1) = 144 ∧
    ∑ i ∈ Icc 1 6, Nat.fib (2 * i) = 232 ∧
    ∑ i ∈ Icc 1 6, i * Nat.fib i = 94 ∧
    ∑ i ∈ Icc 1 6, Nat.fib i * Nat.fib (3 * i) = 24232 ∧
    ∑ i ∈ Icc 1 6, (6 : ℕ).choose i * Nat.fib i = 144 := by
  decide

/-- The shifted binomial identity `∑ binom(n, i) F_{i+m} = F_{2n+m}` at
`n = 4`, `m = 3`. -/
example : ∑ i ∈ range 5, (4 : ℕ).choose i * Nat.fib (i + 3) = 89 := by
  rw [Nat.sum_range_choose_mul_fib_add]
  decide

example : ∑ i ∈ range 5, (4 : ℕ).choose i * Nat.fib (i + 3) =
    Nat.fib (2 * 4 + 3) := by
  decide

/-- Theorem 3(i) with `α = 4` at `n = 3`: `1 + 1 + 16 ≤ (2 * 3) ^ 2`. -/
example : (1 : ℝ) + 1 + 16 ≤ (2 * 3) ^ 2 := by
  have h := sum_fib_rpow_le_of_two_le (n := 3) (by norm_num) (α := 4)
    (by norm_num)
  rw [show Icc 1 3 = {1, 2, 3} by rfl] at h
  norm_num [Nat.fib_add_two] at h ⊢

/-- Theorem 3(ii) with `α = 1` at `n = 3`:
`1 + 1 + 2 ≤ 3 √2 ≤ 6`. -/
example : (4 : ℝ) ≤ 3 * √2 ∧ 3 * √2 ≤ 6 := by
  have h := sum_fib_rpow_le_card_mul_rpow (n := 3) (by norm_num) (α := 1)
    one_pos one_lt_two
  rw [show Icc 1 3 = {1, 2, 3} by rfl] at h
  norm_num [Nat.fib_add_two, ← Real.sqrt_eq_rpow] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ### Theorem 1 and its equality case -/

/-- At `n = 2` equality holds for every admissible `r, s`, e.g. `r = 5`,
`s = -1`. -/
example :
    (∑ k ∈ Icc 1 2, (Nat.fib k : ℝ) ^ (5 : ℝ)) *
        ∑ k ∈ Icc 1 2, (Nat.fib k : ℝ) ^ (-1 : ℝ) =
      ((Nat.fib 2 : ℝ) * Nat.fib 3) ^ 2 :=
  ((sum_fib_rpow_mul_sum_fib_rpow_ge (n := 2) (by norm_num)
    (by norm_num)).2.mpr (Or.inr (Or.inl rfl)))

/-- At `n = 3` and `r = s = 2` equality holds:
`(1 + 1 + 4) ^ 2 = (2 * 3) ^ 2`. -/
example :
    (∑ k ∈ Icc 1 3, (Nat.fib k : ℝ) ^ (2 : ℝ)) *
        ∑ k ∈ Icc 1 3, (Nat.fib k : ℝ) ^ (2 : ℝ) =
      ((Nat.fib 3 : ℝ) * Nat.fib 4) ^ 2 :=
  ((sum_fib_rpow_mul_sum_fib_rpow_ge (n := 3) (by norm_num)
    (by norm_num)).2.mpr (Or.inr (Or.inr ⟨le_rfl, rfl, rfl⟩)))

/-- At `n = 3`, `r = 3` and `s = 1` the inequality is strict:
`(1 + 1 + 8) (1 + 1 + 2) = 40 > 36 = (2 * 3) ^ 2`. -/
example :
    ((Nat.fib 3 : ℝ) * Nat.fib 4) ^ 2 <
      (∑ k ∈ Icc 1 3, (Nat.fib k : ℝ) ^ (3 : ℝ)) *
        ∑ k ∈ Icc 1 3, (Nat.fib k : ℝ) ^ (1 : ℝ) := by
  obtain ⟨hle, hiff⟩ := sum_fib_rpow_mul_sum_fib_rpow_ge (n := 3)
    (by norm_num) (r := 3) (s := 1) (by norm_num)
  refine lt_of_le_of_ne hle fun h => ?_
  rcases hiff.mp h.symm with h | h | ⟨-, h, -⟩ <;> norm_num at h

/-! ### Helper inequalities -/

/-- Lagrange's identity for `f = (1, 2)`, `g = (3, 5)` over `ℤ`:
`2 ((1 + 4) (9 + 25) - (3 + 10) ^ 2) = 2 (1 * 5 - 2 * 3) ^ 2 = 2`. -/
example :
    ∑ i : Fin 2, ∑ j : Fin 2,
        ((![1, 2] : Fin 2 → ℤ) i * (![3, 5] : Fin 2 → ℤ) j -
          (![1, 2] : Fin 2 → ℤ) j * (![3, 5] : Fin 2 → ℤ) i) ^ 2 = 2 := by
  rw [Finset.sum_sum_mul_sub_mul_sq]
  decide

/-- Strict Cauchy–Schwarz for the non-proportional `(1, 2)` and `(3, 5)`
(`1 * 5 ≠ 2 * 3`): `13 ^ 2 < 5 * 34`. -/
example :
    (∑ k, (![1, 2] : Fin 2 → ℤ) k * (![3, 5] : Fin 2 → ℤ) k) ^ 2 <
      (∑ k, (![1, 2] : Fin 2 → ℤ) k ^ 2) *
        ∑ k, (![3, 5] : Fin 2 → ℤ) k ^ 2 :=
  Finset.sum_mul_sq_lt_sq_mul_sq univ _ _ (i := 0) (j := 1) (mem_univ _)
    (mem_univ _) (by decide)

/-- Weighted Chebyshev for `f = g = (1, 2)` and weights `(1, 3)`:
`7 * 7 ≤ 4 * 13`. -/
example : (7 : ℝ) * 7 ≤ 4 * 13 := by
  have h := MonovaryOn.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul
    (s := univ) (f := (![1, 2] : Fin 2 → ℝ)) (g := ![1, 2]) (w := ![1, 3])
    (fun i _ j _ hij => hij.le) (fun i _ => by fin_cases i <;> norm_num)
  norm_num [Fin.sum_univ_two] at h
  linarith

/-- `Real.sum_rpow_le_rpow_sum` with `p = 3` on `(1, 2)`:
`1 + 8 ≤ 27`. -/
example : (1 : ℝ) + 8 ≤ 27 := by
  have h := Real.sum_rpow_le_rpow_sum univ (![(1 : ℝ), 2] : Fin 2 → ℝ)
    (fun i _ => by fin_cases i <;> norm_num) (p := 3) (by norm_num)
  norm_num [Fin.sum_univ_two] at h ⊢

/-! ### Axioms -/

#print axioms Finset.sum_sum_mul_sub_mul_sq
#print axioms Finset.sum_mul_sq_lt_sq_mul_sq
#print axioms MonovaryOn.sum_mul_mul_sum_mul_le_sum_mul_sum_mul_mul
#print axioms Real.sum_rpow_le_rpow_sum
#print axioms Real.sum_rpow_le_rpow_sum_rpow
#print axioms Real.sum_mul_rpow_le_mul_rpow_div
#print axioms Real.mul_rpow_div_le_sum_mul_rpow
#print axioms Real.sum_mul_rpow_mul_sum_mul_rpow_le
#print axioms Real.sum_mul_rpow_mul_sum_mul_rpow_div_max_le
#print axioms Nat.sum_Icc_fib_sq
#print axioms Nat.sum_Icc_fib_two_mul_sub_one
#print axioms Nat.sum_Icc_fib_two_mul_add_one
#print axioms Nat.sum_Icc_mul_fib_add_fib
#print axioms Nat.sum_Icc_fib_mul_fib_three_mul
#print axioms Nat.sum_range_choose_mul_fib_add
#print axioms Nat.sum_Icc_choose_mul_fib
#print axioms Nat.sum_Icc_fib_rpow_two
#print axioms power_sum_rpow_one_div_le
#print axioms power_sum_mul_div_max_le
#print axioms power_sum_le_rpow_of_le
#print axioms power_sum_le_card_mul_rpow_of_lt
#print axioms sum_fib_rpow_le_of_two_le
#print axioms sum_fib_rpow_le_card_mul_rpow
#print axioms weighted_power_sum_mul_div_max_le
#print axioms weighted_power_sum_le_mul_rpow_of_lt
#print axioms weighted_sum_fib_rpow_le_mul_rpow
#print axioms fib_power_sum_identities
#print axioms sum_fib_rpow_mul_sum_fib_rpow_ge

end MetaMathlibExtTest.MonotonePowerSumInequalities
