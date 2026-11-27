/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.MeteredParkingFunctions
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.OneMeteredParkingFunctions

/-!
# A binomial sum for diagonal 1-metered parking counts

After reversing the sum and taking complementary binomial coefficients, two applications of
Pascal's rule give the Lucas recurrence. Its roots identify the sum with the parking-count
Binet formula.

## References

* Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
  Functions*, INTEGERS 25 (2025), Article A73, pp. 1–37, Corollaries 4 and 5 (p. 16) and
  Theorem 2 (p. 15). <https://math.colgate.edu/~integers/z73/z73.pdf>
* OEIS Foundation Inc., *The On-Line Encyclopedia of Integer Sequences*, A097690,
  “Numerators of the continued fraction n-1/(n-1/...) [n times]”; the equivalent binomial
  sums in the entry are due to Seiichi Manyama (2021). <https://oeis.org/A097690>
* Theodore J. Rivlin, *Chebyshev Polynomials: From Approximation Theory to Algebra and Number
  Theory*, 2nd ed., Wiley (1990), Chapter 1 (the second-kind recurrence discussed by the paper).
* Paulo Ribenboim, *The New Book of Prime Number Records*, Springer (1996), and *My Numbers,
  My Friends: Popular Lectures on Number Theory*, Springer (2000), Chapter 1 (the paper's
  references for first-kind Lucas sequences).
-/

namespace MetaMathlibExt

open Finset

namespace MeteredParkingDiagonalChoose

private def chooseCoeff (m k : ℕ) : ℕ := (m + k + 1).choose (2 * k + 1)

private noncomputable def chooseSum (x : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range (m + 1), (chooseCoeff m k : ℝ) * x ^ k

private theorem chooseSum_extend (x : ℝ) {m r : ℕ} (hr : m + 1 ≤ r) :
    chooseSum x m = ∑ k ∈ range r, (chooseCoeff m k : ℝ) * x ^ k := by
  apply sum_subset (range_mono hr)
  intro k _ hk
  have hlt : m + k + 1 < 2 * k + 1 := by
    rw [mem_range] at hk
    omega
  simp [chooseCoeff, Nat.choose_eq_zero_of_lt hlt]

-- The second difference of a binomial coefficient in its top index lowers its bottom index by two.
private theorem chooseCoeff_add_two (m k : ℕ) :
    chooseCoeff (m + 2) (k + 1) + chooseCoeff m (k + 1) =
      2 * chooseCoeff (m + 1) (k + 1) + chooseCoeff (m + 1) k := by
  let N := m + k + 2
  let r := 2 * k + 1
  have h₂ : chooseCoeff (m + 2) (k + 1) = (N + 2).choose (r + 2) := by
    unfold chooseCoeff N r
    congr 1
    omega
  have h₁ : chooseCoeff (m + 1) (k + 1) = (N + 1).choose (r + 2) := by
    unfold chooseCoeff N r
    congr 1
    omega
  have h₀ : chooseCoeff m (k + 1) = N.choose (r + 2) := by
    unfold chooseCoeff N r
    congr 1
  have h : chooseCoeff (m + 1) k = N.choose r := by
    unfold chooseCoeff N r
    congr 1
    omega
  rw [h₂, h₁, h₀, h, Nat.choose_succ_succ' (N + 1) (r + 1),
    Nat.choose_succ_succ' N (r + 1), Nat.choose_succ_succ' N r]
  rw [show r + 1 + 1 = r + 2 by omega]
  omega

private theorem chooseSum_add_two (x : ℝ) (m : ℕ) :
    chooseSum x (m + 2) + chooseSum x m = (x + 2) * chooseSum x (m + 1) := by
  let f (r k : ℕ) : ℝ := (chooseCoeff r k : ℝ) * x ^ k
  have hsplit {r : ℕ} (hr : r + 1 ≤ m + 3) :
      chooseSum x r = (∑ k ∈ range (m + 2), f r (k + 1)) + f r 0 := by
    rw [chooseSum_extend x hr, sum_range_succ']
  have hzero : f (m + 2) 0 + f m 0 = 2 * f (m + 1) 0 := by
    simp [f, chooseCoeff, Nat.cast_add]
    ring
  have hsummand (k : ℕ) : f (m + 2) (k + 1) + f m (k + 1) =
      2 * f (m + 1) (k + 1) + x * f (m + 1) k := by
    have hc : (chooseCoeff (m + 2) (k + 1) : ℝ) + chooseCoeff m (k + 1) =
        2 * chooseCoeff (m + 1) (k + 1) + chooseCoeff (m + 1) k := by
      exact_mod_cast chooseCoeff_add_two m k
    simp only [f, pow_succ]
    linear_combination (x ^ k * x) * hc
  have hsum : (∑ k ∈ range (m + 2), f (m + 2) (k + 1)) +
      (∑ k ∈ range (m + 2), f m (k + 1)) =
      2 * (∑ k ∈ range (m + 2), f (m + 1) (k + 1)) + x * chooseSum x (m + 1) := by
    rw [← sum_add_distrib]
    simp_rw [hsummand, sum_add_distrib, ← mul_sum]
    rfl
  rw [hsplit (r := m + 2) (by omega), hsplit (r := m) (by omega)]
  linear_combination hsum + hzero - 2 * hsplit (r := m + 1) (by omega)

private theorem chooseSum_mul_eq_pow_sub_pow (x s : ℝ) (hsq : s ^ 2 = x ^ 2 - 4) (m : ℕ) :
    chooseSum (x - 2) m * s = ((x + s) / 2) ^ (m + 1) - ((x - s) / 2) ^ (m + 1) := by
  let a := (x + s) / 2
  let b := (x - s) / 2
  have ha : a ^ 2 = x * a - 1 := by
    dsimp [a]
    linear_combination (1 / 4) * hsq
  have hb : b ^ 2 = x * b - 1 := by
    dsimp [b]
    linear_combination (1 / 4) * hsq
  have h (k : ℕ) : chooseSum (x - 2) k * s = a ^ (k + 1) - b ^ (k + 1) ∧
      chooseSum (x - 2) (k + 1) * s = a ^ (k + 2) - b ^ (k + 2) := by
    induction k with
    | zero =>
      constructor <;> norm_num [chooseSum, chooseCoeff, sum_range_succ, a, b] <;> ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : chooseSum (x - 2) (k + 2) + chooseSum (x - 2) k =
          x * chooseSum (x - 2) (k + 1) := by
        simpa only [sub_add_cancel] using chooseSum_add_two (x - 2) k
      linear_combination s * hr + x * ih.2 - ih.1 - a ^ (k + 1) * ha + b ^ (k + 1) * hb
  exact (h m).1

private theorem binet_coefficient {x s : ℝ} (hs : s ≠ 0) (hsq : s ^ 2 = x ^ 2 - 4) :
    (x * (x + s) - 2) / (x * (x + s) - 4) = (x + s) / (2 * s) := by
  have hsum : x + s ≠ 0 := by
    intro h
    have hs' : s = -x := by linarith
    rw [hs', neg_sq] at hsq
    linarith
  have hden : x * (x + s) - 4 = s * (x + s) := by linear_combination -hsq
  have hden0 : x * (x + s) - 4 ≠ 0 := hden.symm ▸ mul_ne_zero hs hsum
  rw [div_eq_div_iff hden0 (mul_ne_zero (by norm_num) hs)]
  linear_combination x * hsq

private theorem count_eq_chooseSum {m n : ℕ} (hm : m ≤ n + 1) (hn : 2 < n) :
    (meteredParkingCount 1 m n : ℝ) = chooseSum ((n : ℝ) - 2) m := by
  let x := (n : ℝ)
  let s := Real.sqrt (x ^ 2 - 4)
  have hx : 3 ≤ x := by
    change (3 : ℝ) ≤ (n : ℝ)
    exact_mod_cast (show 3 ≤ n from hn)
  have hpos : 0 < x ^ 2 - 4 := by nlinarith
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsq : s ^ 2 = x ^ 2 - 4 := Real.sq_sqrt hpos.le
  have hB : (x * (x - s) - 2) / (x * (x - s) - 4) = -(x - s) / (2 * s) := by
    simpa only [sub_eq_add_neg, mul_neg, div_neg, neg_div] using
      (binet_coefficient (x := x) (neg_ne_zero.mpr hs) (by simpa only [neg_sq] using hsq))
  calc
    (meteredParkingCount 1 m n : ℝ) =
        (x * (x + s) - 2) / (x * (x + s) - 4) * ((x + s) / 2) ^ m +
        (x * (x - s) - 2) / (x * (x - s) - 4) * ((x - s) / 2) ^ m :=
      meteredParkingCount_one_binet hm hn
    _ = chooseSum (x - 2) m := by
      rw [binet_coefficient hs hsq, hB]
      apply mul_right_cancel₀ hs
      rw [chooseSum_mul_eq_pow_sub_pow x s hsq]
      field_simp [hs]
      ring

end MeteredParkingDiagonalChoose

open MeteredParkingDiagonalChoose

/-- **1-metered parking functions with as many cars as spots.** For every natural number
$n > 2$, the number of $1$-metered $(n, n)$-parking functions is
$$\mathrm{mpf}_{n,n}(1) = \sum_{k=0}^{n} (n-2)^{n-k} \binom{2n+1-k}{k}.$$

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 4 (`integers-2025-A73-cor-4`). -/
public theorem meteredParkingCount_one_diag {n : ℕ} (hn : 2 < n) :
    meteredParkingCount 1 n n =
      ∑ k ∈ Finset.range (n + 1), (n - 2) ^ (n - k) * (2 * n + 1 - k).choose k := by
  have hn₂ : 2 ≤ n := by omega
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [count_eq_chooseSum (by omega : n ≤ n + 1) hn, Nat.cast_sub hn₂, Nat.cast_ofNat]
  unfold chooseSum
  rw [← sum_range_reflect (fun k => ((n : ℝ) - 2) ^ (n - k) *
    ((2 * n + 1 - k).choose k : ℝ))]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simpa only [mem_range, Nat.lt_succ_iff] using hk
  rw [Nat.add_sub_cancel, show n - (n - k) = k by omega, mul_comm]
  congr 1
  unfold chooseCoeff
  rw [show 2 * n + 1 - (n - k) = n + k + 1 by omega,
    ← Nat.choose_symm (show n - k ≤ n + k + 1 by omega),
    show n + k + 1 - (n - k) = 2 * k + 1 by omega]

end MetaMathlibExt
