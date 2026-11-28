/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ArithmeticFunction.HBCHalfPrimeProductBounds

/-!
# The three-quarter product bound for HBC-admissible tuples

Let $a,d$ be coprime positive integers and $y_1 < \cdots < y_k$ positive integers, with $k \ge 2$.
The HBC-admissibility inequalities
$\prod_{i=1}^{k}(1-1/y_i) \le a/(a+d) < \prod_{i=1}^{k-1}(1-1/y_i)$ force the first term to
exceed $\alpha = (a+d)/d$. If $y_1 \ne \lfloor 1+\alpha\rfloor$, it then exceeds $1+\alpha$, so
Stone's prefix estimate cannot use a prefix of length one. A prefix of length at least two allows
the factor $d$ to be absorbed using the base $(a+d)/d^{3/4}$ in the product bound.

## References

* Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers – Part I*, INTEGERS 24 (2024),
  Article A114, pp. 1–38, Corollary 2; the argument uses Theorem 1 and Remark 4.
* The prefix estimate, range bound, and reindexing used in `hbcAdmissible_prod_le_sqrt` are from
  `MathlibExt.NumberTheory.ArithmeticFunction.HBCHalfPrimeProductBounds`.
-/

namespace MetaMathlibExt

open Finset

/-- **Stone's $d^{3/4}$ product bound for HBC-admissible tuples.** Let $a$ and $d$ be coprime
positive integers, let $k \ge 2$, and let $y_1 < y_2 < \dots < y_k$ be positive integers with
$\prod_{i=1}^{k} (1 - 1/y_i) \le a/(a + d) < \prod_{i=1}^{k-1} (1 - 1/y_i)$ and
$y_1 \ne \lfloor 1 + (a + d)/d \rfloor$. Put $\beta = (a + d)/d^{3/4}$. Then
$a \prod_{i=1}^{k} y_i \le \beta^{2^k} - \beta^{2^{k-1}}$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Corollary 2. -/
public theorem hbcAdmissible_prod_le_of_ne_floor (a d k : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcop : Nat.Coprime a d) (hk : 2 ≤ k) (y : ℕ → ℕ) (hy0 : 0 < y 1)
    (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ (a : ℝ) / (a + d))
    (hlt : (a : ℝ) / (a + d) < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ)))
    (hy1 : y 1 ≠ ⌊1 + ((a : ℝ) + d) / d⌋₊) :
    a * ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
      ((a + d) / (d : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 ^ k -
        ((a + d) / (d : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 ^ (k - 1) := by
  have _ := hcop
  have hI (f : ℕ → ℝ) (n : ℕ) : ∏ i ∈ Icc 1 n, f i = ∏ i ∈ range n, f (1 + i) := by
    rw [← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let α : ℝ := ((a : ℝ) + d) / d
  have hαd : (d : ℝ) * (α - 1) = a := by dsimp [α]; field_simp; ring
  have hα : 1 < α := by dsimp [α]; rw [lt_div_iff₀ hdR]; linarith
  have hr : (a : ℝ) / (a + d) = 1 - 1 / α := by dsimp [α]; field_simp; ring
  obtain ⟨κ, hκ1, hκk, hpre, hproper, hfull⟩ :=
    hbcAdmissible_exists_prefix_bound k a d (fun i => y (1 + i)) ha hd (by omega)
      (fun i hi => by simpa only [Nat.add_assoc] using hmono (1 + i) (by omega) (by omega))
      (by simpa using hy0) (by simpa only [hI] using hle) (by simpa only [hI] using hlt)
  change (a : ℝ) * (∏ i ∈ range κ, (y (1 + i) : ℝ)) + d ≤ d * α ^ 2 ^ κ at hpre
  -- The strict prefix inequality forces the first term to exceed `α`.
  have hyR : (0 : ℝ) < y 1 := by exact_mod_cast hy0
  have hproduct : (a : ℝ) / (a + d) < 1 - 1 / (y 1 : ℝ) := by
    rw [hI, show k - 1 = (k - 2) + 1 by omega, prod_range_succ', Nat.add_zero] at hlt
    exact hlt.trans_le (mul_le_of_le_one_left (Nat.one_sub_one_div_cast_nonneg _) (prod_le_one₀
      (fun i _ => Nat.one_sub_one_div_cast_nonneg _) (fun i _ => sub_le_self _ (by positivity))))
  have hyα : α < (y 1 : ℝ) := by
    by_contra! h
    rw [hr] at hproduct
    linarith [one_div_le_one_div_of_le hyR h]
  have hκ2 : 2 ≤ κ := by
    by_contra! h
    have hκ : κ = 1 := by omega
    rw [hκ, prod_range_one, Nat.add_zero, pow_one] at hpre
    have hy_le : (y 1 : ℝ) ≤ 1 + α := by
      apply le_of_mul_le_mul_left _ haR
      nlinarith only [hpre, hαd, congrArg (fun t : ℝ => t * (1 + α)) hαd]
    apply hy1
    symm
    exact (Nat.floor_eq_iff (by positivity)).mpr ⟨hy_le, by linarith⟩
  let t : ℝ := (d : ℝ) ^ ((1 : ℝ) / 4)
  have ht1 : 1 ≤ t := Real.one_le_rpow hd1 (by norm_num)
  have ht4 : t ^ 4 = d := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdR.le]
    norm_num
  let β : ℝ := ((a : ℝ) + d) / (d : ℝ) ^ ((3 : ℝ) / 4)
  have hβ : β = α * t := by
    dsimp [β, α, t]
    rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) hdR.ne', mul_assoc,
      ← Real.rpow_add hdR, show (1 : ℝ) / 4 + 3 / 4 = 1 by norm_num, Real.rpow_one]
  have hc : (d : ℝ) * α ^ 2 ^ κ ≤ β ^ 2 ^ κ := by
    rw [hβ, mul_pow, mul_comm (d : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← ht4]
    exact pow_le_pow_right₀ ht1 (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hκ2)
  rw [hI (fun i => (y i : ℝ)) k]
  exact hbcAdmissible_range_bound hκ1 hκk hd1 hα.le hproper hfull hc

end MetaMathlibExt
