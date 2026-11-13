/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MedianGenocchiNumber
import MathlibExt.Combinatorics.Enumerative.EulerSeidelMatrix
import MathlibExt.NumberTheory.GenocchiBernoulli
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Ring

open scoped BigOperators

/-!
# Divisibility of median Genocchi numbers

This file proves Chen's power-of-two divisibility and modulo-six congruence for
the odd-indexed median Genocchi numbers. It connects their Bernoulli definition
to a finite Euler-Seidel and Legendre-Stirling table, then normalizes that table
over the integers.
-/

namespace MetaMathlibExt

@[expose]
public section

private theorem mgen_coeff_mul_egf (f g : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.mk (fun k => f k / (k.factorial : ℚ)) *
        PowerSeries.mk (fun k => g k / (k.factorial : ℚ))) =
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * f k * g (n - k)) /
        (n.factorial : ℚ) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i _ * PowerSeries.coeff j _) n,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  simp only [PowerSeries.coeff_mk]
  have hkn : k ≤ n := by omega
  have hchoose : ((n.choose k : ℕ) : ℚ) * ((k.factorial : ℕ) : ℚ) *
      ((((n - k).factorial : ℕ)) : ℚ) = ((n.factorial : ℕ) : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hd1 : ((k.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hd2 : ((((n - k).factorial : ℕ)) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hfact : ((n.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  linear_combination (-(f k * g (n - k))) * hchoose

private theorem mgen_exp_eq_mk : PowerSeries.exp ℚ =
    PowerSeries.mk fun k => 1 / (k.factorial : ℚ) := by
  ext n
  rw [PowerSeries.coeff_exp, PowerSeries.coeff_mk, Algebra.algebraMap_self_apply]

private theorem mgen_genocchi_eq_mk : genocchiPowerSeries =
    PowerSeries.mk fun k => genocchiNumberViaBernoulli k / (k.factorial : ℚ) := by
  ext n
  rw [PowerSeries.coeff_mk, genocchiNumberViaBernoulli_eq_genocchiNumber,
    genocchiNumber_eq]
  have hfact : ((n.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp

private theorem mgen_genocchi_mul_exp :
    genocchiPowerSeries * PowerSeries.exp ℚ = 2 * PowerSeries.X - genocchiPowerSeries := by
  have hG : genocchiPowerSeries * (PowerSeries.exp ℚ + 1) = 2 * PowerSeries.X := by
    rw [genocchiPowerSeries_eq, mul_assoc, PowerSeries.inv_mul_cancel]
    · ring
    · simp [map_add, PowerSeries.constantCoeff_exp]
  calc
    genocchiPowerSeries * PowerSeries.exp ℚ
        = genocchiPowerSeries * (PowerSeries.exp ℚ + 1) - genocchiPowerSeries := by ring
    _ = 2 * PowerSeries.X - genocchiPowerSeries := by rw [hG]

private theorem mgen_genocchi_reflection_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) *
      genocchiNumberViaBernoulli k) =
      (-1 : ℚ) ^ (n + 1) * genocchiNumberViaBernoulli n := by
  have hcoeff := congrArg (PowerSeries.coeff n) mgen_genocchi_mul_exp
  rw [mgen_genocchi_eq_mk, mgen_exp_eq_mk,
    mgen_coeff_mul_egf (fun k => genocchiNumberViaBernoulli k) (fun _ => 1) n] at hcoeff
  rw [map_sub] at hcoeff
  simp only [mul_one, PowerSeries.coeff_mk] at hcoeff
  have h2 : (2 : PowerSeries ℚ) = PowerSeries.C 2 := (map_ofNat _ _).symm
  rw [h2, PowerSeries.coeff_C_mul] at hcoeff
  simp only [PowerSeries.coeff_X] at hcoeff
  have hfact : ((n.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  by_cases hn1 : n = 1
  · subst n
    have hg1 : genocchiNumberViaBernoulli 1 = 1 := by
      norm_num [genocchiNumberViaBernoulli, bernoulli_one]
    rw [hg1] at hcoeff ⊢
    norm_num at hcoeff ⊢
    exact hcoeff
  · simp only [hn1, ite_false, mul_zero, zero_sub] at hcoeff
    have hsum := congrArg (· * (n.factorial : ℚ)) hcoeff
    rw [div_mul_cancel₀ _ hfact, neg_mul, div_mul_cancel₀ _ hfact] at hsum
    rcases n.even_or_odd with hnEven | hnOdd
    · rw [pow_succ, Even.neg_one_pow hnEven]
      norm_num
      exact hsum
    · obtain ⟨r, hr⟩ := hnOdd
      have hnlt : 1 < n := by omega
      have hg : genocchiNumberViaBernoulli n = 0 := by
        rw [genocchiNumberViaBernoulli,
          bernoulli_eq_zero_of_odd (⟨r, hr⟩ : Odd n) hnlt, mul_zero]
      simpa [hg] using hsum

private theorem mgen_seidel_antisymm (a : ℕ → ℚ)
    (h : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), (m.choose i : ℚ) * a i =
      (-1 : ℚ) ^ (m + 1) * a m) (n k : ℕ) :
    eulerSeidelMatrix a n k =
      (-1 : ℚ) ^ (n + k + 1) * eulerSeidelMatrix a k n := by
  induction k generalizing n with
  | zero =>
      have h0 : eulerSeidelMatrix a n 0 = a n := rfl
      have hSn : eulerSeidelMatrix a 0 n =
          ∑ i ∈ Finset.range (n + 1), n.choose i • a (0 + i) :=
        eulerSeidelMatrix_eq_sum a 0 n
      have hsum : (∑ i ∈ Finset.range (n + 1), n.choose i • a (0 + i)) =
          ∑ i ∈ Finset.range (n + 1), (n.choose i : ℚ) * a i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [nsmul_eq_mul, zero_add]
      have hneg : (-1 : ℚ) ^ (n + 1) * (-1 : ℚ) ^ (n + 1) = 1 := by
        rw [← pow_add]
        exact Even.neg_one_pow ⟨n + 1, rfl⟩
      rw [h0, hSn, hsum, h n, show n + 0 + 1 = n + 1 by omega, ← mul_assoc,
        hneg, one_mul]
  | succ k ih =>
      have hdef : eulerSeidelMatrix a n (k + 1) =
          eulerSeidelMatrix a n k + eulerSeidelMatrix a (n + 1) k := rfl
      have hdef2 : eulerSeidelMatrix a k (n + 1) =
          eulerSeidelMatrix a k n + eulerSeidelMatrix a (k + 1) n := rfl
      rw [hdef, ih n, ih (n + 1),
        show (n + 1) + k + 1 = (n + k + 1) + 1 by omega,
        show n + (k + 1) + 1 = (n + k + 1) + 1 by omega, pow_succ, pow_succ]
      linear_combination (-(-1 : ℚ) ^ (n + k + 1)) * hdef2

private theorem mgen_genocchi_seidel_antisymm (n k : ℕ) :
    eulerSeidelMatrix genocchiNumberViaBernoulli n k =
      (-1 : ℚ) ^ (n + k + 1) *
        eulerSeidelMatrix genocchiNumberViaBernoulli k n :=
  mgen_seidel_antisymm genocchiNumberViaBernoulli mgen_genocchi_reflection_sum n k

private def mgenTransform (a : ℕ → ℚ) (c : ℚ) (m : ℕ) : ℚ :=
  a (m + 2) + a (m + 1) - c * a m

private theorem mgen_seidel_transform (a : ℕ → ℚ) (c : ℚ) (n k : ℕ) :
    eulerSeidelMatrix (mgenTransform a c) n k =
      eulerSeidelMatrix a (n + 1) (k + 1) - c * eulerSeidelMatrix a n k := by
  induction k generalizing n with
  | zero =>
      change a (n + 2) + a (n + 1) - c * a n =
        (a (n + 1) + a (n + 1 + 1)) - c * a n
      rw [show n + 1 + 1 = n + 2 by omega]
      ring
  | succ k ih =>
      change eulerSeidelMatrix (mgenTransform a c) n k +
          eulerSeidelMatrix (mgenTransform a c) (n + 1) k = _
      rw [ih n, ih (n + 1)]
      change (eulerSeidelMatrix a (n + 1) (k + 1) - c * eulerSeidelMatrix a n k) +
          (eulerSeidelMatrix a (n + 1 + 1) (k + 1) -
            c * eulerSeidelMatrix a (n + 1) k) =
        (eulerSeidelMatrix a (n + 1) (k + 1) +
            eulerSeidelMatrix a (n + 1 + 1) (k + 1)) -
          c * (eulerSeidelMatrix a n k + eulerSeidelMatrix a (n + 1) k)
      ring

private theorem mgen_transform_antisymm (a : ℕ → ℚ) (c : ℚ)
    (h : ∀ n k : ℕ, eulerSeidelMatrix a n k =
      (-1 : ℚ) ^ (n + k + 1) * eulerSeidelMatrix a k n) (n k : ℕ) :
    eulerSeidelMatrix (mgenTransform a c) n k =
      (-1 : ℚ) ^ (n + k + 1) *
        eulerSeidelMatrix (mgenTransform a c) k n := by
  rw [mgen_seidel_transform, mgen_seidel_transform, h (n + 1) (k + 1), h n k]
  have hpow : (-1 : ℚ) ^ (n + 1 + (k + 1) + 1) =
      (-1 : ℚ) ^ (n + k + 1) := by
    rw [show n + 1 + (k + 1) + 1 = (n + k + 1) + 2 by omega, pow_add]
    norm_num
  rw [hpow]
  ring

private def mgenBasisSeq : ℕ → ℕ → ℚ
  | 0 => genocchiNumberViaBernoulli
  | k + 1 => mgenTransform (mgenBasisSeq k) ((k : ℚ) * (k + 1))

private theorem mgenBasisSeq_antisymm : ∀ k n m : ℕ,
    eulerSeidelMatrix (mgenBasisSeq k) n m =
      (-1 : ℚ) ^ (n + m + 1) * eulerSeidelMatrix (mgenBasisSeq k) m n := by
  intro k
  induction k with
  | zero => exact mgen_genocchi_seidel_antisymm
  | succ k ih =>
      exact mgen_transform_antisymm _ _ ih

private theorem mgenBasisSeq_pair : ∀ k r : ℕ, 1 ≤ r →
    mgenBasisSeq k (2 * r + 1) = (k : ℚ) * mgenBasisSeq k (2 * r) := by
  intro k
  induction k with
  | zero =>
      intro r hr
      have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
      have hlt : 1 < 2 * r + 1 := by omega
      simp only [mgenBasisSeq, Nat.cast_zero, zero_mul]
      rw [genocchiNumberViaBernoulli, bernoulli_eq_zero_of_odd hodd hlt, mul_zero]
  | succ k ih =>
      intro r hr
      rw [mgenBasisSeq, mgenTransform, mgenTransform,
        show 2 * r + 1 + 2 = 2 * (r + 1) + 1 by omega,
        show 2 * r + 1 + 1 = 2 * (r + 1) by omega,
        ih (r + 1) (by omega), ih r hr]
      push_cast
      ring

private theorem mgenBasisSeq_two (k : ℕ) :
    mgenBasisSeq k 2 = -mgenBasisSeq k 1 := by
  have h00 := mgenBasisSeq_antisymm k 0 0
  have hb0 : mgenBasisSeq k 0 = 0 := by
    norm_num [eulerSeidelMatrix] at h00
    linarith
  have h20 := mgenBasisSeq_antisymm k 2 0
  norm_num [eulerSeidelMatrix, hb0] at h20
  linarith

private theorem mgenBasisSeq_one : ∀ k : ℕ,
    mgenBasisSeq k 1 = (-1 : ℚ) ^ k * (k.factorial : ℚ) ^ 2 := by
  intro k
  induction k with
  | zero =>
      norm_num [mgenBasisSeq, genocchiNumberViaBernoulli, bernoulli_one]
  | succ k ih =>
      rw [mgenBasisSeq, mgenTransform, mgenBasisSeq_pair k 1 (by omega),
        mgenBasisSeq_two k, ih, pow_succ, Nat.factorial_succ]
      push_cast
      ring

private def mgenLS : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => mgenLS n k + (k + 1) * (k + 2) * mgenLS n (k + 1)

private theorem mgenLS_eq_zero_of_lt : ∀ n k : ℕ, n < k → mgenLS n k = 0 := by
  intro n
  induction n with
  | zero =>
      intro k hk
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      intro k hk
      cases k with
      | zero => omega
      | succ k =>
          rw [mgenLS, ih k (by omega), ih (k + 1) (by omega)]
          simp

private theorem mgenLS_sum_succ (n : ℕ) (b : ℕ → ℚ) :
    (∑ k ∈ Finset.range (n + 1), (mgenLS n k : ℚ) *
      (b (k + 1) + (k : ℚ) * (k + 1) * b k)) =
      ∑ k ∈ Finset.range (n + 2), (mgenLS (n + 1) k : ℚ) * b k := by
  have hshift : (∑ k ∈ Finset.range (n + 1), (mgenLS n k : ℚ) *
        ((k : ℚ) * (k + 1) * b k)) =
      ∑ k ∈ Finset.range (n + 1),
        (((k + 1) * (k + 2) * mgenLS n (k + 1) : ℕ) : ℚ) * b (k + 1) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ,
      mgenLS_eq_zero_of_lt n (n + 1) (by omega)]
    simp only [Nat.cast_zero, zero_mul, mul_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      zero_add, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  calc
    (∑ k ∈ Finset.range (n + 1), (mgenLS n k : ℚ) *
        (b (k + 1) + (k : ℚ) * (k + 1) * b k)) =
        (∑ k ∈ Finset.range (n + 1), (mgenLS n k : ℚ) * b (k + 1)) +
          ∑ k ∈ Finset.range (n + 1), (mgenLS n k : ℚ) *
            ((k : ℚ) * (k + 1) * b k) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = (∑ k ∈ Finset.range (n + 1), (mgenLS n k : ℚ) * b (k + 1)) +
          ∑ k ∈ Finset.range (n + 1),
            (((k + 1) * (k + 2) * mgenLS n (k + 1) : ℕ) : ℚ) * b (k + 1) := by
          rw [hshift]
    _ = _ := by
          have hrec (k : ℕ) : (mgenLS (n + 1) (k + 1) : ℚ) =
              (mgenLS n k : ℚ) +
                (((k + 1) * (k + 2) * mgenLS n (k + 1) : ℕ) : ℚ) := by
            rw [mgenLS]
            push_cast
            ring
          conv_rhs => rw [Finset.sum_range_succ']
          rw [show (mgenLS (n + 1) 0 : ℚ) * b 0 = 0 by simp [mgenLS], add_zero]
          simp_rw [hrec, add_mul]
          rw [Finset.sum_add_distrib]

private def mgenLIter : ℕ → ℕ → ℚ
  | 0 => genocchiNumberViaBernoulli
  | n + 1 => mgenTransform (mgenLIter n) 0

private theorem mgenBasisSeq_shift (k m : ℕ) :
    mgenBasisSeq k (m + 2) + mgenBasisSeq k (m + 1) =
      mgenBasisSeq (k + 1) m + (k : ℚ) * (k + 1) * mgenBasisSeq k m := by
  rw [mgenBasisSeq, mgenTransform]
  ring

private theorem mgenLIter_eq_sum : ∀ n m : ℕ,
    mgenLIter n m = ∑ k ∈ Finset.range (n + 1),
      (mgenLS n k : ℚ) * mgenBasisSeq k m := by
  intro n
  induction n with
  | zero =>
      intro m
      simp [mgenLIter, mgenLS, mgenBasisSeq]
  | succ n ih =>
      intro m
      rw [mgenLIter, mgenTransform, ih (m + 2), ih (m + 1)]
      simp only [zero_mul, sub_zero]
      rw [← Finset.sum_add_distrib]
      calc
        (∑ k ∈ Finset.range (n + 1),
            ((mgenLS n k : ℚ) * mgenBasisSeq k (m + 2) +
              (mgenLS n k : ℚ) * mgenBasisSeq k (m + 1))) =
            ∑ k ∈ Finset.range (n + 1), (mgenLS n k : ℚ) *
              (mgenBasisSeq (k + 1) m +
                (k : ℚ) * (k + 1) * mgenBasisSeq k m) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [← mul_add, mgenBasisSeq_shift]
        _ = _ := mgenLS_sum_succ n (fun k => mgenBasisSeq k m)

private theorem mgenLIter_eq_seidel : ∀ n m : ℕ,
    mgenLIter n m = eulerSeidelMatrix genocchiNumberViaBernoulli (m + n) n := by
  intro n
  induction n with
  | zero =>
      intro m
      rfl
  | succ n ih =>
      intro m
      rw [mgenLIter, mgenTransform, ih (m + 2), ih (m + 1)]
      simp only [zero_mul, sub_zero]
      rw [show m + 2 + n = m + (n + 1) + 1 by omega,
        show m + 1 + n = m + (n + 1) by omega]
      change _ + _ = _ + _
      ac_rfl

private theorem mgen_median_eq_full (m : ℕ) (hm : 1 ≤ m) :
    medianGenocchiOdd m = ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℚ) * genocchiNumberViaBernoulli (m + 1 + i) := by
  let f : ℕ → ℚ := fun j =>
    (m.choose j : ℚ) * genocchiNumberViaBernoulli (2 * m + 1 - j)
  have hodd : (∑ k ∈ Finset.range ((m - 1) / 2 + 1), f (2 * k + 1)) =
      ∑ j ∈ (Finset.range (m + 1)).filter (fun j => j % 2 = 1), f j := by
    apply Finset.sum_bij (fun k _ => 2 * k + 1)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      constructor <;> omega
    · intro k₁ hk₁ k₂ hk₂ heq
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      refine ⟨j / 2, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro k hk
      rfl
  have hfilter : (∑ j ∈ (Finset.range (m + 1)).filter (fun j => j % 2 = 1), f j) =
      ∑ j ∈ Finset.range (m + 1), f j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases hjodd : j % 2 = 1
    · rw [ite_eq_left hjodd]
    · rw [ite_eq_right hjodd]
      have hjeven : j % 2 = 0 := by omega
      obtain ⟨q, hq⟩ : Even j := Nat.even_iff.mpr hjeven
      have hqle : q ≤ m := by omega
      have hindexOdd : Odd (2 * m + 1 - j) :=
        ⟨m - q, by omega⟩
      have hindexLarge : 1 < 2 * m + 1 - j := by omega
      have hg : genocchiNumberViaBernoulli (2 * m + 1 - j) = 0 := by
        rw [genocchiNumberViaBernoulli,
          bernoulli_eq_zero_of_odd hindexOdd hindexLarge, mul_zero]
      simp [f, hg]
  have hreflect : (∑ i ∈ Finset.range (m + 1), f i) =
      ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℚ) * genocchiNumberViaBernoulli (m + 1 + i) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [f]
    rw [show m + 1 - 1 - i = m - i by omega, Nat.choose_symm (by omega),
      show 2 * m + 1 - (m - i) = m + 1 + i by omega]
  rw [medianGenocchiOdd, ite_eq_right (by omega : m ≠ 0)]
  have hdefsum : (∑ k ∈ Finset.range ((m - 1) / 2 + 1),
      (m.choose (2 * k + 1) : ℚ) * genocchiNumberViaBernoulli (2 * m - 2 * k)) =
      ∑ k ∈ Finset.range ((m - 1) / 2 + 1), f (2 * k + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [f]
    rw [show 2 * m + 1 - (2 * k + 1) = 2 * m - 2 * k by
      rw [Finset.mem_range] at hk
      omega]
  rw [hdefsum, hodd, hfilter, hreflect]

private theorem mgen_median_eq_LIter (m : ℕ) (hm : 1 ≤ m) :
    medianGenocchiOdd m = mgenLIter m 1 := by
  rw [mgen_median_eq_full m hm, mgenLIter_eq_seidel,
    eulerSeidelMatrix_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [nsmul_eq_mul]
  rw [show 1 + m + i = m + 1 + i by omega]

private theorem mgen_median_eq_basis (m : ℕ) (hm : 1 ≤ m) :
    medianGenocchiOdd m = ∑ k ∈ Finset.range (m + 1),
      (mgenLS m k : ℚ) * ((-1 : ℚ) ^ k * (k.factorial : ℚ) ^ 2) := by
  rw [mgen_median_eq_LIter m hm, mgenLIter_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [mgenBasisSeq_one]

private theorem mgen_basis_row_succ (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2),
      (mgenLS (n + 1) k : ℚ) * ((-1 : ℚ) ^ k * (k.factorial : ℚ) ^ 2)) =
      -∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ k * (mgenLS n k : ℚ) *
          (k.factorial : ℚ) * ((k + 1).factorial : ℚ) := by
  have hshift : (∑ j ∈ Finset.range (n + 1),
        ((((j + 1) * (j + 2) * mgenLS n (j + 1) : ℕ) : ℚ) *
          ((-1 : ℚ) ^ (j + 1) * ((j + 1).factorial : ℚ) ^ 2))) =
      ∑ k ∈ Finset.range (n + 1),
        (((k * (k + 1) * mgenLS n k : ℕ) : ℚ) *
          ((-1 : ℚ) ^ k * (k.factorial : ℚ) ^ 2)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ',
      mgenLS_eq_zero_of_lt n (n + 1) (by omega)]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, add_zero]
  have hrec (k : ℕ) : (mgenLS (n + 1) (k + 1) : ℚ) =
      (mgenLS n k : ℚ) +
        (((k + 1) * (k + 2) * mgenLS n (k + 1) : ℕ) : ℚ) := by
    rw [mgenLS]
    push_cast
    ring
  rw [Finset.sum_range_succ']
  rw [show (mgenLS (n + 1) 0 : ℚ) *
      ((-1 : ℚ) ^ 0 * (Nat.factorial 0 : ℚ) ^ 2) = 0 by
    simp [mgenLS], add_zero]
  simp_rw [hrec, add_mul]
  simp only [Nat.add_mul] at hshift
  rw [Finset.sum_add_distrib, hshift, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  ring

private def mgenNormalizedLS : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      mgenNormalizedLS n k + ((k + 1) * (k + 2) / 2) * mgenNormalizedLS n (k + 1)

private theorem mgenNormalizedLS_eq_zero_of_lt : ∀ n k : ℕ,
    n < k → mgenNormalizedLS n k = 0 := by
  intro n
  induction n with
  | zero =>
      intro k hk
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      intro k hk
      cases k with
      | zero => omega
      | succ k =>
          rw [mgenNormalizedLS, ih k (by omega), ih (k + 1) (by omega)]
          simp

private theorem mgenLS_eq_pow_mul_normalized : ∀ n k : ℕ, k ≤ n →
    mgenLS n k = 2 ^ (n - k) * mgenNormalizedLS n k := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst k
      rfl
  | succ n ih =>
      intro k hk
      cases k with
      | zero => simp [mgenLS, mgenNormalizedLS]
      | succ k =>
          have hkn : k ≤ n := by omega
          by_cases htop : k = n
          · subst k
            rw [mgenLS, mgenNormalizedLS,
              mgenLS_eq_zero_of_lt n (n + 1) (by omega),
              mgenNormalizedLS_eq_zero_of_lt n (n + 1) (by omega), ih n le_rfl]
            simp
          · have hklt : k < n := by omega
            have hk1n : k + 1 ≤ n := by omega
            rw [mgenLS, mgenNormalizedLS, ih k hkn, ih (k + 1) hk1n]
            have htwo : 2 * (((k + 1) * (k + 2)) / 2) = (k + 1) * (k + 2) :=
              Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (k + 1))
            have hpow : 2 ^ (n - k) = 2 * 2 ^ (n - (k + 1)) := by
              rw [show n - k = (n - (k + 1)) + 1 by omega, pow_succ]
              ring
            rw [show n + 1 - (k + 1) = n - k by omega, hpow]
            have hfactor : (k + 1) * (k + 2) *
                (2 ^ (n - (k + 1)) * mgenNormalizedLS n (k + 1)) =
                2 * 2 ^ (n - (k + 1)) *
                  (((k + 1) * (k + 2) / 2) * mgenNormalizedLS n (k + 1)) := by
              calc
                _ = (2 * (((k + 1) * (k + 2)) / 2)) *
                    (2 ^ (n - (k + 1)) * mgenNormalizedLS n (k + 1)) := by
                      exact congrArg
                        (fun x => x *
                          (2 ^ (n - (k + 1)) * mgenNormalizedLS n (k + 1)))
                        htwo.symm
                _ = _ := by ac_rfl
            rw [hfactor]
            ring

private def mgenFactor : ℕ → ℕ
  | 0 => 1
  | k + 1 => mgenFactor k * ((k + 1) * (k + 2) / 2)

private theorem mgen_factorial_mul_factorial (k : ℕ) :
    k.factorial * (k + 1).factorial = 2 ^ k * mgenFactor k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have htwo : 2 * (((k + 1) * (k + 2)) / 2) = (k + 1) * (k + 2) :=
        Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (k + 1))
      calc
        (k + 1).factorial * (k + 1 + 1).factorial =
            (k.factorial * (k + 1).factorial) * ((k + 1) * (k + 2)) := by
              change ((k + 1) * k.factorial) *
                  ((k + 2) * (k + 1).factorial) = _
              ac_rfl
        _ = (2 ^ k * mgenFactor k) *
            (2 * (((k + 1) * (k + 2)) / 2)) := by rw [ih, htwo]
        _ = 2 ^ (k + 1) *
            (mgenFactor k * (((k + 1) * (k + 2)) / 2)) := by
              rw [pow_succ]
              ring
        _ = _ := by rw [mgenFactor]

private def mgenQuotient (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (n + k) * (mgenNormalizedLS n k : ℤ) * (mgenFactor k : ℤ)

private theorem mgen_gandhi_sum_eq_pow_mul_quotient (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ (n + k) * (mgenLS n k : ℤ) *
        (k.factorial : ℤ) * ((k + 1).factorial : ℤ)) =
      (2 : ℤ) ^ n * mgenQuotient n := by
  rw [mgenQuotient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hkn : k ≤ n := by omega
  have hls : (mgenLS n k : ℤ) =
      (2 : ℤ) ^ (n - k) * (mgenNormalizedLS n k : ℤ) := by
    exact_mod_cast mgenLS_eq_pow_mul_normalized n k hkn
  have hfact : (k.factorial : ℤ) * ((k + 1).factorial : ℤ) =
      (2 : ℤ) ^ k * (mgenFactor k : ℤ) := by
    exact_mod_cast mgen_factorial_mul_factorial k
  calc
    (-1 : ℤ) ^ (n + k) * (mgenLS n k : ℤ) *
        (k.factorial : ℤ) * ((k + 1).factorial : ℤ) =
        (-1 : ℤ) ^ (n + k) * (mgenLS n k : ℤ) *
          ((k.factorial : ℤ) * ((k + 1).factorial : ℤ)) := by ring
    _ = (-1 : ℤ) ^ (n + k) *
        ((2 : ℤ) ^ (n - k) * (mgenNormalizedLS n k : ℤ)) *
          ((2 : ℤ) ^ k * (mgenFactor k : ℤ)) := by rw [hls, hfact]
    _ = _ := by
      calc
        _ = ((-1 : ℤ) ^ (n + k) * (mgenNormalizedLS n k : ℤ) *
              (mgenFactor k : ℤ)) *
            ((2 : ℤ) ^ (n - k) * (2 : ℤ) ^ k) := by ring
        _ = _ := by rw [← pow_add, Nat.sub_add_cancel hkn]; ring

private theorem mgen_median_eq_signed_quotient (n : ℕ) :
    medianGenocchiOdd (n + 1) =
      (2 : ℚ) ^ n * (((-1 : ℤ) ^ (n + 1) * mgenQuotient n : ℤ) : ℚ) := by
  rw [mgen_median_eq_basis (n + 1) (by omega), mgen_basis_row_succ]
  have hsum := mgen_gandhi_sum_eq_pow_mul_quotient n
  have hcast := congrArg (fun z : ℤ => (z : ℚ)) hsum
  push_cast at hcast
  have hsign : -(∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ k * (mgenLS n k : ℚ) *
          (k.factorial : ℚ) * ((k + 1).factorial : ℚ)) =
      (-1 : ℚ) ^ (n + 1) *
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n + k) * (mgenLS n k : ℚ) *
            (k.factorial : ℚ) * ((k + 1).factorial : ℚ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hp : (-1 : ℚ) ^ (n + 1) * (-1 : ℚ) ^ (n + k) =
        -((-1 : ℚ) ^ k) := by
      rw [← pow_add, show n + 1 + (n + k) = (n + n) + (k + 1) by omega,
        pow_add, Even.neg_one_pow (⟨n, by omega⟩ : Even (n + n)), one_mul,
        pow_succ]
      ring
    calc
      -((-1 : ℚ) ^ k * (mgenLS n k : ℚ) *
          (k.factorial : ℚ) * ((k + 1).factorial : ℚ)) =
          -((-1 : ℚ) ^ k) * (mgenLS n k : ℚ) *
            (k.factorial : ℚ) * ((k + 1).factorial : ℚ) := by ring
      _ = _ := by rw [← hp]; ring
  calc
    -(∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ k * (mgenLS n k : ℚ) *
          (k.factorial : ℚ) * ((k + 1).factorial : ℚ)) = _ := hsign
    _ = (-1 : ℚ) ^ (n + 1) * ((2 : ℚ) ^ n * (mgenQuotient n : ℚ)) := by
      rw [hcast]
    _ = _ := by
      push_cast
      ring

private theorem mgen_factor_six_dvd : ∀ k : ℕ, 3 ≤ k → 6 ∣ mgenFactor k := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk2 : k = 2
      · subst k
        norm_num [mgenFactor]
      · have hk3 : 3 ≤ k := by omega
        rw [mgenFactor]
        exact dvd_mul_of_dvd_left (ih hk3) _

private theorem mgenNormalizedLS_zero (n : ℕ) (hn : 0 < n) :
    mgenNormalizedLS n 0 = 0 := by
  cases n with
  | zero => omega
  | succ n => rfl

private theorem mgenNormalizedLS_one (n : ℕ) :
    mgenNormalizedLS (n + 1) 1 = 1 := by
  induction n with
  | zero => norm_num [mgenNormalizedLS]
  | succ n ih =>
      rw [mgenNormalizedLS]
      rw [mgenNormalizedLS_zero (n + 1) (by omega), ih]

private theorem mgenNormalizedLS_two_mod_two (n : ℕ) :
    mgenNormalizedLS (n + 1) 2 % 2 = n % 2 := by
  induction n with
  | zero => norm_num [mgenNormalizedLS]
  | succ n ih =>
      rw [mgenNormalizedLS, mgenNormalizedLS_one]
      change (1 + 3 * mgenNormalizedLS (n + 1) 2) % 2 = (n + 1) % 2
      omega

private theorem mgen_sum_range_add_three {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (r : ℕ) :
    ∑ k ∈ Finset.range (r + 3), f k =
      f 0 + f 1 + f 2 + ∑ k ∈ Finset.range r, f (k + 3) := by
  rw [show r + 3 = (r + 2) + 1 by omega, Finset.sum_range_succ']
  rw [show r + 2 = (r + 1) + 1 by omega, Finset.sum_range_succ']
  rw [Finset.sum_range_succ']
  simp only [zero_add, Nat.reduceAdd]
  ac_rfl

private theorem mgen_sum_modEq_zero {s : Finset ℕ} {f : ℕ → ℤ} {m : ℤ}
    (h : ∀ k ∈ s, f k ≡ 0 [ZMOD m]) :
    (∑ k ∈ s, f k) ≡ 0 [ZMOD m] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

private theorem mgenQuotient_modEq_first_columns (n : ℕ) (hn : 2 ≤ n) :
    mgenQuotient n ≡
      (-1 : ℤ) ^ (n + 1) +
        (-1 : ℤ) ^ (n + 2) * (mgenNormalizedLS n 2 : ℤ) * 3 [ZMOD 6] := by
  let f : ℕ → ℤ := fun k =>
    (-1 : ℤ) ^ (n + k) * (mgenNormalizedLS n k : ℤ) * (mgenFactor k : ℤ)
  have hlen : n + 1 = (n - 2) + 3 := by omega
  have hsplit : mgenQuotient n =
      f 0 + f 1 + f 2 + ∑ k ∈ Finset.range (n - 2), f (k + 3) := by
    rw [mgenQuotient, hlen, mgen_sum_range_add_three]
  have htail : (∑ k ∈ Finset.range (n - 2), f (k + 3)) ≡ 0 [ZMOD 6] := by
    apply mgen_sum_modEq_zero
    intro k _
    rw [Int.modEq_zero_iff_dvd]
    have hdNat : 6 ∣ mgenFactor (k + 3) := mgen_factor_six_dvd (k + 3) (by omega)
    have hd : (6 : ℤ) ∣ (mgenFactor (k + 3) : ℤ) := by exact_mod_cast hdNat
    obtain ⟨q, hq⟩ := hd
    refine ⟨((-1 : ℤ) ^ (n + (k + 3)) *
      (mgenNormalizedLS n (k + 3) : ℤ) * q), ?_⟩
    simp only [f]
    rw [hq]
    ring
  have hzero : mgenNormalizedLS n 0 = 0 := mgenNormalizedLS_zero n (by omega)
  have hone : mgenNormalizedLS n 1 = 1 := by
    have hn1 : 1 ≤ n := by omega
    simpa [Nat.sub_add_cancel hn1] using mgenNormalizedLS_one (n - 1)
  rw [hsplit]
  calc
    f 0 + f 1 + f 2 + ∑ k ∈ Finset.range (n - 2), f (k + 3) ≡
        f 0 + f 1 + f 2 + 0 [ZMOD 6] := (Int.ModEq.refl _).add htail
    _ = (-1 : ℤ) ^ (n + 1) +
        (-1 : ℤ) ^ (n + 2) * (mgenNormalizedLS n 2 : ℤ) * 3 := by
      simp [f, hzero, hone, mgenFactor]

private theorem mgenQuotient_mod_six (n : ℕ) (hn : 1 ≤ n) :
    mgenQuotient n ≡ if Odd n then 1 else 2 [ZMOD 6] := by
  by_cases hn2 : 2 ≤ n
  · have hfirst := mgenQuotient_modEq_first_columns n hn2
    have hn1 : 1 ≤ n := by omega
    have hcolmod : mgenNormalizedLS n 2 % 2 = (n - 1) % 2 := by
      simpa [Nat.sub_add_cancel hn1] using mgenNormalizedLS_two_mod_two (n - 1)
    by_cases hodd : Odd n
    · simp only [hodd, ↓reduceIte]
      apply hfirst.trans
      obtain ⟨r, hr⟩ := hodd
      have he1 : Even (n + 1) := by
        use r + 1
        omega
      have ho2 : Odd (n + 2) := by
        use r + 1
        omega
      have hAeven : Even (mgenNormalizedLS n 2) :=
        Nat.not_odd_iff_even.mp (Nat.not_odd_iff.mpr (by omega))
      obtain ⟨a, ha⟩ := hAeven
      rw [he1.neg_one_pow, ho2.neg_one_pow, ha, Int.modEq_iff_dvd]
      push_cast
      refine ⟨(a : ℤ), by ring⟩
    · simp only [hodd, ↓reduceIte]
      apply hfirst.trans
      have heven : Even n := Nat.not_odd_iff_even.mp hodd
      obtain ⟨r, hr⟩ := heven
      have ho1 : Odd (n + 1) := by
        use r
        omega
      have he2 : Even (n + 2) := by
        use r + 1
        omega
      have hAodd : Odd (mgenNormalizedLS n 2) := Nat.odd_iff.mpr (by omega)
      obtain ⟨a, ha⟩ := hAodd
      rw [ho1.neg_one_pow, he2.neg_one_pow, ha, Int.modEq_iff_dvd]
      push_cast
      refine ⟨-(a : ℤ), by ring⟩
  · have hn_eq : n = 1 := by omega
    subst n
    norm_num [mgenQuotient, mgenNormalizedLS, mgenFactor,
      Finset.sum_range_succ, Int.ModEq]

/-- **Divisibility of the median Genocchi numbers.** Let $H_{2m+1}$ denote the odd-indexed median
Genocchi values, with the signs given by their defining sum, so that $H_5 = 2$, $H_7 = -8$ and
$H_9 = 56$. For every natural number $n \ge 1$ there is an integer $z$ with $H_{2n+3} = 2^n z$,
and $z \equiv 1 \pmod 6$ if $n$ is odd, while $z \equiv 4 \pmod 6$ if $n$ is even.

Proof: The antisymmetry of the Euler–Seidel matrix of the Genocchi numbers writes $H_{2n+3}$ as
an alternating sum of Legendre–Stirling numbers times $k!\,(k+1)!$. Pulling a power of two out of
each term gives the factor $2^n$; in the remaining sum every term from the fourth on is divisible
by $6$, which gives the residue. The divisibility and residue arguments are Chen's, applied to
this finite sum instead of his continued fraction.

Source: Kwang-Wu Chen, *An Interesting Lemma for Regular C-fractions*, Journal of Integer
Sequences 6 (2003), Article 03.4.8: <https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen50.tex>.
Proves `Wanted` entry `medianGenocchiOdd_divisibility`.
-/
theorem medianGenocchiOdd_divisibility (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, medianGenocchiOdd (n + 1) = (2 : ℚ) ^ n * z ∧
      Int.ModEq 6 z (if Odd n then 1 else 4) := by
  refine ⟨(-1 : ℤ) ^ (n + 1) * mgenQuotient n,
    mgen_median_eq_signed_quotient n, ?_⟩
  have hquot := mgenQuotient_mod_six n hn
  by_cases hodd : Odd n
  · simp only [hodd, ↓reduceIte] at hquot ⊢
    obtain ⟨r, hr⟩ := hodd
    have he : Even (n + 1) := by
      use r + 1
      omega
    rw [he.neg_one_pow, one_mul]
    exact hquot
  · simp only [hodd, ↓reduceIte] at hquot ⊢
    have heven : Even n := Nat.not_odd_iff_even.mp hodd
    obtain ⟨r, hr⟩ := heven
    have ho : Odd (n + 1) := by
      use r
      omega
    rw [ho.neg_one_pow, neg_one_mul]
    exact hquot.neg.trans (by norm_num [Int.ModEq])

end

end MetaMathlibExt
