/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

section
namespace MetaMathlibExt

private noncomputable def myL : Polynomial ℚ →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun n : ℕ => (_root_.bernoulli n) • LinearMap.id)
private theorem myL_monomial (n : ℕ) (a : ℚ) :
    myL ((Polynomial.monomial n) a) = a * _root_.bernoulli n := by
  simp [myL, Polynomial.lsum_apply, mul_comm]
private theorem myL_X_pow (n : ℕ) : myL (Polynomial.X ^ n : Polynomial ℚ) = _root_.bernoulli n := by
  have h : (Polynomial.X ^ n : Polynomial ℚ) = (Polynomial.monomial n) 1 := by
    simp [Polynomial.X_pow_eq_monomial]
  rw [h, myL_monomial, one_mul]
private theorem myL_C_mul (a : ℚ) (p : Polynomial ℚ) : myL (Polynomial.C a * p) = a * myL p := by
  have h : Polynomial.C a * p = a • p := by simp [Polynomial.smul_eq_C_mul]
  rw [h, map_smul, smul_eq_mul]
private theorem myL_X_add_C_pow (n : ℕ) (m : ℕ) :
    myL (((Polynomial.X + Polynomial.C (m : ℚ)) ^ n : Polynomial ℚ))
    = ∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℚ) * _root_.bernoulli i * (m : ℚ) ^ (n - i) := by
  rw [add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hc : ((Nat.choose n i : Polynomial ℚ)) = Polynomial.C ((Nat.choose n i : ℚ)) := by
    exact_mod_cast rfl
  have h1 : (Polynomial.X ^ i * Polynomial.C (m : ℚ) ^ (n - i) * (↑(Nat.choose n i) : Polynomial ℚ))
      = Polynomial.C (((m : ℚ) ^ (n - i) * (Nat.choose n i : ℚ))) * Polynomial.X ^ i := by
    rw [hc, ← Polynomial.C_pow, mul_assoc, ← Polynomial.C_mul]
    ring
  rw [h1, myL_C_mul, myL_X_pow]
  ring
private theorem shift_monomial (n : ℕ) (a : ℚ) (m : ℕ) :
    myL (((Polynomial.monomial n) a).comp (Polynomial.X + Polynomial.C (m : ℚ)))
      - myL ((Polynomial.monomial n) a)
    = ∑ k ∈ Finset.range m,
      Polynomial.eval (k : ℚ) (Polynomial.derivative ((Polynomial.monomial n) a)) := by
  rw [Polynomial.monomial_comp, myL_C_mul, myL_X_add_C_pow, myL_monomial]
  by_cases hn : n = 0
  · subst hn
    simp [Polynomial.monomial_zero_left, Polynomial.derivative_C]
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 :=
      ⟨n - 1, (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)).symm⟩
    have htop : ∑ i ∈ Finset.range (p + 1 + 1),
        ((p + 1).choose i : ℚ) * _root_.bernoulli i * (m : ℚ) ^ (p + 1 - i)
        = (∑ i ∈ Finset.range (p + 1),
          ((p + 1).choose i : ℚ) * _root_.bernoulli i * (m : ℚ) ^ (p + 1 - i))
          + _root_.bernoulli (p + 1) := by
      rw [Finset.sum_range_succ]
      have h1 : (((p + 1).choose (p + 1) : ℕ) : ℚ) = 1 := by simp [Nat.choose_self]
      rw [h1, Nat.sub_self, pow_zero, one_mul, mul_one]
    rw [htop, mul_add, add_sub_cancel_right]
    have hRHS : ∑ k ∈ Finset.range m,
        Polynomial.eval (k : ℚ) (Polynomial.derivative ((Polynomial.monomial (p+1)) a))
        = a * ((p : ℚ) + 1) * ∑ k ∈ Finset.range m, (k : ℚ) ^ p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Polynomial.derivative_monomial, Polynomial.eval_monomial]
      push_cast
      ring
    have hFaul := sum_range_pow m p
    rw [hRHS, hFaul, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hne : ((p : ℚ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
    field_simp
private theorem shift_general (p : Polynomial ℚ) (m : ℕ) :
    myL (p.comp (Polynomial.X + Polynomial.C (m : ℚ))) - myL p
    = ∑ k ∈ Finset.range m, Polynomial.eval (k : ℚ) (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.add_comp, map_add, Polynomial.derivative_add, map_add]
    simp only [Polynomial.eval_add]
    rw [Finset.sum_add_distrib]
    linear_combination hp + hq
  | monomial n a => exact shift_monomial n a m
private theorem neg_one_pow_mul_bernoulli (n : ℕ) :
    (-1 : ℚ) ^ n * _root_.bernoulli n
    = (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℚ) * _root_.bernoulli i) := by
  have htop : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℚ) * _root_.bernoulli i
      = (∑ i ∈ Finset.range n, (Nat.choose n i : ℚ) * _root_.bernoulli i)
        + _root_.bernoulli n := by
    rw [Finset.sum_range_succ]
    have h1 : (((n).choose (n) : ℕ) : ℚ) = 1 := by simp [Nat.choose_self]
    rw [h1, one_mul]
  rw [htop, _root_.sum_bernoulli]
  by_cases hn1 : n = 1
  · subst hn1
    simp [_root_.bernoulli_one]
    norm_num
  · simp only [hn1, ite_false, zero_add]
    by_cases hev : Even n
    · have hpow : (-1 : ℚ) ^ n = 1 := hev.neg_one_pow
      rw [hpow, one_mul]
    · have hodd : Odd n := Nat.not_even_iff_odd.mp hev
      have h1n : 1 < n := by
        rcases Nat.lt_or_ge n 2 with h | h
        · interval_cases n <;> simp_all
        · omega
      have hB : _root_.bernoulli n = 0 := bernoulli_eq_zero_of_odd hodd h1n
      rw [hB, mul_zero]
private theorem reflect_monomial (n : ℕ) (a : ℚ) :
    myL (((Polynomial.monomial n) a).comp (-Polynomial.X))
    = myL (((Polynomial.monomial n) a).comp (Polynomial.X + 1)) := by
  rw [Polynomial.monomial_comp, Polynomial.monomial_comp]
  have hneg : (-Polynomial.X : Polynomial ℚ) ^ n
      = Polynomial.C ((-1 : ℚ) ^ n) * Polynomial.X ^ n := by
    have hX : (-Polynomial.X : Polynomial ℚ) = Polynomial.C (-1) * Polynomial.X := by simp
    rw [hX, mul_pow, ← Polynomial.C_pow]
  rw [hneg, ← mul_assoc, ← Polynomial.C_mul, myL_C_mul, myL_C_mul, myL_X_pow]
  have h1 : ((1 : Polynomial ℚ)) = Polynomial.C (1 : ℚ) := by simp
  have hRHS : myL (((Polynomial.X + 1 : Polynomial ℚ)) ^ n)
      = ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℚ) * _root_.bernoulli i := by
    have h10 : (Polynomial.X + 1 : Polynomial ℚ) = Polynomial.X + Polynomial.C (1 : ℚ) := by
      rw [h1]
    rw [h10]
    have h := myL_X_add_C_pow n 1
    simp only [Nat.cast_one, one_pow, mul_one] at h
    exact h
  rw [hRHS, ← neg_one_pow_mul_bernoulli]
  ring
private theorem reflect_general (p : Polynomial ℚ) :
    myL (p.comp (-Polynomial.X)) = myL (p.comp (Polynomial.X + 1)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.add_comp, Polynomial.add_comp, map_add, map_add, hp, hq]
  | monomial n a => exact reflect_monomial n a
private theorem comp_shift_neg (m : ℕ) :
    (Polynomial.X + Polynomial.C (m : ℚ)).comp (-Polynomial.X)
    = Polynomial.C (m : ℚ) - Polynomial.X := by
  rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, sub_eq_add_neg, add_comm]
private theorem comp_shift_succ (m : ℕ) :
    (Polynomial.X + Polynomial.C (m : ℚ)).comp (Polynomial.X + 1)
    = Polynomial.X + Polynomial.C (((m + 1 : ℕ)) : ℚ) := by
  rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
  have h1 : ((1 : Polynomial ℚ)) = Polynomial.C (1 : ℚ) := by simp
  have hm : (Polynomial.C (m : ℚ) + Polynomial.C (1 : ℚ)) = Polynomial.C (((m + 1 : ℕ)) : ℚ) := by
    rw [← Polynomial.C_add]
    congr 1
    push_cast
    ring
  rw [h1]
  have h2 : Polynomial.C (1 : ℚ) + Polynomial.C (m : ℚ)
      = Polynomial.C (((m + 1 : ℕ)) : ℚ) := by
    rw [add_comm]
    exact hm
  rw [add_assoc, h2]
private theorem antisym_deriv_eval (q : Polynomial ℚ) (m : ℕ)
    (hanti : q.comp (Polynomial.C (m : ℚ) - Polynomial.X) = -q) :
    Polynomial.eval (m : ℚ) (Polynomial.derivative q)
    = Polynomial.eval 0 (Polynomial.derivative q) := by
  have hder : Polynomial.derivative (q.comp (Polynomial.C (m : ℚ) - Polynomial.X))
      = -((Polynomial.derivative q).comp (Polynomial.C (m : ℚ) - Polynomial.X)) := by
    rw [Polynomial.derivative_comp]
    have hd : Polynomial.derivative (Polynomial.C (m : ℚ) - Polynomial.X) = -1 := by simp
    rw [hd]
    have h2 : (-1 : Polynomial ℚ)
        * (Polynomial.derivative q).comp (Polynomial.C (m : ℚ) - Polynomial.X)
        = -((Polynomial.derivative q).comp (Polynomial.C (m : ℚ) - Polynomial.X)) := by
      rw [neg_one_mul]
    rw [h2]
  have h2 : Polynomial.derivative (q.comp (Polynomial.C (m : ℚ) - Polynomial.X))
      = -(Polynomial.derivative q) := by
    rw [hanti, Polynomial.derivative_neg]
  have h3 : (Polynomial.derivative q).comp (Polynomial.C (m : ℚ) - Polynomial.X)
      = Polynomial.derivative q := by
    have := hder.symm.trans h2
    simp only [neg_inj] at this
    exact this
  have hev := congrArg (Polynomial.eval (0 : ℚ)) h3
  simp only [Polynomial.eval_comp] at hev
  have h0 : Polynomial.eval (0 : ℚ) (Polynomial.C (m : ℚ) - Polynomial.X) = (m : ℚ) := by simp
  rw [h0] at hev
  exact hev
private theorem antisym_halving (q : Polynomial ℚ) (m : ℕ) (hm : 1 ≤ m)
    (hanti : q.comp (Polynomial.C (m : ℚ) - Polynomial.X) = -q) :
    myL (q.comp (Polynomial.X + Polynomial.C (m : ℚ)))
    = (1 / 2) * ∑ k ∈ Finset.Ico 1 m, Polynomial.eval (k : ℚ) (Polynomial.derivative q) := by
  have hS1 := shift_general q m
  have hS2 := shift_general q (m + 1)
  have hR := reflect_general (q.comp (Polynomial.X + Polynomial.C (m : ℚ)))
  have hLHS : (q.comp (Polynomial.X + Polynomial.C (m : ℚ))).comp (-Polynomial.X) = -q := by
    rw [Polynomial.comp_assoc, comp_shift_neg, hanti]
  have hRHS : (q.comp (Polynomial.X + Polynomial.C (m : ℚ))).comp (Polynomial.X + 1)
      = q.comp (Polynomial.X + Polynomial.C (((m + 1 : ℕ)) : ℚ)) := by
    rw [Polynomial.comp_assoc, comp_shift_succ]
  rw [hLHS, hRHS, map_neg] at hR
  have hS2' : -(myL q) - myL q
      = ∑ k ∈ Finset.range (m + 1), Polynomial.eval (k : ℚ) (Polynomial.derivative q) := by
    linear_combination hR + hS2
  have hsplit1 : ∑ k ∈ Finset.range m, Polynomial.eval (k : ℚ) (Polynomial.derivative q)
      = Polynomial.eval 0 (Polynomial.derivative q)
        + ∑ k ∈ Finset.Ico 1 m, Polynomial.eval (k : ℚ) (Polynomial.derivative q) := by
    have h := Finset.sum_range_add_sum_Ico
      (fun k => Polynomial.eval (k : ℚ) (Polynomial.derivative q)) hm
    simpa using h.symm
  have hsplit2 : ∑ k ∈ Finset.range (m + 1), Polynomial.eval (k : ℚ) (Polynomial.derivative q)
      = (∑ k ∈ Finset.range m, Polynomial.eval (k : ℚ) (Polynomial.derivative q))
        + Polynomial.eval (m : ℚ) (Polynomial.derivative q) := by
    rw [Finset.sum_range_succ]
  have hdm := antisym_deriv_eval q m hanti
  rw [hsplit1] at hS1
  rw [hsplit2, hsplit1, hdm] at hS2'
  linear_combination hS1 - (1 / 2) * hS2'
private theorem base_invariance (N m : ℕ) :
    ((Polynomial.X ^ N * (Polynomial.X - Polynomial.C (m : ℚ)) ^ N : Polynomial ℚ)).comp
      (Polynomial.C (m : ℚ) - Polynomial.X)
    = (Polynomial.X ^ N * (Polynomial.X - Polynomial.C (m : ℚ)) ^ N : Polynomial ℚ) := by
  have hsub : (Polynomial.X - Polynomial.C (m : ℚ)).comp (Polynomial.C (m : ℚ) - Polynomial.X)
      = -Polynomial.X := by
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    abel
  rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.pow_comp, Polynomial.X_comp, hsub]
  have hbase : (Polynomial.C (m : ℚ) - Polynomial.X) * -Polynomial.X
      = Polynomial.X * (Polynomial.X - Polynomial.C (m : ℚ)) := by ring
  have hmul : ((Polynomial.C (m : ℚ) - Polynomial.X) ^ N * (-Polynomial.X) ^ N : Polynomial ℚ)
      = (((Polynomial.C (m : ℚ) - Polynomial.X) * -Polynomial.X) ^ N) := by
    rw [mul_pow]
  have hmul2 : (Polynomial.X ^ N * (Polynomial.X - Polynomial.C (m : ℚ)) ^ N : Polynomial ℚ)
      = ((Polynomial.X * (Polynomial.X - Polynomial.C (m : ℚ))) ^ N) := by
    rw [mul_pow]
  rw [hmul, hmul2, hbase]
private theorem poly_deriv_comp_neg (F : Polynomial ℚ) (m : ℕ) :
    (Polynomial.derivative F).comp (Polynomial.C (m : ℚ) - Polynomial.X)
    = -(Polynomial.derivative (F.comp (Polynomial.C (m : ℚ) - Polynomial.X))) := by
  have h := Polynomial.derivative_comp F (Polynomial.C (m : ℚ) - Polynomial.X)
  have hd : Polynomial.derivative (Polynomial.C (m : ℚ) - Polynomial.X) = -1 := by simp
  rw [hd] at h
  have h2 : (-1 : Polynomial ℚ)
      * (Polynomial.derivative F).comp (Polynomial.C (m : ℚ) - Polynomial.X)
      = -((Polynomial.derivative F).comp (Polynomial.C (m : ℚ) - Polynomial.X)) := by
    rw [neg_one_mul]
  rw [h2] at h
  rw [h, neg_neg]
private theorem poly_deriv_comp_shift (F : Polynomial ℚ) (m : ℕ) :
    (Polynomial.derivative F).comp (Polynomial.X + Polynomial.C (m : ℚ))
    = Polynomial.derivative (F.comp (Polynomial.X + Polynomial.C (m : ℚ))) := by
  have h := Polynomial.derivative_comp F (Polynomial.X + Polynomial.C (m : ℚ))
  have hd : Polynomial.derivative (Polynomial.X + Polynomial.C (m : ℚ)) = 1 := by simp
  rw [hd] at h
  rw [one_mul] at h
  exact h.symm
private theorem poly_iterate_deriv_comp_neg (k : ℕ) (F : Polynomial ℚ) (m : ℕ) :
    ((Polynomial.derivative ^[k]) F).comp (Polynomial.C (m : ℚ) - Polynomial.X)
    = ((-1 : ℚ) ^ k) •
      ((Polynomial.derivative ^[k]) (F.comp (Polynomial.C (m : ℚ) - Polynomial.X))) := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    have h1 := poly_deriv_comp_neg (((Polynomial.derivative ^[k]) F)) m
    have h2 := ih F
    simp only [Function.iterate_succ_apply'] at h1 h2 ⊢
    rw [h1, h2, map_smul]
    have hpow : (-1 : ℚ) ^ (k + 1) = -((-1 : ℚ) ^ k) := by ring
    rw [hpow, neg_smul]
private theorem poly_iterate_deriv_comp_shift (k : ℕ) (F : Polynomial ℚ) (m : ℕ) :
    ((Polynomial.derivative ^[k]) F).comp (Polynomial.X + Polynomial.C (m : ℚ))
    = ((Polynomial.derivative ^[k]) (F.comp (Polynomial.X + Polynomial.C (m : ℚ)))) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    have h1 := poly_deriv_comp_shift (((Polynomial.derivative ^[k]) F)) m
    have h2 := ih F
    simp only [Function.iterate_succ_apply'] at h1 h2 ⊢
    rw [h1, h2]
private theorem poly_shifted (n r m : ℕ) :
    ((Polynomial.X ^ (n + r) * (Polynomial.X - Polynomial.C (m : ℚ)) ^ (n + r) : Polynomial ℚ)).comp
      (Polynomial.X + Polynomial.C (m : ℚ))
    = (Polynomial.X + Polynomial.C (m : ℚ)) ^ (n + r) * Polynomial.X ^ (n + r) := by
  have hsub : (Polynomial.X - Polynomial.C (m : ℚ)).comp (Polynomial.X + Polynomial.C (m : ℚ))
      = Polynomial.X := by
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel_right]
  rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.pow_comp, Polynomial.X_comp, hsub]
private theorem left_expansion (n r m : ℕ) :
    myL (((Polynomial.derivative ^[r])
      (Polynomial.X ^ (n + r) *
        (Polynomial.X - Polynomial.C (m : ℚ)) ^ (n + r) : Polynomial ℚ)).comp
      (Polynomial.X + Polynomial.C (m : ℚ)))
    = (Nat.factorial r : ℚ) * ∑ k ∈ Finset.range (n + r + 1),
      ((m : ℚ) ^ (n + r - k) * (Nat.choose (n + r) k : ℚ)
        * (Nat.choose (n + k + r) r : ℚ) * _root_.bernoulli (n + k)) := by
  have hexpand : ((Polynomial.X ^ (n + r) *
      (Polynomial.X - Polynomial.C (m : ℚ)) ^ (n + r) : Polynomial ℚ)).comp
        (Polynomial.X + Polynomial.C (m : ℚ))
      = ∑ k ∈ Finset.range (n + r + 1),
        Polynomial.C (((m : ℚ) ^ (n + r - k) * (Nat.choose (n + r) k : ℚ)))
          * Polynomial.X ^ (n + r + k) := by
    rw [poly_shifted, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hc : ((Nat.choose (n + r) k : Polynomial ℚ))
        = Polynomial.C ((Nat.choose (n + r) k : ℚ)) := by
      exact_mod_cast rfl
    have e1 : (Polynomial.X ^ k * Polynomial.X ^ (n + r) : Polynomial ℚ)
        = Polynomial.X ^ (n + r + k) := by
      rw [← pow_add, add_comm k]
    have tk : (Polynomial.X ^ k * Polynomial.C (m : ℚ) ^ (n + r - k)
        * (↑(Nat.choose (n + r) k) : Polynomial ℚ)
          * Polynomial.X ^ (n + r))
        = Polynomial.C (((m : ℚ) ^ (n + r - k) * (Nat.choose (n + r) k : ℚ)))
          * Polynomial.X ^ (n + r + k) := by
      have step1 : (Polynomial.X ^ k * Polynomial.C (m : ℚ) ^ (n + r - k)
            * (↑(Nat.choose (n + r) k) : Polynomial ℚ)
            * Polynomial.X ^ (n + r))
          = (Polynomial.C (((m : ℚ) ^ (n + r - k))) * Polynomial.C ((Nat.choose (n + r) k : ℚ)))
            * (Polynomial.X ^ k * Polynomial.X ^ (n + r)) := by
        rw [hc, ← Polynomial.C_pow]
        ring
      rw [step1, ← Polynomial.C_mul, e1]
    exact tk
  rw [poly_iterate_deriv_comp_shift, hexpand, Polynomial.iterate_derivative_sum,
    map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hsub : n + r + k - r = n + k := by omega
  have hcho : Nat.choose (n + r + k) r = Nat.choose (n + k + r) r := by congr 1; omega
  have hdf : (Nat.descFactorial (n + r + k) r : ℚ)
      = (Nat.factorial r : ℚ) * (Nat.choose (n + r + k) r : ℚ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (n + r + k) r
  rw [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_C_mul,
    ← mul_assoc, ← Polynomial.C_mul, myL_C_mul, myL_X_pow, hsub, hdf, hcho]
  ring
private theorem right_expansion (n r m k : ℕ) :
    Polynomial.eval (k : ℚ) (Polynomial.derivative (((Polynomial.derivative ^[r])
      (Polynomial.X ^ (n + r) * (Polynomial.X - Polynomial.C (m : ℚ)) ^ (n + r) : Polynomial ℚ))))
    = (Nat.factorial (r + 1) : ℚ) * ∑ j ∈ Finset.range (r + 2),
      ((Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ)
        * (k : ℚ) ^ (n + r - (r + 1 - j)) * ((k : ℚ) - (m : ℚ)) ^ (n + r - j)) := by
  have hiter : Polynomial.derivative (((Polynomial.derivative ^[r])
      (Polynomial.X ^ (n + r) * (Polynomial.X - Polynomial.C (m : ℚ)) ^ (n + r) : Polynomial ℚ)))
      = ((Polynomial.derivative ^[r + 1])
        (Polynomial.X ^ (n + r) *
          (Polynomial.X - Polynomial.C (m : ℚ)) ^ (n + r) : Polynomial ℚ)) := by
    rw [Function.iterate_succ_apply']
  rw [hiter, Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hA := Polynomial.iterate_derivative_X_pow_eq_C_mul (R := ℚ) (n + r) (r + 1 - j)
  have hB := Polynomial.iterate_derivative_X_sub_pow (R := ℚ) (n + r) j (m : ℚ)
  have hcoef : (Nat.choose (r + 1) j : ℚ) * (Nat.descFactorial (n + r) (r + 1 - j) : ℚ)
        * (Nat.descFactorial (n + r) j : ℚ)
      = (Nat.factorial (r + 1) : ℚ)
        * (Nat.choose (n + r) (r + 1 - j) : ℚ) * (Nat.choose (n + r) j : ℚ) := by
    have hd1 : (Nat.descFactorial (n + r) (r + 1 - j) : ℚ)
        = (Nat.factorial (r + 1 - j) : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ) := by
      exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (n + r) (r + 1 - j)
    have hd2 : (Nat.descFactorial (n + r) j : ℚ)
        = (Nat.factorial j : ℚ) * (Nat.choose (n + r) j : ℚ) := by
      exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (n + r) j
    rw [hd1, hd2]
    have hle : j ≤ r + 1 := by
      have := Finset.mem_range.mp hj
      omega
    have hcc : Nat.choose (r + 1) j * Nat.factorial j * Nat.factorial (r + 1 - j)
        = Nat.factorial (r + 1) :=
      Nat.choose_mul_factorial_mul_factorial hle
    have hccQ : (Nat.choose (r + 1) j : ℚ) * (Nat.factorial j : ℚ) * (Nat.factorial (r + 1 - j) : ℚ)
        = (Nat.factorial (r + 1) : ℚ) := by
      exact_mod_cast hcc
    linear_combination hccQ * (Nat.choose (n + r) (r + 1 - j) : ℚ) * (Nat.choose (n + r) j : ℚ)
  simp only [hA, hB, nsmul_eq_mul, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_natCast]
  linear_combination hcoef * (k : ℚ) ^ (n + r - (r + 1 - j)) * ((k : ℚ) - (m : ℚ)) ^ (n + r - j)
private theorem zpow_term (n r m k j : ℕ) (hj : j < r + 2) :
    (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ)
      * (k : ℚ) ^ (n + r - (r + 1 - j)) * ((k : ℚ) - (m : ℚ)) ^ (n + r - j)
    = (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ)
      * (k : ℚ) ^ ((j : ℤ) + (n : ℤ) - 1)
        * (((k : ℚ) - (m : ℚ)) ^ ((n : ℤ) + (r : ℤ) - (j : ℤ))) := by
  by_cases h0 : Nat.choose (n + r) j * Nat.choose (n + r) (r + 1 - j) = 0
  · have h0Q : (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ) = 0 := by
      exact_mod_cast h0
    have eL : (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ)
        * (k : ℚ) ^ (n + r - (r + 1 - j)) * ((k : ℚ) - (m : ℚ)) ^ (n + r - j) = 0 := by
      have : (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ)
          * (k : ℚ) ^ (n + r - (r + 1 - j)) * ((k : ℚ) - (m : ℚ)) ^ (n + r - j)
          = ((Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ))
            * ((k : ℚ) ^ (n + r - (r + 1 - j)) * ((k : ℚ) - (m : ℚ)) ^ (n + r - j)) := by ring
      rw [this, h0Q, zero_mul]
    have eR : (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ)
        * (k : ℚ) ^ ((j : ℤ) + (n : ℤ) - 1)
          * (((k : ℚ) - (m : ℚ)) ^ ((n : ℤ) + (r : ℤ) - (j : ℤ))) = 0 := by
      have : (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ)
          * (k : ℚ) ^ ((j : ℤ) + (n : ℤ) - 1)
            * (((k : ℚ) - (m : ℚ)) ^ ((n : ℤ) + (r : ℤ) - (j : ℤ)))
          = ((Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ))
            * ((k : ℚ) ^ ((j : ℤ) + (n : ℤ) - 1)
              * (((k : ℚ) - (m : ℚ)) ^ ((n : ℤ) + (r : ℤ) - (j : ℤ)))) := by ring
      rw [this, h0Q, zero_mul]
    rw [eL, eR]
  · have hj1 : j ≤ n + r := by
      by_contra hc
      have hlt : n + r < j := Nat.lt_of_not_le hc
      have hz : Nat.choose (n + r) j = 0 := Nat.choose_eq_zero_of_lt hlt
      have hz2 : Nat.choose (n + r) j * Nat.choose (n + r) (r + 1 - j) = 0 := by
        rw [hz, zero_mul]
      exact h0 hz2
    have hj2 : r + 1 - j ≤ n + r := by
      by_contra hc
      have hlt : n + r < r + 1 - j := Nat.lt_of_not_le hc
      have hz : Nat.choose (n + r) (r + 1 - j) = 0 := Nat.choose_eq_zero_of_lt hlt
      have hz2 : Nat.choose (n + r) j * Nat.choose (n + r) (r + 1 - j) = 0 := by
        rw [hz, mul_zero]
      exact h0 hz2
    have hle : j ≤ r + 1 := by omega
    have e1 : ((j : ℤ) + (n : ℤ) - 1) = (((n + r - (r + 1 - j) : ℕ)) : ℤ) := by
      rw [Nat.cast_sub hj2, Nat.cast_sub hle]
      push_cast
      omega
    have e2 : ((n : ℤ) + (r : ℤ) - (j : ℤ)) = (((n + r - j : ℕ)) : ℤ) := by
      rw [Nat.cast_sub hj1]
      push_cast
      ring
    rw [e1, e2, zpow_natCast, zpow_natCast]
private theorem q_antisym (n r m : ℕ) (hr : Odd r) :
    (((Polynomial.derivative ^[r])
      (Polynomial.X ^ (n + r) *
        (Polynomial.X - Polynomial.C (m : ℚ)) ^ (n + r) : Polynomial ℚ)).comp
      (Polynomial.C (m : ℚ) - Polynomial.X))
    = -(((Polynomial.derivative ^[r])
      (Polynomial.X ^ (n + r) *
        (Polynomial.X - Polynomial.C (m : ℚ)) ^ (n + r) : Polynomial ℚ))) := by
  have h := poly_iterate_deriv_comp_neg r
    (Polynomial.X ^ (n + r) * (Polynomial.X - Polynomial.C (m : ℚ)) ^ (n + r) : Polynomial ℚ) m
  rw [base_invariance (n + r) m, hr.neg_one_pow] at h
  simp only [neg_one_smul] at h
  exact h

/-- **Gessel's Bernoulli-number identity.** Let $B_j$ denote the $j$-th Bernoulli number, with
$B_1 = -1/2$. For all natural numbers $n$, $r$ and $m$ with $r$ odd and $m \ge 1$,
$$\sum_{k=0}^{n+r} m^{n+r-k} \binom{n+r}{k} \binom{n+k+r}{r} B_{n+k} =
\frac{r+1}{2} \sum_{k=1}^{m-1} \sum_{j=0}^{r+1} \binom{n+r}{j} \binom{n+r}{r+1-j}
k^{j+n-1} (k-m)^{n+r-j}.$$

The powers on the right have integer exponents and nonzero rational bases: for $n = 0$ the terms
$j = 0$ and $j = r + 1$ have exponent $-1$.

Proves `Wanted` entry `gessel_bernoulli_number_identity`.

Source: Redha Chellal and Farid Bencherif, *An Identity for Generalized
Bernoulli Polynomials*, Journal of Integer Sequences 23 (2020), Article 20.11.2,
formula `t5` (the special case `ℓ = n` with `r` odd), lines 142–149,
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.tex>.
Quoted there from H. Belbachir and M. Rahmani, *On Gessel-Kaneko's identity
for Bernoulli numbers*, Appl. Anal. Discrete Math. 7 (2013), 1–10.
Original: I. M. Gessel, *Applications of the classical umbral calculus*,
Algebra Universalis 49 (2003), 397–434.
-/
theorem gessel_bernoulli_number_identity (n r m : ℕ) (hr : Odd r) (hm : 1 ≤ m) :
    Finset.sum (Finset.range (n + r + 1)) (fun k =>
      (m : ℚ) ^ (n + r - k) * (Nat.choose (n + r) k : ℚ) *
        (Nat.choose (n + k + r) r : ℚ) * bernoulli (n + k)) =
    (((r : ℚ) + 1) / 2) * Finset.sum (Finset.Ico 1 m) (fun k =>
      Finset.sum (Finset.range (r + 2)) (fun j =>
        (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ) *
          (k : ℚ) ^ ((j : ℤ) + (n : ℤ) - 1) *
            (((k : ℚ) - (m : ℚ)) ^ ((n : ℤ) + (r : ℤ) - (j : ℤ))))) := by
  have hAnti := q_antisym n r m hr
  have hHalf := antisym_halving
    (((Polynomial.derivative ^[r])
      (Polynomial.X ^ (n + r) *
        (Polynomial.X - Polynomial.C (m : ℚ)) ^ (n + r) : Polynomial ℚ))) m hm hAnti
  have hLeft := left_expansion n r m
  have hRight : ∀ k ∈ Finset.Ico 1 m,
      Polynomial.eval (k : ℚ) (Polynomial.derivative (((Polynomial.derivative ^[r])
        (Polynomial.X ^ (n + r) * (Polynomial.X - Polynomial.C (m : ℚ)) ^ (n + r) : Polynomial ℚ))))
      = (Nat.factorial (r + 1) : ℚ) * Finset.sum (Finset.range (r + 2)) (fun j =>
        (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ) *
          (k : ℚ) ^ ((j : ℤ) + (n : ℤ) - 1) *
            (((k : ℚ) - (m : ℚ)) ^ ((n : ℤ) + (r : ℤ) - (j : ℤ)))) := by
    intro k hk
    rw [right_expansion n r m k]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj2 : j < r + 2 := Finset.mem_range.mp hj
    exact zpow_term n r m k j hj2
  have hSum : Finset.sum (Finset.Ico 1 m) (fun k => Polynomial.eval (k : ℚ) (Polynomial.derivative
      (((Polynomial.derivative ^[r])
        (Polynomial.X ^ (n + r) *
          (Polynomial.X - Polynomial.C (m : ℚ)) ^ (n + r) : Polynomial ℚ)))))
      = (Nat.factorial (r + 1) : ℚ) * Finset.sum (Finset.Ico 1 m) (fun k =>
        Finset.sum (Finset.range (r + 2)) (fun j =>
          (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ) *
            (k : ℚ) ^ ((j : ℤ) + (n : ℤ) - 1) *
              (((k : ℚ) - (m : ℚ)) ^ ((n : ℤ) + (r : ℤ) - (j : ℤ))))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hRight k hk
  have hCombined : (Nat.factorial r : ℚ) * Finset.sum (Finset.range (n + r + 1)) (fun k =>
        (m : ℚ) ^ (n + r - k) * (Nat.choose (n + r) k : ℚ) *
          (Nat.choose (n + k + r) r : ℚ) * _root_.bernoulli (n + k))
      = (1 / 2) * ((Nat.factorial (r + 1) : ℚ) * Finset.sum (Finset.Ico 1 m) (fun k =>
        Finset.sum (Finset.range (r + 2)) (fun j =>
          (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ) *
            (k : ℚ) ^ ((j : ℤ) + (n : ℤ) - 1) *
              (((k : ℚ) - (m : ℚ)) ^ ((n : ℤ) + (r : ℤ) - (j : ℤ)))))) := by
    linear_combination hLeft.symm.trans hHalf + (1 / 2) * hSum
  have hfr : (Nat.factorial r : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hfac : (Nat.factorial (r + 1) : ℚ) = ((r : ℚ) + 1) * (Nat.factorial r : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfac] at hCombined
  have h2 : (Nat.factorial r : ℚ) * Finset.sum (Finset.range (n + r + 1)) (fun k =>
        (m : ℚ) ^ (n + r - k) * (Nat.choose (n + r) k : ℚ) *
          (Nat.choose (n + k + r) r : ℚ) * _root_.bernoulli (n + k))
      = (Nat.factorial r : ℚ) * ((((r : ℚ) + 1) / 2) * Finset.sum (Finset.Ico 1 m) (fun k =>
        Finset.sum (Finset.range (r + 2)) (fun j =>
          (Nat.choose (n + r) j : ℚ) * (Nat.choose (n + r) (r + 1 - j) : ℚ) *
            (k : ℚ) ^ ((j : ℤ) + (n : ℤ) - 1) *
              (((k : ℚ) - (m : ℚ)) ^ ((n : ℤ) + (r : ℤ) - (j : ℤ)))))) := by
    linear_combination hCombined
  exact mul_left_cancel₀ hfr h2

end MetaMathlibExt
end
