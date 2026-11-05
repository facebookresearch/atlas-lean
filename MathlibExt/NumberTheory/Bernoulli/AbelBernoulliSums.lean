/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace MetaMathlibExt

open Finset Nat Polynomial

/-- Finite-difference sum: S(m,j,x) = ∑_{l=0}^m C(m,l) (-1)^{m-l} (x+l)^j. -/
private noncomputable def S (m j : ℕ) (x : ℂ) : ℂ :=
  ∑ l ∈ Finset.range (m + 1), (Nat.choose m l : ℂ) * (-1 : ℂ) ^ (m - l) * (x + (l : ℂ)) ^ j

/-- Auxiliary summand for the reindexed sum. -/
private noncomputable def g (m j : ℕ) (x : ℂ) : ℕ → ℂ :=
  fun k => (Nat.choose m k : ℂ) * (-1 : ℂ) ^ (m + 1 - k) * (x + (k : ℂ)) ^ j

/-- Pascal recurrence for the finite-difference sum. -/
private theorem pascal_identity (m j : ℕ) (x : ℂ) :
    S (m + 1) j x = S m j (x + 1) - S m j x := by
  have hpow : ∀ k : ℕ, k ≤ m → ((-1 : ℂ) ^ (m + 1 - k) = -(-1 : ℂ) ^ (m - k)) := by
    intro k hk
    have h : m + 1 - k = (m - k) + 1 := by omega
    rw [h, pow_succ]
    ring
  have hcast : ∀ k : ℕ, (x + ((k + 1 : ℕ) : ℂ)) = ((x + 1) + (k : ℂ)) := by
    intro k; push_cast; ring
  have hexp : ∀ k : ℕ, m + 1 - (k + 1) = m - k := by intro k; omega
  have hFGH : ∀ k : ℕ,
      (Nat.choose (m + 1) (k + 1) : ℂ) * (-1 : ℂ) ^ (m + 1 - (k + 1)) *
        (x + ((k + 1 : ℕ) : ℂ)) ^ j
      = (Nat.choose m k : ℂ) * (-1 : ℂ) ^ (m - k) * ((x + 1) + (k : ℂ)) ^ j
      + (Nat.choose m (k + 1) : ℂ) * (-1 : ℂ) ^ (m - k) * ((x + 1) + (k : ℂ)) ^ j := by
    intro k
    rw [hexp k, hcast k, Nat.choose_succ_succ]
    push_cast
    ring
  have hG : (∑ k ∈ Finset.range (m + 1),
      (Nat.choose m k : ℂ) * (-1 : ℂ) ^ (m - k) * ((x + 1) + (k : ℂ)) ^ j)
      = S m j (x + 1) := rfl
  have hF0 : ((Nat.choose (m + 1) 0 : ℂ) * (-1 : ℂ) ^ (m + 1 - 0) *
      (x + ((0 : ℕ) : ℂ)) ^ j)
      = ((Nat.choose m 0 : ℂ) * (-1 : ℂ) ^ (m + 1 - 0) * (x + ((0 : ℕ) : ℂ)) ^ j) := by
    simp [Nat.choose_zero_right]
  have hgH : ∀ k : ℕ, g m j x (k + 1)
      = (Nat.choose m (k + 1) : ℂ) * (-1 : ℂ) ^ (m - k) * ((x + 1) + (k : ℂ)) ^ j := by
    intro k
    show (Nat.choose m (k+1) : ℂ) * (-1 : ℂ) ^ (m + 1 - (k+1)) * (x + ((k+1 : ℕ) : ℂ)) ^ j = _
    rw [hexp k, hcast k]
  have hg0 : g m j x 0
      = ((Nat.choose m 0 : ℂ) * (-1 : ℂ) ^ (m + 1 - 0) * (x + ((0 : ℕ) : ℂ)) ^ j) := rfl
  have hgsucc : (∑ k ∈ Finset.range (m + 2), g m j x k)
      = (∑ k ∈ Finset.range (m + 1), g m j x (k + 1)) + g m j x 0 :=
    Finset.sum_range_succ' (g m j x) (m + 1)
  have hglast : (∑ k ∈ Finset.range (m + 2), g m j x k)
      = (∑ k ∈ Finset.range (m + 1), g m j x k) + g m j x (m + 1) :=
    Finset.sum_range_succ (g m j x) (m + 1)
  have hgmlast : g m j x (m + 1) = 0 := by
    show (Nat.choose m (m+1) : ℂ) * (-1 : ℂ) ^ (m + 1 - (m+1)) * (x + ((m+1 : ℕ) : ℂ)) ^ j = 0
    have : Nat.choose m (m + 1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m)
    rw [this]
    simp
  have hgneg : (∑ k ∈ Finset.range (m + 1), g m j x k) = -(S m j x) := by
    have hterm : ∀ k ∈ Finset.range (m + 1), g m j x k =
        -((Nat.choose m k : ℂ) * (-1 : ℂ) ^ (m - k) * (x + (k : ℂ)) ^ j) := by
      intro k hk
      have hkle : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      show (Nat.choose m k : ℂ) * (-1 : ℂ) ^ (m + 1 - k) * (x + (k : ℂ)) ^ j = _
      rw [hpow k hkle]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    rfl
  have hsub : (∑ k ∈ Finset.range (m + 1), g m j x (k + 1))
      = (∑ k ∈ Finset.range (m + 2), g m j x k) - g m j x 0 := by
    rw [hgsucc]; ring
  have hH : (∑ k ∈ Finset.range (m + 1),
      (Nat.choose m (k + 1) : ℂ) * (-1 : ℂ) ^ (m - k) * ((x + 1) + (k : ℂ)) ^ j)
      = -(S m j x) - ((Nat.choose (m + 1) 0 : ℂ) * (-1 : ℂ) ^ (m + 1 - 0) *
        (x + ((0 : ℕ) : ℂ)) ^ j) := by
    have e1 : (∑ k ∈ Finset.range (m + 1),
        (Nat.choose m (k + 1) : ℂ) * (-1 : ℂ) ^ (m - k) * ((x + 1) + (k : ℂ)) ^ j)
        = (∑ k ∈ Finset.range (m + 1), g m j x (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (hgH k).symm
    rw [e1, hsub, hglast, hgmlast, add_zero, hgneg, hg0, ← hF0]
  have key : S (m + 1) j x
      = (∑ k ∈ Finset.range (m + 1),
          (Nat.choose m k : ℂ) * (-1 : ℂ) ^ (m - k) * ((x + 1) + (k : ℂ)) ^ j)
      + (∑ k ∈ Finset.range (m + 1),
          (Nat.choose m (k + 1) : ℂ) * (-1 : ℂ) ^ (m - k) * ((x + 1) + (k : ℂ)) ^ j)
      + ((Nat.choose (m + 1) 0 : ℂ) * (-1 : ℂ) ^ (m + 1 - 0) *
          (x + ((0 : ℕ) : ℂ)) ^ j) := by
    unfold S
    rw [Finset.sum_range_succ']
    rw [Finset.sum_congr rfl (fun k _ => hFGH k)]
    rw [Finset.sum_add_distrib]
  rw [key, hG, hH]
  ring

/-- The m-th finite difference of a degree-j < m polynomial in x vanishes. -/
private theorem fd_vanish (m : ℕ) : ∀ (j : ℕ), j < m → ∀ (x : ℂ), S m j x = 0 := by
  induction m with
  | zero =>
    intro j hj x
    omega
  | succ m IH =>
    intro j hj x
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hj) with hjm | hlt
    · obtain rfl := hjm.symm
      -- diagonal case j = m
      rw [pascal_identity m m x]
      have key : ∀ A : ℂ, S m m A
          = ∑ l ∈ Finset.range (m + 1),
            (Nat.choose m l : ℂ) * (-1 : ℂ) ^ (m - l) * (l : ℂ) ^ m := by
        intro A
        unfold S
        have hexpand : ∀ l : ℕ, (A + (l : ℂ)) ^ m
            = ∑ k ∈ Finset.range (m + 1),
              A ^ k * (l : ℂ) ^ (m - k) * ((Nat.choose m k : ℕ) : ℂ) := by
          intro l
          rw [add_pow]
        simp_rw [hexpand, Finset.mul_sum]
        rw [Finset.sum_comm]
        rw [Finset.sum_eq_single 0]
        · apply Finset.sum_congr rfl
          intro l _
          simp [pow_zero, Nat.choose_zero_right]
        · intro k hk hk0
          have hkle : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          have hkm : m - k < m := by omega
          have h0 : (∑ l ∈ Finset.range (m + 1),
                (Nat.choose m l : ℂ) * (-1 : ℂ) ^ (m - l) * (l : ℂ) ^ (m - k)) = 0 := by
            have hIH := IH (m - k) hkm 0
            unfold S at hIH
            simpa using hIH
          have hfactor : (∑ l ∈ Finset.range (m + 1),
                (Nat.choose m l : ℂ) * (-1 : ℂ) ^ (m - l) *
                  (A ^ k * (l : ℂ) ^ (m - k) * ((Nat.choose m k : ℕ) : ℂ)))
              = (A ^ k * ((Nat.choose m k : ℕ) : ℂ)) *
                (∑ l ∈ Finset.range (m + 1),
                  (Nat.choose m l : ℂ) * (-1 : ℂ) ^ (m - l) * (l : ℂ) ^ (m - k)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            ring
          rw [hfactor, h0, mul_zero]
        · simp
      rw [key (x + 1), key x, sub_self]
    · -- off-diagonal case j < m
      rw [pascal_identity m j x, IH j hlt (x + 1), IH j hlt x, sub_self]

/-- Absorption identity for binomial coefficients. -/
private theorem choose_succ_mul (m l : ℕ) (hl : l ≤ m + 1) :
    Nat.choose (m + 1) l * (m + 1 - l) = (m + 1) * Nat.choose m l := by
  rcases eq_or_lt_of_le hl with hlm | hlt
  · obtain rfl := hlm.symm
    simp [Nat.choose_self]
  · have hle : l ≤ m := by omega
    have hfact1 : (m + 1 - l)! = (m + 1 - l) * (m - l)! := by
      have h : m + 1 - l = (m - l) + 1 := by omega
      rw [h, Nat.factorial_succ]
    have e1 := Nat.choose_mul_factorial_mul_factorial (n := m + 1) (k := l) hl
    have e2 := Nat.choose_mul_factorial_mul_factorial (n := m) (k := l) hle
    have e3 := Nat.factorial_succ m
    have key : (l ! * (m - l)!) * (Nat.choose (m + 1) l * (m + 1 - l))
        = (l ! * (m - l)!) * ((m + 1) * Nat.choose m l) := by
      calc (l ! * (m - l)!) * (Nat.choose (m + 1) l * (m + 1 - l))
          = Nat.choose (m + 1) l * l ! * ((m + 1 - l) * (m - l)!) := by ring
        _ = Nat.choose (m + 1) l * l ! * (m + 1 - l)! := by rw [← hfact1]
        _ = (m + 1)! := e1
        _ = (m + 1) * m ! := e3
        _ = (l ! * (m - l)!) * ((m + 1) * Nat.choose m l) := by
            rw [← e2]; ring
    have hD : l ! * (m - l)! ≠ 0 :=
      ne_of_gt (Nat.mul_pos (Nat.factorial_pos l) (Nat.factorial_pos _))
    exact mul_left_cancel₀ hD key

/-- Abel summand factor: x * (x + l)^{l-1}, via zpow to include l = 0. -/
private noncomputable def abelCoeff (x : ℂ) (l : ℕ) : ℂ := x * (x + (l : ℂ)) ^ ((l : ℤ) - 1)

private theorem abelCoeff_zero (x : ℂ) (hx : x ≠ 0) : abelCoeff x 0 = 1 := by
  have hexp : ((0 : ℕ) : ℤ) - 1 = -1 := by norm_num
  unfold abelCoeff
  rw [hexp]
  simp only [Nat.cast_zero, add_zero, zpow_neg_one]
  exact mul_inv_cancel₀ hx

private theorem abelCoeff_succ (x : ℂ) (l : ℕ) :
    abelCoeff x (l + 1) = x * (x + ((l + 1 : ℕ) : ℂ)) ^ l := by
  have hexp : (((l + 1 : ℕ)) : ℤ) - 1 = ((l : ℕ) : ℤ) := by omega
  unfold abelCoeff
  rw [hexp, zpow_natCast]

/-- Recombination of the Abel factor with the negated base at the eval point. -/
private theorem abelCoeff_term (x : ℂ) (hx : x ≠ 0) (m l : ℕ) (hl : l ≤ m + 1) :
    abelCoeff x l * (-x - (l : ℂ)) ^ (m + 1 - l)
      = x * ((-1 : ℂ) ^ (m + 1 - l) * (x + (l : ℂ)) ^ m) := by
  rcases Nat.eq_zero_or_pos l with rfl | hpos
  · rw [abelCoeff_zero x hx]
    simp only [Nat.cast_zero, sub_zero, one_mul, add_zero]
    have h1 : m + 1 - 0 = m + 1 := by omega
    rw [h1, neg_pow]
    have hps : x ^ (m + 1) = x * x ^ m := pow_succ' x m
    rw [hps]
    ring
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
    have hkm : k ≤ m := by omega
    have step : x * (x + ((k + 1 : ℕ) : ℂ)) ^ k *
          ((-1 : ℂ) ^ (m + 1 - (k + 1)) * (x + ((k + 1 : ℕ) : ℂ)) ^ (m + 1 - (k + 1)))
        = x * ((-1 : ℂ) ^ (m + 1 - (k + 1)) * (x + ((k + 1 : ℕ) : ℂ)) ^ m) := by
      have hcombine : (x + ((k + 1 : ℕ) : ℂ)) ^ k * (x + ((k + 1 : ℕ) : ℂ)) ^ (m + 1 - (k + 1))
          = (x + ((k + 1 : ℕ) : ℂ)) ^ m := by
        have hexp2 : k + (m + 1 - (k + 1)) = m := by omega
        rw [← pow_add, hexp2]
      calc x * (x + ((k + 1 : ℕ) : ℂ)) ^ k *
              ((-1 : ℂ) ^ (m + 1 - (k + 1)) * (x + ((k + 1 : ℕ) : ℂ)) ^ (m + 1 - (k + 1)))
          = x * ((-1 : ℂ) ^ (m + 1 - (k + 1)) *
              ((x + ((k + 1 : ℕ) : ℂ)) ^ k * (x + ((k + 1 : ℕ) : ℂ)) ^ (m + 1 - (k + 1)))) := by
            ring
        _ = x * ((-1 : ℂ) ^ (m + 1 - (k + 1)) * (x + ((k + 1 : ℕ) : ℂ)) ^ m) := by
            rw [hcombine]
    have hneg : -x - (((k + 1 : ℕ)) : ℂ) = -((x + ((k + 1 : ℕ) : ℂ))) := by ring
    rw [abelCoeff_succ, hneg, neg_pow]
    exact step

/-- The Abel sum as a polynomial in the second argument. -/
private noncomputable def AbelPoly (x : ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ l ∈ Finset.range (m + 1),
    Polynomial.C ((Nat.choose m l : ℂ) * abelCoeff x l) *
      (Polynomial.X - Polynomial.C (l : ℂ)) ^ (m - l)

/-- Abel's binomial theorem, polynomial form. -/
private theorem abel_poly (x : ℂ) (hx : x ≠ 0) (m : ℕ) :
    AbelPoly x m = (Polynomial.X + Polynomial.C x) ^ m := by
  induction m with
  | zero =>
    unfold AbelPoly
    rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
    rw [abelCoeff_zero x hx]
    simp
  | succ m IH =>
    have hCH : ∀ l : ℕ, l ≤ m →
        ((Nat.choose (m + 1) l : ℂ) * abelCoeff x l) * ((m + 1 - l : ℕ) : ℂ)
          = ((m + 1 : ℕ) : ℂ) * ((Nat.choose m l : ℂ) * abelCoeff x l) := by
      intro l hlm
      have h := choose_succ_mul m l (by omega)
      have hc : (Nat.choose (m + 1) l : ℂ) * ((m + 1 - l : ℕ) : ℂ)
          = ((m + 1 : ℕ) : ℂ) * (Nat.choose m l : ℂ) := by exact_mod_cast h
      linear_combination (abelCoeff x l) * hc
    have hterm : ∀ l ∈ Finset.range (m + 1),
        (Polynomial.C ((Nat.choose (m + 1) l : ℂ) * abelCoeff x l) *
          (Polynomial.X - Polynomial.C (l : ℂ)) ^ (m + 1 - l)).derivative
        = Polynomial.C ((m + 1 : ℕ) : ℂ) *
          (Polynomial.C ((Nat.choose m l : ℂ) * abelCoeff x l) *
            (Polynomial.X - Polynomial.C (l : ℂ)) ^ (m - l)) := by
      intro l hl
      have hlm : l ≤ m := by have := Finset.mem_range.mp hl; omega
      have he2 : m + 1 - l - 1 = m - l := by omega
      have eP : ((Polynomial.X - Polynomial.C (l : ℂ)) ^ (m + 1 - l)).derivative
          = Polynomial.C ((m + 1 - l : ℕ) : ℂ) *
            (Polynomial.X - Polynomial.C (l : ℂ)) ^ (m - l) := by
        rw [Polynomial.derivative_pow, Polynomial.derivative_X_sub_C, mul_one, he2]
      rw [Polynomial.derivative_C_mul, eP, ← mul_assoc, ← Polynomial.C_mul, hCH l hlm,
        Polynomial.C_mul, mul_assoc]
    have hlast : (Polynomial.C ((Nat.choose (m + 1) (m + 1) : ℂ) * abelCoeff x (m + 1)) *
        (Polynomial.X - Polynomial.C ((m + 1 : ℕ) : ℂ)) ^ (m + 1 - (m + 1))).derivative = 0 := by
      simp
    have hF : (AbelPoly x (m + 1)).derivative
        = Polynomial.C ((m + 1 : ℕ) : ℂ) * AbelPoly x m := by
      have hsum : (AbelPoly x (m + 1)).derivative
          = (∑ l ∈ Finset.range (m + 1),
              Polynomial.C ((m + 1 : ℕ) : ℂ) *
                (Polynomial.C ((Nat.choose m l : ℂ) * abelCoeff x l) *
                  (Polynomial.X - Polynomial.C (l : ℂ)) ^ (m - l))) := by
        unfold AbelPoly
        rw [Polynomial.derivative_sum, Finset.sum_range_succ, hlast, add_zero]
        exact Finset.sum_congr rfl (fun l hl => hterm l hl)
      rw [hsum, ← Finset.mul_sum]
      rfl
    have hG : ((Polynomial.X + Polynomial.C x) ^ (m + 1)).derivative
        = Polynomial.C ((m + 1 : ℕ) : ℂ) * (Polynomial.X + Polynomial.C x) ^ m := by
      rw [Polynomial.derivative_pow]
      simp only [Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
        add_zero, mul_one]
      rw [Nat.add_sub_cancel]
    have hDderiv : (AbelPoly x (m + 1) - (Polynomial.X + Polynomial.C x) ^ (m + 1)).derivative
        = 0 := by
      rw [Polynomial.derivative_sub, hF, hG, IH, sub_self]
    have hFeval : (AbelPoly x (m + 1)).eval (-x) = x * S (m + 1) m x := by
      unfold AbelPoly
      rw [Polynomial.eval_finsetSum]
      have hrange : m + 1 + 1 = m + 2 := by omega
      rw [hrange]
      have hterm_eval : ∀ l ∈ Finset.range (m + 2),
          (Polynomial.C ((Nat.choose (m + 1) l : ℂ) * abelCoeff x l) *
            (Polynomial.X - Polynomial.C (l : ℂ)) ^ (m + 1 - l)).eval (-x)
          = (Nat.choose (m + 1) l : ℂ) * (x * ((-1 : ℂ) ^ (m + 1 - l) * (x + (l : ℂ)) ^ m)) := by
        intro l hl
        have hlm : l ≤ m + 1 := by have := Finset.mem_range.mp hl; omega
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
        have ht := abelCoeff_term x hx m l hlm
        linear_combination (Nat.choose (m + 1) l : ℂ) * ht
      rw [Finset.sum_congr rfl hterm_eval]
      have hfactor : (∑ l ∈ Finset.range (m + 2),
            (Nat.choose (m + 1) l : ℂ) * (x * ((-1 : ℂ) ^ (m + 1 - l) * (x + (l : ℂ)) ^ m)))
          = x * (∑ l ∈ Finset.range (m + 2),
            (Nat.choose (m + 1) l : ℂ) * ((-1 : ℂ) ^ (m + 1 - l) * (x + (l : ℂ)) ^ m)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      rw [hfactor]
      congr 1
      unfold S
      rw [hrange]
      apply Finset.sum_congr rfl
      intro l _
      ring
    have hGeval : ((Polynomial.X + Polynomial.C x) ^ (m + 1)).eval (-x) = 0 := by
      rw [Polynomial.eval_pow]
      have hbase : (Polynomial.X + Polynomial.C x).eval (-x) = 0 := by
        rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        exact neg_add_cancel x
      rw [hbase]
      exact zero_pow (Nat.succ_ne_zero m)
    have heval : (AbelPoly x (m + 1) - (Polynomial.X + Polynomial.C x) ^ (m + 1)).eval (-x)
        = 0 := by
      rw [Polynomial.eval_sub, hFeval, hGeval, fd_vanish (m + 1) m (Nat.lt_succ_self m) x,
        mul_zero, sub_zero]
    have hD0 : ∀ k : ℕ,
        (AbelPoly x (m + 1) - (Polynomial.X + Polynomial.C x) ^ (m + 1)).coeff (k + 1) = 0 := by
      intro k
      have h := Polynomial.coeff_derivative
        (AbelPoly x (m + 1) - (Polynomial.X + Polynomial.C x) ^ (m + 1)) k
      rw [hDderiv] at h
      simp only [Polynomial.coeff_zero] at h
      have hne : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      rcases mul_eq_zero.mp h.symm with h0 | h1
      · exact h0
      · exact absurd h1 hne
    have hDsum := Polynomial.as_sum_range_C_mul_X_pow
      (AbelPoly x (m + 1) - (Polynomial.X + Polynomial.C x) ^ (m + 1))
    have hDC : AbelPoly x (m + 1) - (Polynomial.X + Polynomial.C x) ^ (m + 1)
        = Polynomial.C ((AbelPoly x (m + 1) - (Polynomial.X + Polynomial.C x) ^ (m + 1)).coeff 0) := by
      conv_lhs => rw [hDsum]
      rw [Finset.sum_range_succ']
      simp [hD0]
    have hcoeff0 : (AbelPoly x (m + 1) - (Polynomial.X + Polynomial.C x) ^ (m + 1)).coeff 0
        = 0 := by
      have h := heval
      rw [hDC] at h
      rw [Polynomial.eval_C] at h
      exact h
    have hD : AbelPoly x (m + 1) - (Polynomial.X + Polynomial.C x) ^ (m + 1) = 0 := by
      rw [hDC, hcoeff0, Polynomial.C_0]
    exact sub_eq_zero.mp hD

/-- Bernoulli polynomial evaluation via its defining coefficients. -/
private theorem bernoulli_eval_eq (m : ℕ) (w : ℂ) :
    Polynomial.eval₂ (algebraMap ℚ ℂ) w (Polynomial.bernoulli m)
      = ∑ i ∈ Finset.range (m + 1),
        (((_root_.bernoulli i * Nat.choose m i : ℚ)) : ℂ) * w ^ (m - i) := by
  unfold Polynomial.bernoulli
  rw [Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.eval₂_monomial]
  congr 1

/-- Trinomial coefficient identity. -/
private theorem trinomial (n l i : ℕ) (h : l + i ≤ n) :
    (Nat.choose n l : ℂ) * (Nat.choose (n - l) i : ℂ)
      = (Nat.choose n i : ℂ) * (Nat.choose (n - i) l : ℂ) := by
  have hsub2 : (n - l) - i = n - l - i := by omega
  have hsub4 : (n - i) - l = n - l - i := by omega
  have e1nat := Nat.choose_mul_factorial_mul_factorial (n := n) (k := l) (by omega)
  have e2nat := Nat.choose_mul_factorial_mul_factorial (n := n - l) (k := i) (by omega)
  have e3nat := Nat.choose_mul_factorial_mul_factorial (n := n) (k := i) (by omega)
  have e4nat := Nat.choose_mul_factorial_mul_factorial (n := n - i) (k := l) (by omega)
  rw [hsub2] at e2nat
  rw [hsub4] at e4nat
  have e1 : (Nat.choose n l : ℂ) * ((l ! : ℕ) : ℂ) * ((((n - l)! : ℕ)) : ℂ)
      = (((n ! : ℕ)) : ℂ) := by exact_mod_cast e1nat
  have e2 : (Nat.choose (n - l) i : ℂ) * ((i ! : ℕ) : ℂ) * ((((n - l - i)! : ℕ)) : ℂ)
      = ((((n - l)! : ℕ)) : ℂ) := by exact_mod_cast e2nat
  have e3 : (Nat.choose n i : ℂ) * ((i ! : ℕ) : ℂ) * ((((n - i)! : ℕ)) : ℂ)
      = (((n ! : ℕ)) : ℂ) := by exact_mod_cast e3nat
  have e4 : (Nat.choose (n - i) l : ℂ) * ((l ! : ℕ) : ℂ) * ((((n - l - i)! : ℕ)) : ℂ)
      = ((((n - i)! : ℕ)) : ℂ) := by exact_mod_cast e4nat
  have hD : ((l ! : ℕ) : ℂ) * ((i ! : ℕ) : ℂ) * ((((n - l - i)! : ℕ)) : ℂ) ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    · exact_mod_cast Nat.factorial_ne_zero l
    · exact_mod_cast Nat.factorial_ne_zero i
    · exact_mod_cast Nat.factorial_ne_zero (n - l - i)
  have key : (((l ! : ℕ) : ℂ) * ((i ! : ℕ) : ℂ) * ((((n - l - i)! : ℕ)) : ℂ))
        * ((Nat.choose n l : ℂ) * (Nat.choose (n - l) i : ℂ)) = (((n ! : ℕ)) : ℂ) := by
    calc (((l ! : ℕ) : ℂ) * ((i ! : ℕ) : ℂ) * ((((n - l - i)! : ℕ)) : ℂ))
            * ((Nat.choose n l : ℂ) * (Nat.choose (n - l) i : ℂ))
        = ((Nat.choose n l : ℂ) * ((l ! : ℕ) : ℂ)) *
          ((Nat.choose (n - l) i : ℂ) * ((i ! : ℕ) : ℂ) * ((((n - l - i)! : ℕ)) : ℂ)) := by
          ring
      _ = ((Nat.choose n l : ℂ) * ((l ! : ℕ) : ℂ)) * ((((n - l)! : ℕ)) : ℂ) := by
          rw [e2]
      _ = (Nat.choose n l : ℂ) * ((l ! : ℕ) : ℂ) * ((((n - l)! : ℕ)) : ℂ) := by
          ring
      _ = (((n ! : ℕ)) : ℂ) := e1
  have key2 : (((l ! : ℕ) : ℂ) * ((i ! : ℕ) : ℂ) * ((((n - l - i)! : ℕ)) : ℂ))
        * ((Nat.choose n i : ℂ) * (Nat.choose (n - i) l : ℂ)) = (((n ! : ℕ)) : ℂ) := by
    calc (((l ! : ℕ) : ℂ) * ((i ! : ℕ) : ℂ) * ((((n - l - i)! : ℕ)) : ℂ))
            * ((Nat.choose n i : ℂ) * (Nat.choose (n - i) l : ℂ))
        = ((Nat.choose n i : ℂ) * ((i ! : ℕ) : ℂ)) *
          ((Nat.choose (n - i) l : ℂ) * ((l ! : ℕ) : ℂ) * ((((n - l - i)! : ℕ)) : ℂ)) := by
          ring
      _ = ((Nat.choose n i : ℂ) * ((i ! : ℕ) : ℂ)) * ((((n - i)! : ℕ)) : ℂ) := by
          rw [e4]
      _ = (Nat.choose n i : ℂ) * ((i ! : ℕ) : ℂ) * ((((n - i)! : ℕ)) : ℂ) := by
          ring
      _ = (((n ! : ℕ)) : ℂ) := e3
  have hDD : (((l ! : ℕ) : ℂ) * ((i ! : ℕ) : ℂ) * ((((n - l - i)! : ℕ)) : ℂ))
        * ((Nat.choose n l : ℂ) * (Nat.choose (n - l) i : ℂ))
      = (((l ! : ℕ) : ℂ) * ((i ! : ℕ) : ℂ) * ((((n - l - i)! : ℕ)) : ℂ))
        * ((Nat.choose n i : ℂ) * (Nat.choose (n - i) l : ℂ)) := by
    rw [key, key2]
  exact mul_left_cancel₀ hD hDD

/--
**Abel–Bernoulli sum.** Let $B_k(t)$ denote the $k$-th Bernoulli polynomial. For every natural
number $n$ and all complex numbers $x$ and $y$ with $x \neq 0$,
$$\sum_{l=0}^{n} \binom{n}{l} (x + l)^{l-1} B_{n-l}(y + n - l) = \frac{1}{x} B_n(y + x + n),$$
where $(x + l)^{l-1}$ is an integer power, so the term $l = 0$ contains the factor $x^{-1}$.

This is the first of the source's two Abel–Bernoulli sums.

Source: Claudio de J. Pita Ruiz V., "Carlitz-Type and Other Bernoulli
Identities," Journal of Integer Sequences 19 (2016), Article 16.1.8,
Proposition [Abel-Bernoulli sums], equation (5.11), lines 790–794,
https://cs.uwaterloo.ca/journals/JIS/VOL19/Pita/pita23.tex
Proves `Wanted` entry `abel_bernoulli_sum`.
-/
theorem abel_bernoulli_sum :
    ∀ (n : ℕ) (x y : ℂ), x ≠ 0 →
      ∑ l ∈ Finset.range (n + 1),
        (Nat.choose n l : ℂ) * (x + (l : ℂ)) ^ ((l : ℤ) - 1) *
          Polynomial.eval₂ (algebraMap ℚ ℂ) (y + (n - l : ℕ))
            (Polynomial.bernoulli (n - l)) =
        (1 / x) * Polynomial.eval₂ (algebraMap ℚ ℂ) (y + x + (n : ℂ))
          (Polynomial.bernoulli n) := by
  intro n x y hx
  set w0 : ℂ := y + (n : ℂ) with hw0
  have hpt : ∀ l : ℕ, l ≤ n → (y + ((n - l : ℕ) : ℂ)) = w0 - (l : ℂ) := by
    intro l hln
    have hc : ((n - l : ℕ) : ℂ) = (n : ℂ) - (l : ℂ) := Nat.cast_sub hln
    rw [hc, hw0]
    ring
  have hptR : y + x + (n : ℂ) = w0 + x := by
    rw [hw0]
    ring
  have hB : x * ((1 / x) * Polynomial.eval₂ (algebraMap ℚ ℂ) (y + x + (n : ℂ))
      (Polynomial.bernoulli n))
      = Polynomial.eval₂ (algebraMap ℚ ℂ) (w0 + x) (Polynomial.bernoulli n) := by
    rw [← mul_assoc, mul_one_div_cancel hx, one_mul, hptR]
  have habel : ∀ i : ℕ, i ≤ n →
      (x + w0) ^ (n - i)
        = ∑ l ∈ Finset.range (n - i + 1),
          (Nat.choose (n - i) l : ℂ) * abelCoeff x l * (w0 - (l : ℂ)) ^ (n - i - l) := by
    intro i hin
    have h := congrArg (fun p : Polynomial ℂ => Polynomial.eval w0 p) (abel_poly x hx (n - i))
    unfold AbelPoly at h
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_add] at h
    rw [add_comm x w0]
    exact h.symm
  have hterm : ∀ l ∈ Finset.range (n + 1),
      x * ((Nat.choose n l : ℂ) * (x + (l : ℂ)) ^ ((l : ℤ) - 1) *
        Polynomial.eval₂ (algebraMap ℚ ℂ) (y + ((n - l : ℕ) : ℂ))
          (Polynomial.bernoulli (n - l)))
      = (Nat.choose n l : ℂ) * abelCoeff x l *
        Polynomial.eval₂ (algebraMap ℚ ℂ) (w0 - (l : ℂ)) (Polynomial.bernoulli (n - l)) := by
    intro l hl
    have hln : l ≤ n := by have := Finset.mem_range.mp hl; omega
    rw [hpt l hln]
    unfold abelCoeff
    ring
  have hexpand : ∀ l ∈ Finset.range (n + 1),
      (Nat.choose n l : ℂ) * abelCoeff x l *
        Polynomial.eval₂ (algebraMap ℚ ℂ) (w0 - (l : ℂ)) (Polynomial.bernoulli (n - l))
      = ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n l : ℂ) * abelCoeff x l *
          (((_root_.bernoulli i * Nat.choose (n - l) i : ℚ)) : ℂ) * (w0 - (l : ℂ)) ^ (n - l - i) := by
    intro l hl
    have hln : l ≤ n := by have := Finset.mem_range.mp hl; omega
    have hext : (∑ i ∈ Finset.range (n - l + 1),
          (((_root_.bernoulli i * Nat.choose (n - l) i : ℚ)) : ℂ) * (w0 - (l : ℂ)) ^ (n - l - i))
        = ∑ i ∈ Finset.range (n + 1),
          (((_root_.bernoulli i * Nat.choose (n - l) i : ℚ)) : ℂ) * (w0 - (l : ℂ)) ^ (n - l - i) := by
      apply Finset.sum_subset
      · intro i hi
        have h2 := Finset.mem_range.mp hi
        exact Finset.mem_range.mpr (by omega)
      · intro i hi hni
        have h1 : n - l < i := by
          have h2 : ¬ i < n - l + 1 := fun h => hni (Finset.mem_range.mpr h)
          omega
        have hC : Nat.choose (n - l) i = 0 := Nat.choose_eq_zero_of_lt h1
        simp [hC]
    rw [bernoulli_eval_eq, hext, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hboth : ∀ l ∈ Finset.range (n + 1),
      x * ((Nat.choose n l : ℂ) * (x + (l : ℂ)) ^ ((l : ℤ) - 1) *
        Polynomial.eval₂ (algebraMap ℚ ℂ) (y + ((n - l : ℕ) : ℂ))
          (Polynomial.bernoulli (n - l)))
      = ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n l : ℂ) * abelCoeff x l *
          (((_root_.bernoulli i * Nat.choose (n - l) i : ℚ)) : ℂ) * (w0 - (l : ℂ)) ^ (n - l - i) := by
    intro l hl
    rw [hterm l hl]
    exact hexpand l hl
  have hper : ∀ i ∈ Finset.range (n + 1),
      (((_root_.bernoulli i * Nat.choose n i : ℚ)) : ℂ) * (w0 + x) ^ (n - i)
      = ∑ l ∈ Finset.range (n + 1),
        (((_root_.bernoulli i * Nat.choose n i : ℚ)) : ℂ) *
          ((Nat.choose (n - i) l : ℂ) * abelCoeff x l * (w0 - (l : ℂ)) ^ (n - i - l)) := by
    intro i hi
    have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
    have hextR : (∑ l ∈ Finset.range (n - i + 1),
          (((_root_.bernoulli i * Nat.choose n i : ℚ)) : ℂ) *
            ((Nat.choose (n - i) l : ℂ) * abelCoeff x l * (w0 - (l : ℂ)) ^ (n - i - l)))
        = ∑ l ∈ Finset.range (n + 1),
          (((_root_.bernoulli i * Nat.choose n i : ℚ)) : ℂ) *
            ((Nat.choose (n - i) l : ℂ) * abelCoeff x l * (w0 - (l : ℂ)) ^ (n - i - l)) := by
      apply Finset.sum_subset
      · intro l hl
        have h2 := Finset.mem_range.mp hl
        exact Finset.mem_range.mpr (by omega)
      · intro l hl hnl
        have h1 : n - i < l := by
          have h2 : ¬ l < n - i + 1 := fun h => hnl (Finset.mem_range.mpr h)
          omega
        have hC : Nat.choose (n - i) l = 0 := Nat.choose_eq_zero_of_lt h1
        simp [hC]
    have hxc : (w0 + x) ^ (n - i) = (x + w0) ^ (n - i) := by rw [add_comm]
    rw [hxc, habel i hin, Finset.mul_sum, hextR]
  have hRHS : Polynomial.eval₂ (algebraMap ℚ ℂ) (w0 + x) (Polynomial.bernoulli n)
      = ∑ l ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
        (((_root_.bernoulli i * Nat.choose n i : ℚ)) : ℂ) *
          ((Nat.choose (n - i) l : ℂ) * abelCoeff x l * (w0 - (l : ℂ)) ^ (n - i - l)) := by
    rw [bernoulli_eval_eq]
    exact Eq.trans (Finset.sum_congr rfl hper) Finset.sum_comm
  apply mul_left_cancel₀ hx
  rw [hB, Finset.mul_sum, Finset.sum_congr rfl hboth, hRHS]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro i hi
  have hln : l ≤ n := by have := Finset.mem_range.mp hl; omega
  have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
  by_cases h : l + i ≤ n
  · have hTR := trinomial n l i h
    have hexp : n - l - i = n - i - l := by omega
    rw [hexp]
    push_cast
    linear_combination (abelCoeff x l * ((_root_.bernoulli i : ℂ)) * (w0 - (l : ℂ)) ^ (n - i - l)) * hTR
  · have h1 : n - l < i := by omega
    have h2 : n - i < l := by omega
    have hC1 : Nat.choose (n - l) i = 0 := Nat.choose_eq_zero_of_lt h1
    have hC2 : Nat.choose (n - i) l = 0 := Nat.choose_eq_zero_of_lt h2
    simp [hC1, hC2]

end MetaMathlibExt
