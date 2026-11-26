/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModifiedDegenerateBernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
import MathlibExt.NumberTheory.ModifiedDegenerateBernoulliThreeTerm

/-!
# Miki-type identity for modified degenerate Bernoulli numbers

Specializing the three-term identity at weights $-1,a,b$ with $a+b=n+1$ and summing over $a$
gives the Miki-type identity of Su and Pan.
-/

open Finset

namespace MetaMathlibExt
namespace modifiedDegenerateBernoulli_miki

local notation "B" => modifiedDegenerateBernoulli

private theorem choose_neg_one (k : ℕ) : Ring.choose (-1 : ℂ) k = (-1) ^ k := by
  simp [Ring.choose_neg', Ring.multichoose_one, Units.smul_def, zsmul_eq_mul]

private theorem signed_at_one (lam : ℂ) (k : ℕ) :
    (-1) ^ k * B lam k 1 = B lam k 0 := by
  have h := congrArg (algebraMap ℚ ℂ) (Polynomial.bernoulli_eval_one_sub k 1)
  simp only [sub_self, map_mul, map_pow, map_neg, map_one] at h
  have ev (x : ℚ) : Polynomial.aeval (algebraMap ℚ ℂ x) (Polynomial.bernoulli k) =
      algebraMap ℚ ℂ ((Polynomial.bernoulli k).eval x) :=
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval x _
  simp only [modifiedDegenerateBernoulli, ← map_one (algebraMap ℚ ℂ),
    ← map_zero (algebraMap ℚ ℂ), ev]
  rw [h, map_one]
  ring

private theorem signed_at_zero (lam : ℂ) (k : ℕ) :
    (-1) ^ k * B lam k 0 = B lam k 0 + if k = 1 then 1 else 0 := by
  by_cases hk : k = 1
  · norm_num [hk, modifiedDegenerateBernoulli_one]
  rcases k.even_or_odd with he | ho
  · simp [he.neg_one_pow, hk]
  · simp [modifiedDegenerateBernoulli, Polynomial.aeval_def, Polynomial.eval₂_at_zero,
      Polynomial.coeff_bernoulli, bernoulli_eq_zero_of_odd ho (by have := ho.pos; omega), hk]

-- With positive weights a + 1 and b + 1, only k = a and k = a + 1 survive.
private theorem two_terms (a b : ℕ) (f : ℕ → ℂ) :
    ∑ k ∈ range (a + b + 2), ((a + 1).choose k : ℂ) *
        ((b + 1).choose (a + b + 1 - k) : ℂ) * f k =
      (a + 1 : ℂ) * f a + (b + 1 : ℂ) * f (a + 1) := by
  let s := range (a + b + 2)
  have ha : a ∈ s := mem_range.mpr (by omega)
  have ha' : a + 1 ∈ s.erase a := mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩
  change ∑ k ∈ s, _ = _
  rw [← add_sum_erase _ _ ha, ← add_sum_erase _ _ ha', sum_eq_zero]
  · simp [show a + b + 1 - a = b + 1 by omega, Nat.choose_succ_self_right]
  · intro k hk
    obtain ⟨hne', hk'⟩ := mem_erase.mp hk
    have hne := ne_of_mem_erase hk'
    rcases lt_or_ge k a with h | h
    · simp [Nat.choose_eq_zero_of_lt (show b + 1 < a + b + 1 - k by omega)]
    · simp [Nat.choose_eq_zero_of_lt (show a + 1 < k by omega)]

private theorem pair_identity (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = n + 1)
    (lam : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    let f := fun k => B lam k 0 * B lam (n - k) 0
    let T := fun m : ℕ => ∑ k ∈ range (n + 1), (m.choose k : ℂ) * f k
    f a / a + f b / b = T a / a + T b / b + B lam (n - 1) 0 := by
  intro f T
  have flip (k : ℕ) (hk : k ≤ n) : f (n - k) = f k := by
    simp only [f, Nat.sub_sub_self hk, mul_comm]
  have h := modifiedDegenerateBernoulli_three_term n (by omega) lam hlam hlam1
    (-1) a b 0 1 0 (by exact_mod_cast (show (-1 : ℤ) + a + b = n by omega)) (by norm_num)
  dsimp only at h
  simp only [Ring.choose_natCast, choose_neg_one] at h
  have firstSum :
      ∑ k ∈ range (n + 1), (-1 : ℂ) ^ k * a.choose k * b.choose (n - k) *
          B lam (n - k) 0 * B lam k 1 = (a : ℂ) * f b + (b : ℂ) * f a := by
    trans ∑ k ∈ range (n + 1), (a.choose k : ℂ) * b.choose (n - k) * f k
    · apply sum_congr rfl
      intro k _
      dsimp only [f]
      rw [← signed_at_one lam k]
      ring
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
    obtain rfl : n = i + j + 1 := by omega
    have hflip : f i = f (j + 1) := by
      simpa only [show i + j + 1 - (j + 1) = i by omega] using flip (j + 1) (by omega)
    rw [two_terms, hflip, Nat.cast_succ, Nat.cast_succ]
  have secondSum :
      ∑ k ∈ range (n + 1), (-1 : ℂ) ^ k * b.choose k * (-1) ^ (n - k) *
          B lam (n - k) 1 * B lam k 0 = T b + b * B lam (n - 1) 0 := by
    dsimp only [T]
    rw [show (b : ℂ) * B lam (n - 1) 0 =
      ∑ k ∈ range (n + 1), if k = 1 then (b : ℂ) * B lam (n - 1) 0 else 0 by
        simp [show 1 < n + 1 by omega], ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    calc
      _ = (b.choose k : ℂ) * (((-1) ^ k * B lam k 0) *
          ((-1) ^ (n - k) * B lam (n - k) 1)) := by ring
      _ = _ := by
        rw [signed_at_zero, signed_at_one]
        by_cases hk : k = 1 <;> simp [hk, f]
        ring
  have thirdSum :
      ∑ k ∈ range (n + 1), (-1 : ℂ) ^ k * (-1) ^ k * a.choose (n - k) *
          B lam (n - k) 0 * B lam k 0 = T a := by
    dsimp only [T]
    rw [← sum_flip (fun k => (a.choose k : ℂ) * f k)]
    apply sum_congr rfl
    intro k hk
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul, flip k (mem_range_succ_iff.mp hk)]
    dsimp only [f]
    ring
  rw [firstSum, secondSum, thirdSum] at h
  field_simp [Nat.cast_ne_zero.mpr ha.ne', Nat.cast_ne_zero.mpr hb.ne']
  linear_combination -h

-- Summing a column of the binomial transform with weight 1/a gives a hockey-stick sum.
private theorem weighted_choose (n j : ℕ) :
    ∑ a ∈ Icc 1 n, (a.choose (j + 1) : ℂ) / a = (n.choose (j + 1) : ℂ) / (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    have h : (n + 1 : ℂ) * n.choose j = (n + 1).choose (j + 1) * (j + 1 : ℂ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n j
    nth_rw 2 [Nat.choose_succ_succ']
    push_cast
    field_simp
    linear_combination -h

private theorem sum_transform (n : ℕ) (f : ℕ → ℂ) :
    ∑ a ∈ Icc 1 n, (∑ k ∈ range (n + 1), (a.choose k : ℂ) * f k) / a =
      (harmonic n : ℂ) * f 0 + ∑ k ∈ Icc 1 n, (n.choose k : ℂ) * f k / k := by
  have hH : ∑ a ∈ Icc 1 n, (a : ℂ)⁻¹ = (harmonic n : ℂ) := by
    induction n with
    | zero => simp
    | succ n ih => simp [sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
  simp_rw [sum_div]
  rw [sum_comm, sum_range_eq_add_Ico _ (by omega), Ico_add_one_right_eq_Icc]
  congr 1
  · simp [div_eq_inv_mul, ← sum_mul, hH]
  · apply sum_congr rfl
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (show k ≠ 0 from Nat.ne_of_gt (mem_Icc.mp hk).1)
    simpa only [sum_mul, div_mul_eq_mul_div, Nat.cast_succ] using
      congrArg (· * f (j + 1)) (weighted_choose n j)

end modifiedDegenerateBernoulli_miki

/-- **Miki-type identity for modified degenerate Bernoulli numbers.** Let $n \ge 4$, let $\lambda$
be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$, write
$\mathfrak{B}_{k,\lambda} = \mathfrak{B}_{k,\lambda}(0)$ for the value at $0$ of the modified
degenerate Bernoulli polynomial $\mathfrak{B}_{k,\lambda}(x)$, and let $H_n = \sum_{k=1}^{n} 1/k$
be the $n$-th harmonic number. Then

$$
\sum_{k=1}^{n-1} \frac{\mathfrak{B}_{k,\lambda} \mathfrak{B}_{n-k,\lambda}}{k} -
\sum_{k=1}^{n-1} \binom{n}{k} \frac{\mathfrak{B}_{k,\lambda} \mathfrak{B}_{n-k,\lambda}}{k} =
\frac{\lambda}{\log(1+\lambda)}\, H_n\, \mathfrak{B}_{n,\lambda} +
\frac{n}{2}\, \mathfrak{B}_{n-1,\lambda},
$$

where $\log$ is the principal branch.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Corollary 2, equation
(mikiD) (`jis-2024-24.5.4-cor-2`). -/
public theorem modifiedDegenerateBernoulli_miki (n : ℕ) (hn : 4 ≤ n) (lam : ℂ)
    (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ∑ k ∈ Icc 1 (n - 1), modifiedDegenerateBernoulli lam k 0 / k *
        modifiedDegenerateBernoulli lam (n - k) 0 -
      ∑ k ∈ Icc 1 (n - 1), (n.choose k : ℂ) * modifiedDegenerateBernoulli lam k 0 / k *
        modifiedDegenerateBernoulli lam (n - k) 0 =
      lam / Complex.log (1 + lam) * (harmonic n : ℂ) * modifiedDegenerateBernoulli lam n 0 +
        n / 2 * modifiedDegenerateBernoulli lam (n - 1) 0 := by
  let B := fun k => modifiedDegenerateBernoulli lam k 0
  let f := fun k => B k * B (n - k)
  let T := fun a : ℕ => ∑ k ∈ range (n + 1), (a.choose k : ℂ) * f k
  have h := sum_congr (s₁ := Icc 1 n) rfl fun a ha => by
    obtain ⟨ha₁, ha₂⟩ := mem_Icc.mp ha
    exact modifiedDegenerateBernoulli_miki.pair_identity n a (n + 1 - a)
      ha₁ (by omega) (by omega) lam hlam hlam1
  change ∑ a ∈ Icc 1 n, (f a / a + f (n + 1 - a) / (n + 1 - a : ℕ)) =
    ∑ a ∈ Icc 1 n, (T a / a + T (n + 1 - a) / (n + 1 - a : ℕ) + B (n - 1)) at h
  have reflect (g : ℕ → ℂ) :
      ∑ a ∈ Icc 1 n, g (n + 1 - a) = ∑ a ∈ Icc 1 n, g a := by
    simpa only [Ico_add_one_right_eq_Icc, Nat.add_sub_cancel,
      Nat.add_sub_cancel_left] using sum_Ico_reflect g 1 (n := n + 1) (m := n + 1) (by omega)
  simp only [sum_add_distrib, reflect (fun a => f a / a), reflect (fun a => T a / a),
    sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel] at h
  rw [show (∑ a ∈ Icc 1 n, T a / a) = _ from
    modifiedDegenerateBernoulli_miki.sum_transform n f] at h
  have split (g : ℕ → ℂ) : ∑ k ∈ Icc 1 n, g k = (∑ k ∈ Icc 1 (n - 1), g k) + g n := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using
      sum_Icc_succ_top (a := 1) (b := n - 1) (by omega) g
  simp only [split (fun k => f k / k), split (fun k => (n.choose k : ℂ) * f k / k),
    Nat.choose_self, Nat.cast_one, one_mul] at h
  have hzero : B 0 = lam / Complex.log (1 + lam) := by
    simp [B, modifiedDegenerateBernoulli]
  dsimp only [f, Nat.sub_zero] at h
  rw [hzero] at h
  change (∑ k ∈ Icc 1 (n - 1), B k / k * B (n - k)) -
    (∑ k ∈ Icc 1 (n - 1), (n.choose k : ℂ) * B k / k * B (n - k)) = _
  simp_rw [div_mul_eq_mul_div, mul_assoc]
  dsimp only [B] at h ⊢
  linear_combination h / 2

end MetaMathlibExt
