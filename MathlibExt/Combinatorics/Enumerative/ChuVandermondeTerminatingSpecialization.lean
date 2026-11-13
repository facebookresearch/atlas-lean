/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.LinearCombination

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

private theorem chu_aux_prod (k : ℕ) : ∀ m : ℕ,
    (∏ i ∈ Finset.Icc 2 (m + 1), (k + i)) = Nat.ascFactorial (k + 2) m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ m + 1 + 1), ih, Nat.ascFactorial_succ]
    ring

private theorem chu_aux_point (n k : ℕ) (hn : 1 ≤ n) :
    ((n + k).choose k : ℚ) / ((k : ℚ) + 1)
      = (∏ i ∈ Finset.Icc 2 n, ((k : ℚ) + (i : ℚ))) / (n.factorial : ℚ) := by
  have hle : k ≤ n + k := Nat.le_add_left k n
  have hA := Nat.choose_mul_factorial_mul_factorial hle
  rw [Nat.add_sub_cancel] at hA
  have hB := Nat.factorial_mul_ascFactorial (k + 1) (n - 1)
  rw [show k + 1 + 1 = k + 2 from rfl] at hB
  rw [show k + 1 + (n - 1) = n + k from by omega] at hB
  have hn' : n = (n - 1) + 1 := by omega
  have hkey : (∏ i ∈ Finset.Icc 2 n, (k + i)) = Nat.ascFactorial (k + 2) (n - 1) := by
    conv_lhs => rw [hn']
    exact chu_aux_prod k (n - 1)
  have hA' : ((n + k).choose k : ℚ) * (k.factorial : ℚ) * (n.factorial : ℚ)
      = ((n + k).factorial : ℚ) := by exact_mod_cast hA
  have hB' : ((k + 1).factorial : ℚ) * ((∏ i ∈ Finset.Icc 2 n, (k + i) : ℕ) : ℚ)
      = ((n + k).factorial : ℚ) := by
    have hBn : ((k + 1).factorial * Nat.ascFactorial (k + 2) (n - 1) : ℕ)
        = ((n + k).factorial : ℕ) := hB
    rw [← hkey] at hBn
    exact_mod_cast hBn
  have hC' : ((k + 1).factorial : ℚ) = ((k : ℚ) + 1) * (k.factorial : ℚ) := by
    have hC := Nat.factorial_succ k
    exact_mod_cast hC
  have hkF : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hcancel : ((n + k).choose k : ℚ) * (n.factorial : ℚ)
      = ((∏ i ∈ Finset.Icc 2 n, (k + i) : ℕ) : ℚ) * ((k : ℚ) + 1) := by
    have hAB : ((n + k).choose k : ℚ) * (k.factorial : ℚ) * (n.factorial : ℚ)
        = ((∏ i ∈ Finset.Icc 2 n, (k + i) : ℕ) : ℚ) * ((k : ℚ) + 1) * (k.factorial : ℚ) := by
      rw [hA', ← hB', hC']
      ring
    have hAB' : (((n + k).choose k : ℚ) * (n.factorial : ℚ)) * (k.factorial : ℚ)
        = ((((∏ i ∈ Finset.Icc 2 n, (k + i) : ℕ) : ℚ)) * ((k : ℚ) + 1)) * (k.factorial : ℚ) := by
      linear_combination hAB
    exact mul_right_cancel₀ hkF hAB'
  have hEval : (∏ i ∈ Finset.Icc 2 n, ((k : ℚ) + (i : ℚ)))
      = ((∏ i ∈ Finset.Icc 2 n, (k + i) : ℕ) : ℚ) := by
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl (fun i _ => (Nat.cast_add k i).symm)
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hnF : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [hEval, div_eq_div_iff hk1 hnF]
  exact hcancel

private theorem chu_aux_vanish (n : ℕ) (P : Polynomial ℚ) (hP : P.natDegree < n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * P.eval (k : ℚ) = 0 := by
  have h1 := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP
  have h2 := fwdDiff_iter_eq_sum_shift (1 : ℚ) (fun x => P.eval x) n (0 : ℚ)
  rw [h1] at h2
  simp only [Pi.zero_apply, zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul,
    Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_neg, Int.cast_one] at h2
  have hsq2 : ∀ k : ℕ, (-1 : ℚ) ^ k * (-1 : ℚ) ^ k = 1 := by
    intro k
    have h2e : (-1 : ℚ) ^ (k + k) = 1 := Even.neg_one_pow ⟨k, rfl⟩
    rwa [pow_add] at h2e
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * P.eval (k : ℚ)
        = (-1 : ℚ) ^ n * ((-1 : ℚ) ^ k * (n.choose k : ℚ) * P.eval (k : ℚ)) := by
    intro k hk
    have hk' : k < n + 1 := Finset.mem_range.mp hk
    have hkn : k ≤ n := by omega
    have hpow : (-1 : ℚ) ^ n = (-1 : ℚ) ^ (n - k) * (-1 : ℚ) ^ k := by
      conv_lhs => rw [← Nat.sub_add_cancel hkn, pow_add]
    rw [hpow]
    linear_combination
      -(↑(n.choose k) * P.eval (↑k) * (-1 : ℚ) ^ (n - k)) * (hsq2 k)
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at h2
  have hne : (-1 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_eq_zero.mp h2.symm).resolve_left hne

private theorem chu_aux_deg (n : ℕ) (hn : 1 ≤ n) :
    (∏ i ∈ Finset.Icc 2 n, (Polynomial.X + Polynomial.C (i : ℚ))).natDegree < n := by
  calc (∏ i ∈ Finset.Icc 2 n, (Polynomial.X + Polynomial.C (i : ℚ))).natDegree
      ≤ ∑ i ∈ Finset.Icc 2 n, (Polynomial.X + Polynomial.C (i : ℚ)).natDegree :=
        Polynomial.natDegree_prod_le _ _
    _ = ∑ _i ∈ Finset.Icc 2 n, 1 :=
        Finset.sum_congr rfl (fun i _ => Polynomial.natDegree_X_add_C _)
    _ = (Finset.Icc 2 n).card := by simp
    _ = n + 1 - 2 := Nat.card_Icc 2 n
    _ < n := by omega

/-- **Terminating Chu–Vandermonde specialization.** For every natural number $n \ge 1$, the
following sum of rational numbers vanishes:
$$\sum_{k=0}^{n} \binom{n}{k} \binom{n+k}{k} \frac{(-1)^k}{k+1} = 0.$$

The source identifies the sum as the terminating Gauss hypergeometric value
${}_2F_1(n+1, -n; 2; 1) = (1-n)_n / (2)_n = 0$, where $(a)_n$ is the rising factorial.

Source: Carsten Elsner, "On Prime-Detecting Sequences From Apéry's Recurrence
Formulae for ζ(3) and ζ(2)", Journal of Integer Sequences 11 (2008),
Article 08.5.1, lines 606–608,
<https://cs.uwaterloo.ca/journals/JIS/VOL11/Elsner/elsner7.tex>.
Proves `Wanted` entry `chu_vandermonde_terminating_specialization`.
-/
theorem chu_vandermonde_terminating_specialization
    (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℚ) * ((n + k).choose k : ℚ) * (-1 : ℚ) ^ k / (k + 1) = 0 := by
  set P : Polynomial ℚ := ∏ i ∈ Finset.Icc 2 n, (Polynomial.X + Polynomial.C (i : ℚ))
    with hPdef
  have hPdeg : P.natDegree < n := chu_aux_deg n hn
  have hvan : ∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (n.choose k : ℚ) * P.eval (k : ℚ) = 0 :=
    chu_aux_vanish n P hPdeg
  have hEval : ∀ k : ℕ, P.eval (k : ℚ)
      = ∏ i ∈ Finset.Icc 2 n, ((k : ℚ) + (i : ℚ)) := by
    intro k
    rw [hPdef, Polynomial.eval_prod]
    exact Finset.prod_congr rfl (fun i _ => by
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C])
  have hd : ∀ k : ℕ, ((k : ℚ) + 1) ≠ 0 := fun k => by positivity
  have hN : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hpoint : ∀ k ∈ Finset.range (n + 1),
      (n.choose k : ℚ) * ((n + k).choose k : ℚ) * (-1 : ℚ) ^ k / (k + 1)
        = ((-1 : ℚ) ^ k * (n.choose k : ℚ) * P.eval (k : ℚ)) / (n.factorial : ℚ) := by
    intro k _
    rw [hEval k]
    have hC2 := chu_aux_point n k hn
    rw [div_eq_div_iff (hd k) hN] at hC2
    rw [div_eq_div_iff (hd k) hN]
    linear_combination ((n.choose k : ℚ) * (-1 : ℚ) ^ k) * hC2
  rw [Finset.sum_congr rfl hpoint, ← Finset.sum_div, hvan, zero_div]

end

end MetaMathlibExt
