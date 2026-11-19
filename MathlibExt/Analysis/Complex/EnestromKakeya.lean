/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

/-!
# Eneström–Kakeya zero localization for polynomials with positive coefficients
-/

namespace MathlibExt.Analysis.Complex.EnestromKakeya

private theorem upper_of_mono {n : ℕ} (hn : 1 ≤ n) (c : ℕ → ℝ)
    (hpos : ∀ k, k ≤ n → 0 < c k)
    (hmono : ∀ k, k < n → c k ≤ c (k + 1))
    (z : ℂ)
    (hsum : ∑ k ∈ Finset.range (n + 1), ((c k : ℝ) : ℂ) * z ^ k = 0) :
    ‖z‖ ≤ 1 := by
  by_contra hnge
  have hlt : (1 : ℝ) < ‖z‖ := lt_of_not_ge hnge
  have hz1 : (1 : ℝ) ≤ ‖z‖ := le_of_lt hlt
  have hpos0 : 0 < c 0 := hpos 0 (by omega)
  have hposn : 0 < c n := hpos n le_rfl
  have htele_aux : ∀ m : ℕ, ∑ k ∈ Finset.range m, (c (k + 1) - c k) = c m - c 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  have htele : ∑ k ∈ Finset.range n, (c (k + 1) - c k) = c n - c 0 := htele_aux n
  have key : ((c n : ℝ) : ℂ) * z ^ (n + 1)
      = ((c 0 : ℝ) : ℂ) + ∑ k ∈ Finset.range n, (((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1) := by
    have hS0 : z * (∑ k ∈ Finset.range (n + 1), ((c k : ℝ) : ℂ) * z ^ k)
        - (∑ k ∈ Finset.range (n + 1), ((c k : ℝ) : ℂ) * z ^ k) = 0 := by
      rw [hsum]
      simp
    rw [Finset.mul_sum] at hS0
    have hexpand : (∑ k ∈ Finset.range (n + 1), z * (((c k : ℝ) : ℂ) * z ^ k))
        = ∑ k ∈ Finset.range (n + 1), ((c k : ℝ) : ℂ) * z ^ (k + 1) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hexpand] at hS0
    have hsplit1 : ∑ k ∈ Finset.range (n + 1), ((c k : ℝ) : ℂ) * z ^ (k + 1)
        = (∑ k ∈ Finset.range n, ((c k : ℝ) : ℂ) * z ^ (k + 1))
          + ((c n : ℝ) : ℂ) * z ^ (n + 1) := by
      exact Finset.sum_range_succ _ _
    have hsplit2 : ∑ k ∈ Finset.range (n + 1), ((c k : ℝ) : ℂ) * z ^ k
        = (∑ k ∈ Finset.range n, ((c (k + 1) : ℝ) : ℂ) * z ^ (k + 1))
          + ((c 0 : ℝ) : ℂ) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, mul_one]
    rw [hsplit1, hsplit2] at hS0
    have hsum_eq : ∑ k ∈ Finset.range n, (((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1)
        = (∑ k ∈ Finset.range n, ((c (k + 1) : ℝ) : ℂ) * z ^ (k + 1))
          - (∑ k ∈ Finset.range n, ((c k : ℝ) : ℂ) * z ^ (k + 1)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [Complex.ofReal_sub]
      ring
    linear_combination hS0 - hsum_eq
  have hnorm_key : ‖((c n : ℝ) : ℂ) * z ^ (n + 1)‖
      ≤ ‖((c 0 : ℝ) : ℂ)‖
        + ∑ k ∈ Finset.range n, ‖(((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1)‖ := by
    rw [key]
    calc ‖((c 0 : ℝ) : ℂ) + ∑ k ∈ Finset.range n, (((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1)‖
        ≤ ‖((c 0 : ℝ) : ℂ)‖ + ‖∑ k ∈ Finset.range n, (((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1)‖ :=
          norm_add_le _ _
      _ ≤ ‖((c 0 : ℝ) : ℂ)‖
          + ∑ k ∈ Finset.range n, ‖(((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1)‖ := by
          gcongr
          exact norm_sum_le _ _
  have e1 : ‖((c n : ℝ) : ℂ)‖ = c n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hposn]
  have e0 : ‖((c 0 : ℝ) : ℂ)‖ = c 0 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos0]
  have eDiff : ∀ k ∈ Finset.range n, ‖(((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1)‖
      = (c (k + 1) - c k) * ‖z‖ ^ (k + 1) := by
    intro k hk
    rw [norm_mul, norm_pow]
    have hle : c k ≤ c (k + 1) := hmono k (Finset.mem_range.mp hk)
    have hnn : (0 : ℝ) ≤ c (k + 1) - c k := sub_nonneg.mpr hle
    have hnorm : ‖(((c (k + 1) - c k : ℝ)) : ℂ)‖ = c (k + 1) - c k := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    rw [hnorm]
  have hnorm2 : c n * ‖z‖ ^ (n + 1)
      ≤ c 0 + ∑ k ∈ Finset.range n, (c (k + 1) - c k) * ‖z‖ ^ (k + 1) := by
    have h := hnorm_key
    rw [norm_mul, norm_pow, e1, e0, Finset.sum_congr rfl eDiff] at h
    exact h
  have hpow_le : ∀ k ∈ Finset.range n, (c (k + 1) - c k) * ‖z‖ ^ (k + 1)
      ≤ (c (k + 1) - c k) * ‖z‖ ^ n := by
    intro k hk
    have hmem : k < n := Finset.mem_range.mp hk
    have hle : c k ≤ c (k + 1) := hmono k hmem
    have hnn : (0 : ℝ) ≤ c (k + 1) - c k := sub_nonneg.mpr hle
    apply mul_le_mul_of_nonneg_left _ hnn
    apply pow_le_pow_right₀ hz1 (by omega : k + 1 ≤ n)
  have hsum_le : ∑ k ∈ Finset.range n, (c (k + 1) - c k) * ‖z‖ ^ (k + 1)
      ≤ ∑ k ∈ Finset.range n, (c (k + 1) - c k) * ‖z‖ ^ n := Finset.sum_le_sum hpow_le
  have hfactor : ∑ k ∈ Finset.range n, (c (k + 1) - c k) * ‖z‖ ^ n
      = (c n - c 0) * ‖z‖ ^ n := by
    rw [← Finset.sum_mul]
    rw [htele]
  have h1le : (1 : ℝ) ≤ ‖z‖ ^ n := one_le_pow₀ hz1
  have hc0le : c 0 ≤ c 0 * ‖z‖ ^ n := by
    calc c 0 = c 0 * 1 := by ring
      _ ≤ c 0 * ‖z‖ ^ n := by
          apply mul_le_mul_of_nonneg_left h1le (le_of_lt hpos0)
  have hfinal : c n * ‖z‖ ^ (n + 1) ≤ c n * ‖z‖ ^ n := by
    calc c n * ‖z‖ ^ (n + 1)
        ≤ c 0 + ∑ k ∈ Finset.range n, (c (k + 1) - c k) * ‖z‖ ^ (k + 1) := hnorm2
      _ ≤ c 0 + ∑ k ∈ Finset.range n, (c (k + 1) - c k) * ‖z‖ ^ n := by gcongr
      _ = c 0 + (c n - c 0) * ‖z‖ ^ n := by rw [hfactor]
      _ ≤ c 0 * ‖z‖ ^ n + (c n - c 0) * ‖z‖ ^ n := by gcongr
      _ = c n * ‖z‖ ^ n := by ring
  have hpow_le' : ‖z‖ ^ (n + 1) ≤ ‖z‖ ^ n :=
    le_of_mul_le_mul_left hfinal hposn
  have hlt' : ‖z‖ ^ n < ‖z‖ ^ (n + 1) :=
    pow_lt_pow_right₀ hlt (Nat.lt_succ_self n)
  linarith

private theorem lower_of_anti {n : ℕ} (hn : 1 ≤ n) (c : ℕ → ℝ)
    (hpos : ∀ k, k ≤ n → 0 < c k)
    (hanti : ∀ k, k < n → c (k + 1) ≤ c k)
    (z : ℂ)
    (hsum : ∑ k ∈ Finset.range (n + 1), ((c k : ℝ) : ℂ) * z ^ k = 0) :
    1 ≤ ‖z‖ := by
  by_contra hnge
  have hlt : ‖z‖ < (1 : ℝ) := lt_of_not_ge hnge
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  have hpos0 : 0 < c 0 := hpos 0 (by omega)
  have hposn : 0 < c n := hpos n le_rfl
  have htele_aux : ∀ m : ℕ, ∑ k ∈ Finset.range m, (c k - c (k + 1)) = c 0 - c m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  have htele : ∑ k ∈ Finset.range n, (c k - c (k + 1)) = c 0 - c n := htele_aux n
  have key : ((c n : ℝ) : ℂ) * z ^ (n + 1)
      = ((c 0 : ℝ) : ℂ) + ∑ k ∈ Finset.range n, (((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1) := by
    have hS0 : z * (∑ k ∈ Finset.range (n + 1), ((c k : ℝ) : ℂ) * z ^ k)
        - (∑ k ∈ Finset.range (n + 1), ((c k : ℝ) : ℂ) * z ^ k) = 0 := by
      rw [hsum]
      simp
    rw [Finset.mul_sum] at hS0
    have hexpand : (∑ k ∈ Finset.range (n + 1), z * (((c k : ℝ) : ℂ) * z ^ k))
        = ∑ k ∈ Finset.range (n + 1), ((c k : ℝ) : ℂ) * z ^ (k + 1) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hexpand] at hS0
    have hsplit1 : ∑ k ∈ Finset.range (n + 1), ((c k : ℝ) : ℂ) * z ^ (k + 1)
        = (∑ k ∈ Finset.range n, ((c k : ℝ) : ℂ) * z ^ (k + 1))
          + ((c n : ℝ) : ℂ) * z ^ (n + 1) := by
      exact Finset.sum_range_succ _ _
    have hsplit2 : ∑ k ∈ Finset.range (n + 1), ((c k : ℝ) : ℂ) * z ^ k
        = (∑ k ∈ Finset.range n, ((c (k + 1) : ℝ) : ℂ) * z ^ (k + 1))
          + ((c 0 : ℝ) : ℂ) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, mul_one]
    rw [hsplit1, hsplit2] at hS0
    have hsum_eq : ∑ k ∈ Finset.range n, (((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1)
        = (∑ k ∈ Finset.range n, ((c (k + 1) : ℝ) : ℂ) * z ^ (k + 1))
          - (∑ k ∈ Finset.range n, ((c k : ℝ) : ℂ) * z ^ (k + 1)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [Complex.ofReal_sub]
      ring
    linear_combination hS0 - hsum_eq
  have key2 : ((c 0 : ℝ) : ℂ)
      = ((c n : ℝ) : ℂ) * z ^ (n + 1)
        - ∑ k ∈ Finset.range n, (((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1) := by
    linear_combination -key
  have hnorm0 : ‖((c 0 : ℝ) : ℂ)‖
      ≤ ‖((c n : ℝ) : ℂ) * z ^ (n + 1)‖
        + ∑ k ∈ Finset.range n, ‖(((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1)‖ := by
    rw [key2]
    calc ‖((c n : ℝ) : ℂ) * z ^ (n + 1)
          - ∑ k ∈ Finset.range n, (((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1)‖
        ≤ ‖((c n : ℝ) : ℂ) * z ^ (n + 1)‖
          + ‖∑ k ∈ Finset.range n, (((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1)‖ :=
          norm_sub_le _ _
      _ ≤ ‖((c n : ℝ) : ℂ) * z ^ (n + 1)‖
          + ∑ k ∈ Finset.range n, ‖(((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1)‖ := by
          gcongr
          exact norm_sum_le _ _
  have e0 : ‖((c 0 : ℝ) : ℂ)‖ = c 0 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos0]
  have eN : ‖((c n : ℝ) : ℂ) * z ^ (n + 1)‖ = c n * ‖z‖ ^ (n + 1) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hposn]
  have eDiff : ∀ k ∈ Finset.range n, ‖(((c (k + 1) - c k : ℝ)) : ℂ) * z ^ (k + 1)‖
      = (c k - c (k + 1)) * ‖z‖ ^ (k + 1) := by
    intro k hk
    rw [norm_mul, norm_pow]
    have hle : c (k + 1) ≤ c k := hanti k (Finset.mem_range.mp hk)
    have hnn : (0 : ℝ) ≤ c k - c (k + 1) := sub_nonneg.mpr hle
    have hnorm : ‖(((c (k + 1) - c k : ℝ)) : ℂ)‖ = c k - c (k + 1) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      ring
    rw [hnorm]
  have hnorm2 : c 0 ≤ c n * ‖z‖ ^ (n + 1)
      + ∑ k ∈ Finset.range n, (c k - c (k + 1)) * ‖z‖ ^ (k + 1) := by
    have h := hnorm0
    rw [e0, eN, Finset.sum_congr rfl eDiff] at h
    exact h
  have hpow_one : ∀ k ∈ Finset.range n, (c k - c (k + 1)) * ‖z‖ ^ (k + 1)
      ≤ (c k - c (k + 1)) * 1 := by
    intro k hk
    have hle : c (k + 1) ≤ c k := hanti k (Finset.mem_range.mp hk)
    have hnn : (0 : ℝ) ≤ c k - c (k + 1) := sub_nonneg.mpr hle
    apply mul_le_mul_of_nonneg_left _ hnn
    exact pow_le_one₀ hznn (le_of_lt hlt)
  have hsum_le : ∑ k ∈ Finset.range n, (c k - c (k + 1)) * ‖z‖ ^ (k + 1)
      ≤ ∑ k ∈ Finset.range n, (c k - c (k + 1)) := by
    have h1 : ∑ k ∈ Finset.range n, (c k - c (k + 1)) * ‖z‖ ^ (k + 1)
        ≤ ∑ k ∈ Finset.range n, ((c k - c (k + 1)) * 1) := Finset.sum_le_sum hpow_one
    simpa using h1
  have hfactor : ∑ k ∈ Finset.range n, (c k - c (k + 1)) = c 0 - c n := htele
  have hstrict : c n * ‖z‖ ^ (n + 1) < c n := by
    have hpow : ‖z‖ ^ (n + 1) < (1 : ℝ) :=
      pow_lt_one₀ hznn hlt (by omega : n + 1 ≠ 0)
    calc c n * ‖z‖ ^ (n + 1) < c n * 1 :=
          mul_lt_mul_of_pos_left hpow hposn
      _ = c n := by ring
  have hfinal : c 0 < c n + (c 0 - c n) := by
    calc c 0 ≤ c n * ‖z‖ ^ (n + 1)
            + ∑ k ∈ Finset.range n, (c k - c (k + 1)) * ‖z‖ ^ (k + 1) := hnorm2
      _ < c n + ∑ k ∈ Finset.range n, (c k - c (k + 1)) := by
          apply add_lt_add_of_lt_of_le hstrict hsum_le
      _ = c n + (c 0 - c n) := by rw [hfactor]
  linarith

set_option backward.proofsInPublic true in
/-- **Eneström–Kakeya theorem.** Let $n \ge 1$ and let $a_0, a_1, \dots, a_n$ be positive real
numbers. Then every complex zero $z$ of the polynomial $f(z) = a_0 + a_1 z + \dots + a_n z^n$
satisfies $\rho_1 \le |z| \le \rho_2$, where $\rho_1$ and $\rho_2$ are the minimum and the maximum
of the ratios $a_k / a_{k+1}$ for $0 \le k \le n - 1$.

Source: Karl Dilcher and Larry Ericksen, "Polynomials Whose Coefficients Are Stern
Numbers," Journal of Integer Sequences 24 (2021), Article 21.10.3, Theorem 4.1
(quoted there as the classical Eneström–Kakeya theorem).
Public TeX URL: `https://cs.uwaterloo.ca/journals/JIS/VOL24/Dilcher/dilcher51.tex`
Retrieved TeX SHA-256:
`72f3e8444cd0fd6b5f55e89d6427f130b294841131d89c994fe3bb2971dbb19e`
Proves `Wanted` entry `enestrom_kakeya_zero_localization`.
-/
theorem enestrom_kakeya_zero_localization
    {n : ℕ} (hn : 1 ≤ n) (a : Fin (n + 1) → ℝ) (hpos : ∀ k, 0 < a k) :
    ∀ z : ℂ,
      (∑ k : Fin (n + 1),
        Polynomial.C ((a k : ℝ) : ℂ) * Polynomial.X ^ (k : ℕ)).IsRoot z →
        (Finset.image (fun k : Fin n => a k.castSucc / a k.succ) Finset.univ).min'
          ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, by omega⟩)⟩ ≤ ‖z‖ ∧
        ‖z‖ ≤ (Finset.image (fun k : Fin n => a k.castSucc / a k.succ)
          Finset.univ).max'
          ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, by omega⟩)⟩ := by
  intro z hz
  set S : Finset ℝ := Finset.image (fun k : Fin n => a k.castSucc / a k.succ) Finset.univ with hSdef
  set m : ℝ := S.min' ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, by omega⟩)⟩ with hmdef
  set R : ℝ := S.max' ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, by omega⟩)⟩ with hRdef
  let A : ℕ → ℝ := fun k => if h : k < n + 1 then a ⟨k, h⟩ else 0
  have hA : ∀ k (h : k < n + 1), A k = a ⟨k, h⟩ := by
    intro k h
    simp only [A, h, dite_true]
  have hposA : ∀ k, k ≤ n → 0 < A k := by
    intro k hk
    have hlt : k < n + 1 := by omega
    rw [hA k hlt]
    exact hpos _
  have heval : Polynomial.eval z (∑ k : Fin (n + 1),
      Polynomial.C ((a k : ℝ) : ℂ) * Polynomial.X ^ (k : ℕ)) = 0 := hz
  rw [Polynomial.eval_finsetSum] at heval
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at heval
  have hconv : (∑ k : Fin (n + 1), ((a k : ℝ) : ℂ) * z ^ (k : ℕ))
      = ∑ k ∈ Finset.range (n + 1), (((A k : ℝ)) : ℂ) * z ^ k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => (((A k : ℝ)) : ℂ) * z ^ k) (n + 1)]
    apply Finset.sum_congr rfl
    intro k _
    have hlt : (k.val < n + 1) := k.isLt
    have hAk : A k.val = a k := by
      have h1 := hA k.val hlt
      have h2 : (⟨k.val, hlt⟩ : Fin (n + 1)) = k := Fin.eta k hlt
      rw [h2] at h1
      exact h1
    rw [hAk]
  have hsumA : ∑ k ∈ Finset.range (n + 1), (((A k : ℝ)) : ℂ) * z ^ k = 0 := by
    rw [← hconv]
    exact heval
  have hRpos : 0 < R := by
    have hmem : R ∈ S := Finset.max'_mem S _
    rw [hSdef] at hmem
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨k, hk⟩ := hmem
    have h1 : 0 < a k.castSucc := hpos _
    have h2 : 0 < a k.succ := hpos _
    rw [← hk]
    exact div_pos h1 h2
  have hmpos : 0 < m := by
    have hmem : m ∈ S := Finset.min'_mem S _
    rw [hSdef] at hmem
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨k, hk⟩ := hmem
    have h1 : 0 < a k.castSucc := hpos _
    have h2 : 0 < a k.succ := hpos _
    rw [← hk]
    exact div_pos h1 h2
  have hRbound : ∀ k, k < n → A k / A (k + 1) ≤ R := by
    intro k hk
    have hkfin : k < n := hk
    have hmem : a (⟨k, hkfin⟩ : Fin n).castSucc / a (⟨k, hkfin⟩ : Fin n).succ ∈ S := by
      rw [hSdef]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hle : a (⟨k, hkfin⟩ : Fin n).castSucc / a (⟨k, hkfin⟩ : Fin n).succ ≤ R := by
      exact Finset.le_max' S _ hmem
    have h1 : (⟨k, hkfin⟩ : Fin n).castSucc = (⟨k, by omega⟩ : Fin (n + 1)) :=
      Fin.castSucc_mk n k hkfin
    have h2 : (⟨k, hkfin⟩ : Fin n).succ = (⟨k + 1, by omega⟩ : Fin (n + 1)) :=
      Fin.succ_mk n k hkfin
    rw [h1, h2] at hle
    have e1 : A k = a ⟨k, by omega⟩ := hA k (by omega)
    have e2 : A (k + 1) = a ⟨k + 1, by omega⟩ := hA (k + 1) (by omega)
    rw [e1, e2]
    exact hle
  have hmbound : ∀ k, k < n → m ≤ A k / A (k + 1) := by
    intro k hk
    have hkfin : k < n := hk
    have hmem : a (⟨k, hkfin⟩ : Fin n).castSucc / a (⟨k, hkfin⟩ : Fin n).succ ∈ S := by
      rw [hSdef]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hle : m ≤ a (⟨k, hkfin⟩ : Fin n).castSucc / a (⟨k, hkfin⟩ : Fin n).succ := by
      exact Finset.min'_le S _ hmem
    have h1 : (⟨k, hkfin⟩ : Fin n).castSucc = (⟨k, by omega⟩ : Fin (n + 1)) :=
      Fin.castSucc_mk n k hkfin
    have h2 : (⟨k, hkfin⟩ : Fin n).succ = (⟨k + 1, by omega⟩ : Fin (n + 1)) :=
      Fin.succ_mk n k hkfin
    rw [h1, h2] at hle
    have e1 : A k = a ⟨k, by omega⟩ := hA k (by omega)
    have e2 : A (k + 1) = a ⟨k + 1, by omega⟩ := hA (k + 1) (by omega)
    rw [e1, e2]
    exact hle
  have hUpper : ‖z‖ ≤ R := by
    have hRne : R ≠ 0 := ne_of_gt hRpos
    have hRc : ((R : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hRne
    let cU : ℕ → ℝ := fun k => A k * R ^ k
    have hposU : ∀ k, k ≤ n → 0 < cU k := by
      intro k hk
      change 0 < A k * R ^ k
      exact mul_pos (hposA k hk) (pow_pos hRpos k)
    have hmonoU : ∀ k, k < n → cU k ≤ cU (k + 1) := by
      intro k hk
      change A k * R ^ k ≤ A (k + 1) * R ^ (k + 1)
      have hAk1 : 0 < A (k + 1) := hposA (k + 1) (by omega)
      have hRk : 0 ≤ R ^ k := le_of_lt (pow_pos hRpos k)
      have hdiv : A k / A (k + 1) ≤ R := hRbound k hk
      have hAle : A k ≤ R * A (k + 1) := by
        rw [div_le_iff₀ hAk1] at hdiv
        linarith [hdiv]
      calc A k * R ^ k ≤ (R * A (k + 1)) * R ^ k :=
            mul_le_mul_of_nonneg_right hAle hRk
        _ = A (k + 1) * R ^ (k + 1) := by ring
    have hsumU : ∑ k ∈ Finset.range (n + 1), (((cU k : ℝ)) : ℂ) * (z / ((R : ℝ) : ℂ)) ^ k = 0 := by
      have hpoint : ∀ k ∈ Finset.range (n + 1),
          ((((cU k : ℝ))) : ℂ) * (z / ((R : ℝ) : ℂ)) ^ k
          = ((A k : ℝ) : ℂ) * z ^ k := by
        intro k _
        have hRpk : ((R : ℝ) : ℂ) ^ k ≠ 0 := pow_ne_zero k hRc
        change (((A k * R ^ k : ℝ)) : ℂ) * _ = _
        push_cast
        rw [div_pow]
        field_simp
      rw [Finset.sum_congr rfl hpoint]
      exact hsumA
    have hle : ‖z / ((R : ℝ) : ℂ)‖ ≤ 1 :=
      upper_of_mono hn cU hposU hmonoU _ hsumU
    rw [norm_div] at hle
    have hRnorm : ‖((R : ℝ) : ℂ)‖ = R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
    rw [hRnorm] at hle
    rw [div_le_one hRpos] at hle
    exact hle
  have hLower : m ≤ ‖z‖ := by
    have hmne : m ≠ 0 := ne_of_gt hmpos
    have hmc : ((m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmne
    let cL : ℕ → ℝ := fun k => A k * m ^ k
    have hposL : ∀ k, k ≤ n → 0 < cL k := by
      intro k hk
      change 0 < A k * m ^ k
      exact mul_pos (hposA k hk) (pow_pos hmpos k)
    have hantiL : ∀ k, k < n → cL (k + 1) ≤ cL k := by
      intro k hk
      change A (k + 1) * m ^ (k + 1) ≤ A k * m ^ k
      have hAk1 : 0 < A (k + 1) := hposA (k + 1) (by omega)
      have hmk : 0 ≤ m ^ k := le_of_lt (pow_pos hmpos k)
      have hdiv : m ≤ A k / A (k + 1) := hmbound k hk
      have hAle : m * A (k + 1) ≤ A k := by
        rw [le_div_iff₀ hAk1] at hdiv
        linarith [hdiv]
      calc A (k + 1) * m ^ (k + 1) = (m * A (k + 1)) * m ^ k := by ring
        _ ≤ A k * m ^ k := by
            exact mul_le_mul_of_nonneg_right hAle hmk
    have hsumL : ∑ k ∈ Finset.range (n + 1), (((cL k : ℝ)) : ℂ) * (z / ((m : ℝ) : ℂ)) ^ k = 0 := by
      have hpoint : ∀ k ∈ Finset.range (n + 1),
          ((((cL k : ℝ))) : ℂ) * (z / ((m : ℝ) : ℂ)) ^ k
          = ((A k : ℝ) : ℂ) * z ^ k := by
        intro k _
        have hmpk : ((m : ℝ) : ℂ) ^ k ≠ 0 := pow_ne_zero k hmc
        change (((A k * m ^ k : ℝ)) : ℂ) * _ = _
        push_cast
        rw [div_pow]
        field_simp
      rw [Finset.sum_congr rfl hpoint]
      exact hsumA
    have hge : 1 ≤ ‖z / ((m : ℝ) : ℂ)‖ :=
      lower_of_anti hn cL hposL hantiL _ hsumL
    rw [norm_div] at hge
    have hmnorm : ‖((m : ℝ) : ℂ)‖ = m := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmpos]
    rw [hmnorm] at hge
    rw [one_le_div hmpos] at hge
    exact hge
  exact ⟨hLower, hUpper⟩

end MathlibExt.Analysis.Complex.EnestromKakeya
