/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.ZetaValues

/-!
# Functions in the Selberg class

This module defines `SelbergClassFunction`, the functions in the Selberg class, and proves
that the $k$-th derivative of such a function has no $a$-points far to the right, under the
hypothesis that $a \ne 0$ or some Dirichlet coefficient $a(n)$ with $n \ge 2$ is nonzero.
-/

namespace MetaMathlibExt

open Filter Asymptotics

@[expose] public section

/-- **Functions in the Selberg class.** A function in the Selberg class consists of Dirichlet
coefficients $a \colon \mathbb{N} \to \mathbb{C}$, a function $F \colon \mathbb{C} \to \mathbb{C}$,
a number $r \in \mathbb{N}$ of Gamma factors, a conductor $Q > 0$, real numbers
$\lambda_1, \dots, \lambda_r > 0$, complex numbers $\mu_1, \dots, \mu_r$ with
$\operatorname{Re} \mu_j \ge 0$ and a root number $\omega \in \mathbb{C}$ with $|\omega| = 1$,
such that:

- $a(1) = 1$;
- for every $s$ with $\operatorname{Re} s > 1$ the Dirichlet series $\sum_{n \ge 1} a(n) n^{-s}$
  converges absolutely and equals $F(s)$;
- (Ramanujan hypothesis) for every $\varepsilon > 0$ there is a constant $C$ with
  $|a(n)| \le C n^{\varepsilon}$ for all $n$;
- (Euler product) there are $b \colon \mathbb{N} \to \mathbb{C}$ with $b(n) = 0$ unless $n$ is a
  prime power, a real $\theta < 1/2$ and a constant $C$ with $|b(n)| \le C n^{\theta}$ for all $n$,
  and a real $\sigma_0$ such that for every $s$ with $\operatorname{Re} s > \sigma_0$ the series
  $\sum_{n \ge 1} b(n) n^{-s}$ converges absolutely and $F(s) = \exp \sum_{n \ge 1} b(n) n^{-s}$;
- (analytic continuation) there are $m \in \mathbb{N}$, an entire function $g$ and real numbers
  $\rho$, $A$ with $|g(s)| \le A e^{|s|^{\rho}}$ for all $s$ (so $g$ has finite order) and
  $g(s) = (s - 1)^m F(s)$ for all $s \ne 1$;
- (functional equation) with $\Phi(s) = F(s) Q^s \prod_{j=1}^r \Gamma(\lambda_j s + \mu_j)$, the
  identity $\Phi(s) = \omega \overline{\Phi(1 - \bar s)}$ holds for every $s \ne 0, 1$ such that
  for no $j$ is $\lambda_j s + \mu_j$ or $\lambda_j (1 - \bar s) + \mu_j$ an integer $\le 0$.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Section 2. -/
structure SelbergClassFunction where
  /-- The Dirichlet coefficients `a(n)`. -/
  coeff : ℕ → ℂ
  /-- The function `F` (its value at the possible pole `s = 1` is irrelevant). -/
  toFun : ℂ → ℂ
  coeff_one : coeff 1 = 1
  lseries : ∀ s : ℂ, 1 < s.re → LSeriesSummable coeff s ∧ LSeries coeff s = toFun s
  ramanujan : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, ‖coeff n‖ ≤ C * (n : ℝ) ^ ε
  eulerProduct : ∃ b : ℕ → ℂ, (∀ n, b n ≠ 0 → IsPrimePow n) ∧
    (∃ θ : ℝ, θ < 1 / 2 ∧ ∃ C : ℝ, ∀ n : ℕ, ‖b n‖ ≤ C * (n : ℝ) ^ θ) ∧
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → LSeriesSummable b s ∧ toFun s = Complex.exp (LSeries b s)
  analyticContinuation : ∃ m : ℕ, ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
    (∃ ρ A : ℝ, ∀ s : ℂ, ‖g s‖ ≤ A * Real.exp (‖s‖ ^ ρ)) ∧
    ∀ s : ℂ, s ≠ 1 → g s = (s - 1) ^ m * toFun s
  /-- The number `r` of Gamma factors. -/
  r : ℕ
  /-- The conductor `Q_F`. -/
  Q : ℝ
  Q_pos : 0 < Q
  /-- The Gamma-factor scalings `λ_j`. -/
  lam : Fin r → ℝ
  lam_pos : ∀ j, 0 < lam j
  /-- The Gamma-factor shifts `μ_j`. -/
  mu : Fin r → ℂ
  mu_re_nonneg : ∀ j, 0 ≤ (mu j).re
  /-- The root number `ω`. -/
  omega : ℂ
  norm_omega : ‖omega‖ = 1
  functionalEquation : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
    (∀ j (n : ℕ), (lam j : ℂ) * s + mu j ≠ -(n : ℂ) ∧
      (lam j : ℂ) * (1 - (starRingEnd ℂ) s) + mu j ≠ -(n : ℂ)) →
    toFun s * (Q : ℂ) ^ s * ∏ j, Complex.Gamma ((lam j : ℂ) * s + mu j) =
      omega * (starRingEnd ℂ) (toFun (1 - (starRingEnd ℂ) s) *
        (Q : ℂ) ^ (1 - (starRingEnd ℂ) s) *
        ∏ j, Complex.Gamma ((lam j : ℂ) * (1 - (starRingEnd ℂ) s) + mu j))

namespace SelbergClassFunction.exists_no_aPoint_right

private lemma logMul_iterate_apply (F : SelbergClassFunction) (k n : ℕ) :
    (LSeries.logMul^[k] F.coeff) n = (Complex.log (n : ℂ)) ^ k * F.coeff n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ']
    ring

private lemma norm_logMul_iterate_le (F : SelbergClassFunction) (k n : ℕ) (hn : 1 ≤ n)
    (C : ℝ) (hC : ∀ m : ℕ, ‖F.coeff m‖ ≤ C * (m : ℝ) ^ (1 : ℝ)) :
    ‖(LSeries.logMul^[k] F.coeff) n‖ ≤ C * (n : ℝ) ^ (k + 1) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : ‖Complex.log (n : ℂ)‖ = Real.log n := by
    have h : Complex.log (n : ℂ) = (Real.log n : ℂ) :=
      (Complex.ofReal_log (show (0:ℝ) ≤ (n:ℝ) by positivity)).symm
    rw [h]
    exact Complex.norm_of_nonneg (Real.log_nonneg hnR)
  have hlogle : Real.log n ≤ (n : ℝ) := Real.log_le_self (by linarith)
  rw [logMul_iterate_apply, norm_mul, norm_pow, hlog]
  have h1 : (Real.log n) ^ k ≤ (n : ℝ) ^ k :=
    pow_le_pow_left₀ (Real.log_nonneg hnR) hlogle k
  have hC1 : ‖F.coeff n‖ ≤ C * (n : ℝ) := by
    simpa using hC n
  have hC0 : 0 ≤ C := by
    have := hC 1
    rw [F.coeff_one] at this
    exact le_trans zero_le_one (by simpa using this)
  calc (Real.log n) ^ k * ‖F.coeff n‖
      ≤ (n : ℝ) ^ k * (C * (n : ℝ)) :=
        mul_le_mul h1 hC1 (norm_nonneg _) (by positivity)
    _ = C * (n : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

private lemma iteratedDeriv_eq (F : SelbergClassFunction) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    iteratedDeriv k F.toFun s = (-1) ^ k * LSeries (LSeries.logMul^[k] F.coeff) s := by
  obtain ⟨y, hy1, hy2⟩ := exists_between hs
  have hsum : LSeriesSummable F.coeff (y : ℂ) := (F.lseries (y : ℂ) (by simpa using hy1)).1
  have habs : LSeries.abscissaOfAbsConv F.coeff < s.re := by
    have hle := hsum.abscissaOfAbsConv_le
    simp only [Complex.ofReal_re] at hle
    exact hle.trans_lt (by exact_mod_cast hy2)
  have hEqOn : Set.EqOn F.toFun (LSeries F.coeff) {z : ℂ | 1 < z.re} :=
    fun z hz ↦ (F.lseries z hz).2.symm
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h := (hEqOn.iteratedDeriv_of_isOpen hopen k) hs
  rw [h]
  exact LSeries_iteratedDeriv k habs

private lemma summable_logMul_iterate (F : SelbergClassFunction) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (LSeries.logMul^[k] F.coeff) s := by
  obtain ⟨y, hy1, hy2⟩ := exists_between hs
  have hsum : LSeriesSummable F.coeff (y : ℂ) := (F.lseries (y : ℂ) (by simpa using hy1)).1
  have habs : LSeries.abscissaOfAbsConv F.coeff < s.re := by
    have hle := hsum.abscissaOfAbsConv_le
    simp only [Complex.ofReal_re] at hle
    exact hle.trans_lt (by exact_mod_cast hy2)
  have habs' : LSeries.abscissaOfAbsConv (LSeries.logMul^[k] F.coeff) < s.re := by
    rw [LSeries.abscissaOfAbsConv_logPowMul]
    exact habs
  exact LSeriesSummable_of_abscissaOfAbsConv_lt_re habs'

private lemma norm_term_le (F : SelbergClassFunction) (k : ℕ) {s : ℂ}
    (hs : (k : ℝ) + 3 ≤ s.re) (C : ℝ) (hC : ∀ m : ℕ, ‖F.coeff m‖ ≤ C * (m : ℝ) ^ (1 : ℝ))
    (q n : ℕ) (hq : 2 ≤ q) (hqn : q ≤ n) :
    ‖LSeries.term (LSeries.logMul^[k] F.coeff) s n‖ ≤
      C * (1 / (n : ℝ) ^ 2) * ((q : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹ := by
  have hn : 2 ≤ n := hq.trans hqn
  have hn0 : n ≠ 0 := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqnR : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hqn
  have hpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hE : 0 ≤ s.re - (k : ℝ) - 3 := by linarith
  have hQpos : (0:ℝ) < (q : ℝ) ^ (s.re - (k : ℝ) - 3) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hsplit : (n : ℝ) ^ s.re = (n : ℝ) ^ (k + 3) * (n : ℝ) ^ (s.re - (k : ℝ) - 3) := by
    have h1 : (n : ℝ) ^ s.re =
        (n : ℝ) ^ ((k : ℝ) + 3) * (n : ℝ) ^ (s.re - (k : ℝ) - 3) := by
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    rw [h1]
    congr 1
    rw [show ((k : ℝ) + 3) = ((k + 3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hQle : (q : ℝ) ^ (s.re - (k : ℝ) - 3) ≤ (n : ℝ) ^ (s.re - (k : ℝ) - 3) :=
    Real.rpow_le_rpow (by positivity) hqnR hE
  have hgnorm : ‖LSeries.term (LSeries.logMul^[k] F.coeff) s n‖ =
      ‖(LSeries.logMul^[k] F.coeff) n‖ / (n : ℝ) ^ s.re := by
    rw [LSeries.norm_term_eq]
    simp [hn0]
  rw [hgnorm]
  have hg := norm_logMul_iterate_le F k n (by omega) C hC
  have hdenpos : (0:ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hpos _
  have hstep : ‖(LSeries.logMul^[k] F.coeff) n‖ / (n : ℝ) ^ s.re ≤
      C * (n : ℝ) ^ (k + 1) / (n : ℝ) ^ s.re :=
    (div_le_div_iff_of_pos_right hdenpos).mpr hg
  refine hstep.trans ?_
  have hpow : (n : ℝ) ^ (k + 3) = (n : ℝ) ^ (k + 1) * (n : ℝ) ^ 2 := by
    rw [show k + 3 = (k + 1) + 2 by omega, pow_add]
  have hC0 : 0 ≤ C := by
    have h1 := hC 1
    rw [F.coeff_one] at h1
    have : (1:ℝ) ≤ C := by simpa using h1
    linarith
  calc C * (n : ℝ) ^ (k + 1) / (n : ℝ) ^ s.re
      = C * (1 / (n : ℝ) ^ 2) * ((n : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹ := by
        rw [hsplit, hpow]
        field_simp
    _ ≤ C * (1 / (n : ℝ) ^ 2) * ((q : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact inv_anti₀ hQpos hQle

private lemma norm_LSeries_le (F : SelbergClassFunction) (k : ℕ) {s : ℂ}
    (hs1 : 1 < s.re) (hs : (k : ℝ) + 3 ≤ s.re) (hk : 1 ≤ k) (C : ℝ)
    (hC : ∀ m : ℕ, ‖F.coeff m‖ ≤ C * (m : ℝ) ^ (1 : ℝ)) :
    ‖LSeries (LSeries.logMul^[k] F.coeff) s‖ ≤
      C * (Real.pi ^ 2 / 6) * ((2 : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹ := by
  have hsum := summable_logMul_iterate F k hs1
  have hnorm : Summable (fun n ↦ ‖LSeries.term (LSeries.logMul^[k] F.coeff) s n‖) :=
    hsum.norm
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  have hbound : Summable (fun n : ℕ ↦ (C * ((2 : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹) *
      (1 / (n : ℝ) ^ 2)) :=
    hasSum_zeta_two.summable.mul_left _
  have hle : ∀ n : ℕ, ‖LSeries.term (LSeries.logMul^[k] F.coeff) s n‖ ≤
      (C * ((2 : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹) * (1 / (n : ℝ) ^ 2) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rcases eq_or_ne n 1 with rfl | hn1
    · have hC0 : 0 ≤ C := by
        have h1 := hC 1
        rw [F.coeff_one] at h1
        have hle1 : (1:ℝ) ≤ C := by simpa using h1
        linarith
      have hg : (LSeries.logMul^[k] F.coeff) 1 = 0 := by
        have hlog : Complex.log ((1 : ℕ) : ℂ) = 0 := by simp
        rw [logMul_iterate_apply, hlog, zero_pow (by omega : k ≠ 0), zero_mul]
      have hterm : LSeries.term (LSeries.logMul^[k] F.coeff) s 1 = 0 := by
        simp [LSeries.term, hg]
      rw [hterm, norm_zero]
      simp only [Nat.cast_one, one_pow, div_one, mul_one]
      exact mul_nonneg hC0 (inv_nonneg.mpr (Real.rpow_nonneg (by norm_num) _))
    · have h := norm_term_le F k hs C hC 2 n (by norm_num) (by omega)
      calc ‖LSeries.term (LSeries.logMul^[k] F.coeff) s n‖
          ≤ C * (1 / (n : ℝ) ^ 2) * ((2 : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹ := h
        _ = (C * ((2 : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹) * (1 / (n : ℝ) ^ 2) := by ring
  have htsum := hnorm.tsum_le_tsum hle hbound
  rw [tsum_mul_left, hasSum_zeta_two.tsum_eq] at htsum
  calc ∑' n, ‖LSeries.term (LSeries.logMul^[k] F.coeff) s n‖
      ≤ (C * ((2 : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹) * (Real.pi ^ 2 / 6) := htsum
    _ = C * (Real.pi ^ 2 / 6) * ((2 : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹ := by ring

private lemma norm_tsum_update_le (F : SelbergClassFunction) (k : ℕ) {s : ℂ}
    (hs1 : 1 < s.re) (hs : (k : ℝ) + 3 ≤ s.re) (hk : 1 ≤ k) (C : ℝ)
    (hC : ∀ m : ℕ, ‖F.coeff m‖ ≤ C * (m : ℝ) ^ (1 : ℝ))
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (hmin : ∀ n, 2 ≤ n → n < ℓ → F.coeff n = 0) :
    ‖∑' n, Function.update (LSeries.term (LSeries.logMul^[k] F.coeff) s) ℓ 0 n‖ ≤
      C * (Real.pi ^ 2 / 6) * (((ℓ + 1 : ℕ) : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹ := by
  have hC0 : 0 ≤ C := by
    have h1 := hC 1
    rw [F.coeff_one] at h1
    have hle1 : (1:ℝ) ≤ C := by simpa using h1
    linarith
  have hQnonneg : 0 ≤ (((ℓ + 1 : ℕ) : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹ :=
    inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
  have hsum := summable_logMul_iterate F k hs1
  set E : ℝ := s.re - (k : ℝ) - 3 with hEdef
  set Q : ℝ := ((ℓ + 1 : ℕ) : ℝ) ^ E with hQdef
  have hZsum : Summable (fun n : ℕ ↦ (C * Q⁻¹) * (1 / (n : ℝ) ^ 2)) :=
    hasSum_zeta_two.summable.mul_left _
  have hZnn : ∀ n : ℕ, 0 ≤ (C * Q⁻¹) * (1 / (n : ℝ) ^ 2) := fun n ↦ by positivity
  have hBsum : Summable (fun n : ℕ ↦ if n ≤ ℓ then (0:ℝ) else (C * Q⁻¹) * (1 / (n : ℝ) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) hZsum
    · by_cases hn : n ≤ ℓ
      · simp only [hn, ite_true, le_refl]
      · simp only [hn, ite_false]; exact hZnn n
    · by_cases hn : n ≤ ℓ
      · simp only [hn, ite_true]; exact hZnn n
      · simp only [hn, ite_false, le_refl]
  have hBnn : ∀ n : ℕ, ‖Function.update (LSeries.term (LSeries.logMul^[k] F.coeff) s) ℓ 0 n‖ ≤
      (if n ≤ ℓ then (0:ℝ) else (C * Q⁻¹) * (1 / (n : ℝ) ^ 2)) := by
    intro n
    by_cases hnℓ : n = ℓ
    · subst hnℓ
      simp only [Function.update_self]
      simp
    · simp only [Function.update_of_ne hnℓ]
      by_cases hnle : n ≤ ℓ
      · simp only [hnle, ite_true]
        have hterm : LSeries.term (LSeries.logMul^[k] F.coeff) s n = 0 := by
          rcases eq_or_ne n 0 with rfl | hn0
          · simp
          rcases eq_or_ne n 1 with rfl | hn1
          · have hlog : Complex.log ((1 : ℕ) : ℂ) = 0 := by simp
            have hg : (LSeries.logMul^[k] F.coeff) 1 = 0 := by
              rw [logMul_iterate_apply, hlog, zero_pow (by omega : k ≠ 0), zero_mul]
            simp [LSeries.term, hg]
          · have hn2 : 2 ≤ n := by omega
            have hnlt : n < ℓ := by omega
            have hg : (LSeries.logMul^[k] F.coeff) n = 0 := by
              rw [logMul_iterate_apply, hmin n hn2 hnlt, mul_zero]
            simp [LSeries.term, hg]
        rw [hterm]
        simp
      · simp only [hnle, ite_false]
        have hnq : ℓ + 1 ≤ n := by omega
        have h := norm_term_le F k hs C hC (ℓ + 1) n (by omega) hnq
        calc ‖LSeries.term (LSeries.logMul^[k] F.coeff) s n‖
            ≤ C * (1 / (n : ℝ) ^ 2) * (((ℓ + 1 : ℕ) : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹ := h
          _ = (C * Q⁻¹) * (1 / (n : ℝ) ^ 2) := by simp [Q, hEdef]; ring
  have hnorm : Summable (fun n ↦
      ‖Function.update (LSeries.term (LSeries.logMul^[k] F.coeff) s) ℓ 0 n‖) :=
    (hsum.update ℓ 0).norm
  have h1 := (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hBnn hBsum)
  have hleBZ : ∀ n : ℕ, (if n ≤ ℓ then (0:ℝ) else (C * Q⁻¹) * (1 / (n : ℝ) ^ 2)) ≤
      (C * Q⁻¹) * (1 / (n : ℝ) ^ 2) := by
    intro n
    by_cases hn : n ≤ ℓ
    · simp only [hn, ite_true]; exact hZnn n
    · simp only [hn, ite_false, le_refl]
  have h2 := hBsum.tsum_le_tsum hleBZ hZsum
  rw [tsum_mul_left, hasSum_zeta_two.tsum_eq] at h2
  refine h1.trans ?_
  calc ∑' n, (if n ≤ ℓ then (0:ℝ) else (C * Q⁻¹) * (1 / (n : ℝ) ^ 2))
      ≤ (C * Q⁻¹) * (Real.pi ^ 2 / 6) := h2
    _ = C * (Real.pi ^ 2 / 6) * (((ℓ + 1 : ℕ) : ℝ) ^ (s.re - (k : ℝ) - 3))⁻¹ := by
        simp [Q, hEdef]; ring

end SelbergClassFunction.exists_no_aPoint_right

namespace SelbergClassFunction

open exists_no_aPoint_right

/-- **Lemma 1 (no a-points of derivatives far to the right).** Let $F$ be a function in the
Selberg class with Dirichlet coefficients $a(n)$, let $k \ge 1$, and let $a \in \mathbb{C}$ be such
that $a \ne 0$ or $a(n) \ne 0$ for some $n \ge 2$. Then there is a real number $E_1 \ge 1$ such
that the $k$-th derivative $F^{(k)}$ satisfies $F^{(k)}(s) \ne a$ for every $s \in \mathbb{C}$
with $\operatorname{Re} s \ge E_1$.

For $F = 1$ and $a = 0$ every point is a $0$-point, so the hypothesis on $a$ cannot be dropped.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 1 (`integers-2024-A11-lem-1`). -/
theorem exists_no_aPoint_right (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (hF : a ≠ 0 ∨ ∃ n, 2 ≤ n ∧ F.coeff n ≠ 0) :
    ∃ E₁ : ℝ, 1 ≤ E₁ ∧ ∀ s : ℂ, E₁ ≤ s.re → iteratedDeriv k F.toFun s ≠ a := by
  obtain ⟨C, hC⟩ := F.ramanujan 1 one_pos
  have hC1 : (1:ℝ) ≤ C := by
    have h1 := hC 1
    rw [F.coeff_one] at h1
    simpa using h1
  have hC0 : 0 ≤ C := by linarith
  have hCpos : 0 < C := by linarith
  have hPpos : 0 < Real.pi ^ 2 / 6 := by positivity
  by_cases ha : a ≠ 0
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
      (show (0:ℝ) < ‖a‖ / (C * (Real.pi ^ 2 / 6)) by positivity) (show (1/2:ℝ) < 1 by norm_num)
    refine ⟨max 1 ((k:ℝ) + 3 + N), le_max_left _ _, fun s hs ↦ ?_⟩
    have hs1 : 1 < s.re := by
      have hmax := le_max_right (1:ℝ) ((k:ℝ) + 3 + N)
      have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
      linarith [hs, hmax, hkR, hN0]
    have hs3 : (k:ℝ) + 3 ≤ s.re := by
      have hmax := le_max_right (1:ℝ) ((k:ℝ) + 3 + N)
      have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
      linarith [hs, hmax, hN0]
    have hbound := norm_LSeries_le F k hs1 hs3 hk C hC
    have hfactor : C * (Real.pi ^ 2 / 6) * ((2:ℝ) ^ (s.re - (k:ℝ) - 3))⁻¹ < ‖a‖ := by
      have hle : (2:ℝ) ^ ((N:ℝ)) ≤ (2:ℝ) ^ (s.re - (k:ℝ) - 3) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          have hmax := le_max_right (1:ℝ) ((k:ℝ) + 3 + N)
          have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
          linarith [hs, hmax, hN0])
      have hpow : ((2:ℝ) ^ ((N:ℝ))) = (2:ℝ) ^ N := Real.rpow_natCast _ _
      have hinv : ((2:ℝ) ^ (s.re - (k:ℝ) - 3))⁻¹ ≤ ((2:ℝ) ^ N)⁻¹ := by
        rw [← hpow]
        exact inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _) hle
      have hN' : C * (Real.pi ^ 2 / 6) * ((2:ℝ) ^ N)⁻¹ < ‖a‖ := by
        have h2 : ((2:ℝ) ^ N)⁻¹ = (1/2 : ℝ) ^ N := by rw [one_div_pow, one_div]
        rw [h2]
        have hN2 := (lt_div_iff₀ (by positivity : (0:ℝ) < C * (Real.pi ^ 2 / 6))).mp hN
        rw [mul_comm] at hN2
        exact hN2
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hinv (by positivity)) hN'
    intro heq
    have hnorm : ‖iteratedDeriv k F.toFun s‖ = ‖LSeries (LSeries.logMul^[k] F.coeff) s‖ := by
      rw [iteratedDeriv_eq F k hs1]
      simp
    rw [heq] at hnorm
    have hlt := hbound.trans_lt hfactor
    rw [← hnorm] at hlt
    exact (lt_irrefl ‖a‖) hlt
  · have ha0 : a = 0 := not_ne_iff.mp ha
    rcases hF with h | h
    · exact absurd ha0 h
    · obtain ⟨n₀, hn₀, hcoeff₀⟩ := h
      classical
      have hex : ∃ n, 2 ≤ n ∧ F.coeff n ≠ 0 := ⟨n₀, hn₀, hcoeff₀⟩
      set ℓ : ℕ := Nat.find hex with hℓdef
      have hspec := Nat.find_spec hex
      have hℓ2 : 2 ≤ ℓ := hspec.1
      have hℓcoeff : F.coeff ℓ ≠ 0 := hspec.2
      have hmin : ∀ n, 2 ≤ n → n < ℓ → F.coeff n = 0 := by
        intro n hn2 hnlt
        by_contra hne
        exact Nat.find_min hex hnlt ⟨hn2, hne⟩
      have hlogpos : 0 < Real.log ℓ := Real.log_pos (by exact_mod_cast (by omega : 1 < ℓ))
      have hDpos : 0 < (Real.log ℓ) ^ k * ‖F.coeff ℓ‖ :=
        mul_pos (pow_pos hlogpos k) (norm_pos_iff.mpr hℓcoeff)
      set ρ : ℝ := (ℓ:ℝ) / ((ℓ:ℝ) + 1) with hρdef
      have hρ0 : 0 < ρ := by positivity
      have hρ1 : ρ < 1 := by
        rw [hρdef, div_lt_one (by positivity)]
        linarith
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
        (show (0:ℝ) < (Real.log ℓ) ^ k * ‖F.coeff ℓ‖ /
          (C * (Real.pi ^ 2 / 6) * (ℓ:ℝ) ^ ((k:ℝ) + 3)) by positivity)
        hρ1
      refine ⟨max 1 ((k:ℝ) + 3 + N), le_max_left _ _, fun s hs ↦ ?_⟩
      have hs1 : 1 < s.re := by
        have hmax := le_max_right (1:ℝ) ((k:ℝ) + 3 + N)
        have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
        linarith [hs, hmax, hkR, hN0]
      have hs3 : (k:ℝ) + 3 ≤ s.re := by
        have hmax := le_max_right (1:ℝ) ((k:ℝ) + 3 + N)
        have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
        linarith [hs, hmax, hN0]
      have hEN : (N:ℝ) ≤ s.re - (k:ℝ) - 3 := by
        have hmax := le_max_right (1:ℝ) ((k:ℝ) + 3 + N)
        linarith [hs, hmax]
      rw [ha0]
      intro heq
      have hL0 : LSeries (LSeries.logMul^[k] F.coeff) s = 0 := by
        have h := iteratedDeriv_eq F k hs1
        rw [heq] at h
        exact (mul_eq_zero.mp h.symm).resolve_left (by simp)
      have hsum := summable_logMul_iterate F k hs1
      have hdecomp : LSeries (LSeries.logMul^[k] F.coeff) s =
          LSeries.term (LSeries.logMul^[k] F.coeff) s ℓ +
            ∑' n, Function.update (LSeries.term (LSeries.logMul^[k] F.coeff) s) ℓ 0 n := by
        have h := hsum.tsum_eq_add_tsum_ite ℓ
        have hupd : (fun n : ℕ ↦ if n = ℓ then (0:ℂ) else
            LSeries.term (LSeries.logMul^[k] F.coeff) s n) =
            Function.update (LSeries.term (LSeries.logMul^[k] F.coeff) s) ℓ 0 := by
          funext n
          by_cases hn : n = ℓ
          · subst hn; simp
          · simp only [hn, ite_false, Function.update_of_ne hn]
        rw [← hupd]
        exact h
      have hmain : ‖LSeries.term (LSeries.logMul^[k] F.coeff) s ℓ‖ =
          (Real.log ℓ) ^ k * ‖F.coeff ℓ‖ / (ℓ:ℝ) ^ s.re := by
        have hlog : ‖Complex.log ((ℓ:ℕ):ℂ)‖ = Real.log ℓ := by
          have h : Complex.log ((ℓ:ℕ):ℂ) = (Real.log ℓ : ℂ) :=
            (Complex.ofReal_log (show (0:ℝ) ≤ (ℓ:ℝ) by positivity)).symm
          rw [h]
          exact Complex.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ ℓ)))
        rw [LSeries.norm_term_eq]
        simp [show ℓ ≠ 0 by omega, logMul_iterate_apply, norm_pow, hlog]
      have hrem := norm_tsum_update_le F k hs1 hs3 hk C hC ℓ hℓ2 hmin
      have hlt : C * (Real.pi ^ 2 / 6) *
          (((ℓ + 1 : ℕ) : ℝ) ^ (s.re - (k:ℝ) - 3))⁻¹ <
          (Real.log ℓ) ^ k * ‖F.coeff ℓ‖ / (ℓ:ℝ) ^ s.re := by
        have hQpos : 0 < ((ℓ + 1 : ℕ) : ℝ) ^ (s.re - (k:ℝ) - 3) :=
          Real.rpow_pos_of_pos (by positivity) _
        have hLpos : 0 < (ℓ:ℝ) ^ s.re := Real.rpow_pos_of_pos (by positivity) _
        have hcast : ((ℓ + 1 : ℕ) : ℝ) = (ℓ:ℝ) + 1 := by push_cast; ring
        have hsplit : (ℓ:ℝ) ^ s.re = (ℓ:ℝ) ^ ((k:ℝ) + 3) * (ℓ:ℝ) ^ (s.re - (k:ℝ) - 3) := by
          rw [← Real.rpow_add (by positivity)]
          congr 1
          ring
        have hρrpow : ρ ^ (s.re - (k:ℝ) - 3) ≤ ρ ^ ((N:ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hρ0 (le_of_lt hρ1) hEN
        have hρN : ρ ^ ((N:ℝ)) = ρ ^ N := Real.rpow_natCast _ _
        have hkey : C * (Real.pi ^ 2 / 6) * (ℓ:ℝ) ^ ((k:ℝ) + 3) *
            ρ ^ (s.re - (k:ℝ) - 3) < (Real.log ℓ) ^ k * ‖F.coeff ℓ‖ := by
          have hle : C * (Real.pi ^ 2 / 6) * (ℓ:ℝ) ^ ((k:ℝ) + 3) *
              ρ ^ (s.re - (k:ℝ) - 3) ≤
              C * (Real.pi ^ 2 / 6) * (ℓ:ℝ) ^ ((k:ℝ) + 3) * ρ ^ N := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [← hρN]
            exact hρrpow
          have hN2 := (lt_div_iff₀ (by positivity :
              (0:ℝ) < C * (Real.pi ^ 2 / 6) * (ℓ:ℝ) ^ ((k:ℝ) + 3))).mp hN
          rw [mul_comm] at hN2
          exact hle.trans_lt hN2
        rw [lt_div_iff₀ hLpos, hcast]
        have hQ1pos : 0 < ((ℓ:ℝ) + 1) ^ (s.re - (k:ℝ) - 3) := by
          rw [← hcast]; exact hQpos
        have hρeq : ρ ^ (s.re - (k:ℝ) - 3) =
            (ℓ:ℝ) ^ (s.re - (k:ℝ) - 3) / ((ℓ:ℝ) + 1) ^ (s.re - (k:ℝ) - 3) := by
          rw [hρdef, Real.div_rpow (by positivity) (by positivity)]
        rw [hsplit]
        have hmul : C * (Real.pi ^ 2 / 6) * (((ℓ:ℝ) + 1) ^ (s.re - (k:ℝ) - 3))⁻¹ *
            ((ℓ:ℝ) ^ ((k:ℝ) + 3) * (ℓ:ℝ) ^ (s.re - (k:ℝ) - 3)) =
            C * (Real.pi ^ 2 / 6) * (ℓ:ℝ) ^ ((k:ℝ) + 3) * ρ ^ (s.re - (k:ℝ) - 3) := by
          rw [hρeq]
          field_simp
        rw [hmul]
        exact hkey
      rw [hL0] at hdecomp
      have hterm_eq : LSeries.term (LSeries.logMul^[k] F.coeff) s ℓ =
          -∑' n, Function.update (LSeries.term (LSeries.logMul^[k] F.coeff) s) ℓ 0 n := by
        rw [eq_neg_iff_add_eq_zero]
        exact hdecomp.symm
      rw [hterm_eq, norm_neg] at hmain
      rw [← hmain] at hlt
      exact absurd (hrem.trans_lt hlt) (lt_irrefl _)

end SelbergClassFunction

end

end MetaMathlibExt
