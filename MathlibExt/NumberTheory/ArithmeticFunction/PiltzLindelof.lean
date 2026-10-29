/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import MathlibExt.NumberTheory.ArithmeticFunction.KFoldDivisor
public import MathlibExt.NumberTheory.LSeries.LindelofHypothesis
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import MathlibExt.Analysis.Complex.TaylorRemainder
import MathlibExt.Analysis.Complex.VerticalIntegral.ContourShift
import MathlibExt.Analysis.Complex.VerticalIntegral.PerronKernel
import MathlibExt.NumberTheory.ArithmeticFunction.DivisorBounds
import MathlibExt.NumberTheory.LSeries.PerronError

/-!
# Summatory function of the Piltz divisor function, conditional on the Lindelöf hypothesis

Let `d_k = ArithmeticFunction.piltz k` be the `k`-fold divisor function. Its Dirichlet series
is `ζ(s) ^ k`. **Assuming the Lindelöf hypothesis** (`LindelofHypothesis`, an open conjecture),
a truncated Perron formula and a contour shift to the line `re s = 1 / 2` give
`∑_{n ≤ x} d_k(n) = x P_{k-1}(log x) + O(x ^ (1 / 2 + ε))` for every `ε > 0`. Here
`P_{k-1} = ArithmeticFunction.piltzMainPoly k` is an explicit real polynomial of degree `k - 1`
with leading coefficient `1 / (k - 1)!`: `x P_{k-1}(log x)` is the residue of
`ζ(s) ^ k x ^ s / s` at `s = 1`. The results that depend on the hypothesis take it as an explicit
argument `LindelofHypothesis`, and their names end in `_of_lindelofHypothesis`.

## Main statements

* `ArithmeticFunction.LSeriesSummable_piltz`, `ArithmeticFunction.LSeries_piltz`:
  `∑ d_k(n) n ^ (-s) = ζ(s) ^ k` for `re s > 1`.
* `ArithmeticFunction.piltz_le_sigma_zero_pow`: `d_k(n) ≤ d(n) ^ k`.
* `ArithmeticFunction.exists_piltz_le_mul_rpow`: `d_k(n) = O(n ^ δ)` for every `δ > 0`.
* `ArithmeticFunction.piltzMainPoly`: the main-term polynomial, with
  `ArithmeticFunction.piltzMainPoly_degree` and `ArithmeticFunction.piltzMainPoly_leadingCoeff`.
* `ArithmeticFunction.sum_piltz_sub_mul_piltzMainPoly_isBigO_of_lindelofHypothesis`,
  `ArithmeticFunction.exists_polynomial_sum_piltz_isBigO_of_lindelofHypothesis`: the asymptotic
  formula for `∑_{n ≤ x} d_k(n)`, **conditional on the Lindelöf hypothesis**.
-/

@[expose] public section

open Filter Asymptotics MeasureTheory

namespace ArithmeticFunction

/-- `d_k(n) ≤ d(n) ^ k`. -/
theorem piltz_le_sigma_zero_pow (k n : ℕ) : piltz k n ≤ sigma 0 n ^ k := by
  induction k generalizing n with
  | zero =>
    rw [piltz_zero, one_apply, pow_zero]
    split_ifs <;> omega
  | succ k ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [piltz_succ_apply, pow_succ']
    calc ∑ d ∈ n.divisors, piltz k d ≤ ∑ _d ∈ n.divisors, sigma 0 n ^ k := by
          refine Finset.sum_le_sum fun d hd => (ih d).trans (Nat.pow_le_pow_left ?_ k)
          rw [sigma_zero_apply, sigma_zero_apply]
          exact Finset.card_le_card (Nat.divisors_subset_of_dvd hn (Nat.dvd_of_mem_divisors hd))
      _ = sigma 0 n * sigma 0 n ^ k := by
          rw [Finset.sum_const, smul_eq_mul, sigma_zero_apply]

/-- **The divisor bound for `d_k`.** For every `δ > 0` there is `A > 0` with
`d_k(n) ≤ A * n ^ δ` for all `n`. -/
theorem exists_piltz_le_mul_rpow (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, (piltz k n : ℝ) ≤ A * (n : ℝ) ^ δ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, one_pos, fun n => ?_⟩
    rw [piltz_zero, one_apply, one_mul]
    split_ifs with h
    · simp [h]
    · simp only [Nat.cast_zero]; positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨C, hC0, hC⟩ := exists_sigma_zero_le_mul_rpow (ε := δ / k) (by positivity)
  refine ⟨C ^ k, by positivity, fun n => ?_⟩
  have h1 : (piltz k n : ℝ) ≤ (sigma 0 n : ℝ) ^ k := by exact_mod_cast piltz_le_sigma_zero_pow k n
  have h2 : (sigma 0 n : ℝ) ^ k ≤ (C * (n : ℝ) ^ (δ / k)) ^ k :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hC n) k
  have h3 : (C * (n : ℝ) ^ (δ / k)) ^ k = C ^ k * (n : ℝ) ^ δ := by
    rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (δ / k)) k,
      ← Real.rpow_mul (Nat.cast_nonneg n), div_mul_cancel₀ δ hk0.ne']
  linarith

private theorem LSeriesSummable_piltz_and_LSeries_piltz (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (piltz k n : ℂ)) s ∧
      LSeries (fun n : ℕ => (piltz k n : ℂ)) s = riemannZeta s ^ k := by
  have hdelta : (fun n : ℕ => (piltz 0 n : ℂ)) = LSeries.delta := by
    funext n
    rw [piltz_zero, one_apply]
    by_cases h : n = 1 <;> simp [h, LSeries.delta]
  have hconv : ∀ m : ℕ, (fun n : ℕ => (piltz (m + 1) n : ℂ))
      = LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => (piltz m n : ℂ)) := by
    intro m
    funext n
    rw [LSeries.convolution_def, piltz_succ_apply, Nat.cast_sum]
    dsimp only
    rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => (1 : ℕ → ℂ) a * (piltz m b : ℂ))]
    simp
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  induction k with
  | zero =>
      rw [hdelta]
      refine ⟨?_, ?_⟩
      · refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
        rw [LSeries.term_delta]
        simp only [Finset.mem_singleton] at hn
        simp [hn]
      · simpa using congrFun LSeries_delta s
  | succ m ih =>
      rw [hconv m]
      exact ⟨h1.convolution ih.1,
        by rw [LSeries_convolution' h1 ih.1, LSeries_one_eq_riemannZeta hs, ih.2, pow_succ']⟩

/-- The Dirichlet series of `d_k` converges absolutely for `re s > 1`. -/
theorem LSeriesSummable_piltz (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (piltz k n : ℂ)) s :=
  (LSeriesSummable_piltz_and_LSeries_piltz k hs).1

/-- `∑ d_k(n) n ^ (-s) = ζ(s) ^ k` for `re s > 1`. -/
theorem LSeries_piltz (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (piltz k n : ℂ)) s = riemannZeta s ^ k :=
  (LSeriesSummable_piltz_and_LSeries_piltz k hs).2

open Nat in
/-- The main-term polynomial of the Piltz divisor problem:
`P_{k-1}(y) = ∑_{j < k} c_j y ^ (k - 1 - j) / (k - 1 - j)!`, where `c_j = G^{(j)}(1) / j!` are the
Taylor coefficients at `s = 1` of the entire-near-`1` function `G(s) = ζ₁(s) ^ k / s`, and
`ζ₁(s) = (s - 1) ζ(s)` (`riemannZeta₁`). Equivalently, `x P_{k-1}(log x)` is the residue of
`ζ(s) ^ k x ^ s / s` at `s = 1`. (The coefficients `c_j` are real; the real part only serves to
land in `ℝ`.) -/
noncomputable def piltzMainPoly (k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range k, Polynomial.C
    ((iteratedDeriv j (fun s : ℂ => riemannZeta₁ s ^ k / s) 1 / (j ! : ℂ)).re
      / ((k - 1 - j)! : ℝ)) * Polynomial.X ^ (k - 1 - j)

open Nat in
private theorem piltzMainPoly_coeff_sub_one {k : ℕ} (hk : 1 ≤ k) :
    (piltzMainPoly k).coeff (k - 1) = 1 / ((k - 1)! : ℝ) := by
  rw [piltzMainPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
  · simp [riemannZeta₁_one]
  · intro j hj hj0
    have hj' := Finset.mem_range.mp hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- `P_{k-1}` has degree `k - 1`. -/
theorem piltzMainPoly_degree {k : ℕ} (hk : 1 ≤ k) :
    (piltzMainPoly k).degree = ((k - 1 : ℕ) : WithBot ℕ) := by
  refine Polynomial.degree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · refine Polynomial.degree_sum_le _ _ |>.trans (Finset.sup_le fun j hj => ?_)
    exact (Polynomial.degree_C_mul_X_pow_le _ _).trans
      (by exact_mod_cast (show k - 1 - j ≤ k - 1 by omega))
  · rw [piltzMainPoly_coeff_sub_one hk]
    exact one_div_ne_zero (by exact_mod_cast (k - 1).factorial_ne_zero)

/-- The leading coefficient of `P_{k-1}` is `1 / (k - 1)!`, since `ζ` has residue `1` at
`s = 1`. -/
theorem piltzMainPoly_leadingCoeff {k : ℕ} (hk : 1 ≤ k) :
    (piltzMainPoly k).leadingCoeff = 1 / ((k - 1).factorial : ℝ) := by
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some (piltzMainPoly_degree hk),
    piltzMainPoly_coeff_sub_one hk]

/-- **The summatory function of `d_k`, conditional on the Lindelöf hypothesis.** Assume the
Lindelöf hypothesis (`LindelofHypothesis`, an open conjecture). Let `k ≥ 1` and `ε > 0`. Then
`∑_{n ≤ x} d_k(n) = x * P_{k-1}(log x) + O(x ^ (1 / 2 + ε))`, where
`P_{k-1} = piltzMainPoly k` is the explicit polynomial of degree `k - 1` and leading coefficient
`1 / (k - 1)!` for which `x P_{k-1}(log x)` is the residue of `ζ(s) ^ k x ^ s / s` at `s = 1`. -/
theorem sum_piltz_sub_mul_piltzMainPoly_isBigO_of_lindelofHypothesis
    (hLindelof : LindelofHypothesis) {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℝ))
        - x * (piltzMainPoly k).eval (Real.log x)) =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε) := by
  classical
  have hgrowth : ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n →
      ‖(piltz k n : ℂ)‖ ≤ A * (n : ℝ) ^ δ := by
    intro δ hδ
    obtain ⟨A, hA0, hA⟩ := exists_piltz_le_mul_rpow k hδ
    exact ⟨A, hA0, fun n _ => by rw [Complex.norm_natCast]; exact hA n⟩
  -- ## The pole-free numerator `G (s) = (s - 1) ^ k ζ (s) ^ k / s` and its Taylor expansion
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ, G = fun s => riemannZeta₁ s ^ k / s := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Set ℂ, U = {s : ℂ | 1 / 2 ≤ s.re} := ⟨_, rfl⟩
  have hGd : ∀ s ∈ U, DifferentiableAt ℂ G s := by
    intro s hs
    rw [hUdef] at hs
    have hs' : 1 / 2 ≤ s.re := hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      norm_num at hs'
    rw [hGdef]
    exact ((differentiable_riemannZeta₁ s).pow k).div differentiableAt_id hs0
  have hU1 : U ∈ nhds (1 : ℂ) := by
    refine Filter.mem_of_superset ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)) fun s hs => ?_
    rw [hUdef]
    exact le_of_lt (show (1 / 2 : ℝ) < s.re from hs)
  obtain ⟨g, hg, hGg'⟩ := DifferentiableOn.eq_sum_iteratedDeriv_add_pow_mul
    (fun s hs => (hGd s hs).differentiableWithinAt) hU1 k
  obtain ⟨b, hbdef⟩ : ∃ b : ℕ → ℂ, b = fun j => iteratedDeriv j G 1 / (j.factorial : ℂ) :=
    ⟨_, rfl⟩
  have hGg : ∀ s ∈ U, G s = (∑ j ∈ Finset.range k, b j * (s - 1) ^ j) + (s - 1) ^ k * g s :=
    fun s _ => by rw [hbdef]; exact hGg' s
  -- ## The analytic core, at non-integral `x`
  have hcore : ∃ K : ℝ, ∀ x : ℝ, 1 < x → (∀ n : ℕ, (n : ℝ) ≠ x) →
      ‖(((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℝ)) : ℝ) : ℂ)
        - ∑ j ∈ Finset.range k,
            b j * ((x * Real.log x ^ (k - 1 - j) / ((k - 1 - j).factorial : ℝ) : ℝ) : ℂ)‖
        ≤ K * x ^ (1 / 2 + ε) := by
    -- ## Parameters: Lindelöf at `a / k`, truncated Perron at `c = 5 / 4`
    obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = min ε (1 / 2) := ⟨_, rfl⟩
    have ha0 : 0 < a := by rw [hadef]; exact lt_min hε (by norm_num)
    have haε : a ≤ ε := by rw [hadef]; exact min_le_left _ _
    have ha12 : a ≤ 1 / 2 := by rw [hadef]; exact min_le_right _ _
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    obtain ⟨A, hA0, hA⟩ := hLindelof (a / k) (by positivity)
    have hζk : ∀ s : ℂ, 1 / 2 ≤ s.re → 1 ≤ |s.im| →
        ‖riemannZeta s‖ ^ k ≤ A ^ k * |s.im| ^ a := by
      intro s h1 h2
      have ht0 : (0 : ℝ) ≤ |s.im| := abs_nonneg _
      calc ‖riemannZeta s‖ ^ k ≤ (A * |s.im| ^ (a / k)) ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) (hA s h1 h2) k
        _ = A ^ k * |s.im| ^ a := by
            rw [mul_pow, ← Real.rpow_natCast (|s.im| ^ (a / k)) k, ← Real.rpow_mul ht0,
              div_mul_cancel₀ a hk0.ne']
    obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, |t| ≤ 1 →
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B := by
      have hcont : ContinuousOn
          (fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
          (Set.Icc (-1) 1) := by
        intro t _
        have hne : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I ≠ 1 := by
          intro h
          have := congrArg Complex.re h
          norm_num at this
        exact (ContinuousAt.comp (f := fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)).continuousWithinAt
      obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
      refine ⟨max B 0, le_max_right _ _, fun t ht => ?_⟩
      exact (hB t (Set.mem_Icc.mpr (abs_le.mp ht))).trans (le_max_left _ _)
    obtain ⟨C, hC0, hC⟩ := LSeries.norm_sum_sub_truncated_perron_le
      (a := fun n => (piltz k n : ℂ)) (ε := 1 / 4) (by norm_num) hgrowth
      (5 / 4) (by norm_num)
    obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 4 * B ^ k + 2 * A ^ k := ⟨_, rfl⟩
    have hM0 : 0 ≤ M := by rw [hMdef]; positivity
    clear hgrowth hLindelof hA hGd hU1
    refine ⟨2 * C + 4 * M / a + 2 * A ^ k, fun x hx hxi => ?_⟩
    have hx0 : (0 : ℝ) < x := by linarith
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    -- ## The integrand, its principal part and its holomorphic part
    obtain ⟨Fp, hFp⟩ : ∃ Fp : ℂ → ℂ, Fp = fun s => riemannZeta s ^ k * (x : ℂ) ^ s / s :=
      ⟨_, rfl⟩
    obtain ⟨Kk, hKk⟩ : ∃ Kk : ℕ → ℂ → ℂ, Kk = fun m s => (x : ℂ) ^ s / (s - 1) ^ (m + 1) :=
      ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ℂ → ℂ, Q = fun s => ∑ j ∈ Finset.range k, b j * Kk (k - 1 - j) s :=
      ⟨_, rfl⟩
    obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ, D = fun s => g s * (x : ℂ) ^ s := ⟨_, rfl⟩
    have hFeq : ∀ s ∈ U, s ≠ 1 → Fp s = Q s + D s := by
      intro s hs hs1
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [hUdef] at hs
        norm_num at hs
      have hG := hGg s hs
      have hFG : Fp s = G s * (x : ℂ) ^ s / (s - 1) ^ k := by
        rw [hFp, hGdef]
        simp only
        rw [riemannZeta_eq_inv_sub_mul hs1, mul_pow, inv_pow]
        field_simp
      rw [hFG, hG, hQ, hD, add_mul, add_div, Finset.sum_mul, Finset.sum_div]
      simp only
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        have hp : (s - 1) ^ k = (s - 1) ^ j * (s - 1) ^ (k - 1 - j + 1) := by
          rw [← pow_add]; congr 1; omega
        rw [hKk, hp]
        field_simp
      · field_simp
    -- ## Regularity
    have hcpow : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
      fun s => differentiableAt_id.const_cpow (Or.inl hxC)
    have hKd : ∀ m : ℕ, ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ (Kk m) s := by
      intro m s hs
      rw [hKk]
      change DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s / (s - 1) ^ (m + 1)) s
      have hden : DifferentiableAt ℂ (fun s : ℂ => (s - 1) ^ (m + 1)) s := by fun_prop
      exact (hcpow s).div hden (pow_ne_zero _ (sub_ne_zero.mpr hs))
    have hQd : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ Q s := by
      intro s hs
      rw [hQ]
      have : DifferentiableAt ℂ (∑ j ∈ Finset.range k, fun s => b j * Kk (k - 1 - j) s) s :=
        DifferentiableAt.sum fun j _ => (hKd _ s hs).const_mul _
      convert this using 1
      funext s
      simp
    have hDd : DifferentiableOn ℂ D U := by
      rw [hD]
      exact hg.mul fun s _ => (hcpow s).differentiableWithinAt
    -- ## The four-sided rectangle functional on `[1/2, 5/4] × [-T, T]`
    obtain ⟨Rect, hRect⟩ : ∃ Rect : (ℂ → ℂ) → ℝ → ℂ, Rect = fun f T =>
        (∫ σ in (1 / 2 : ℝ)..(5 / 4), f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
          - (∫ σ in (1 / 2 : ℝ)..(5 / 4), f ((σ : ℂ) + (T : ℂ) * Complex.I))
          + Complex.I • (∫ y in (-T)..T, f (((5 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
          - Complex.I • (∫ y in (-T)..T, f (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) :=
      ⟨_, rfl⟩
    have hmemU : ∀ s : ℂ, 1 / 2 ≤ s.re → s ∈ U := fun s h => by rw [hUdef]; exact h
    have hRD : ∀ T : ℝ, 0 < T → Rect D T = 0 := by
      intro T hT
      rw [hRect]
      refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn D ⟨1 / 2, -T⟩ ⟨5 / 4, T⟩
        (hDd.mono fun s hs => ?_)
      obtain ⟨h1, -⟩ := hs
      change s.re ∈ Set.uIcc (1 / 2 : ℝ) (5 / 4) at h1
      rw [Set.uIcc_of_le (by norm_num)] at h1
      exact hmemU s h1.1
    have hside : ∀ (a c : ℝ) (φ : ℝ → ℂ), ContinuousOn φ (Set.uIcc a c) →
        (∀ v ∈ Set.uIcc a c, φ v ∈ U) → (∀ v ∈ Set.uIcc a c, φ v ≠ 1) →
        (∫ v in a..c, Fp (φ v)) = (∫ v in a..c, Q (φ v)) + ∫ v in a..c, D (φ v) := by
      intro a c φ hφ hmem hne
      have hQi : IntervalIntegrable (fun v => Q (φ v)) volume a c :=
        (ContinuousOn.comp (t := {s | s ≠ 1})
          (fun s hs => (hQd s hs).continuousAt.continuousWithinAt) hφ
          (fun v hv => hne v hv)).intervalIntegrable
      have hDi : IntervalIntegrable (fun v => D (φ v)) volume a c :=
        (ContinuousOn.comp hDd.continuousOn hφ (fun v hv => hmem v hv)).intervalIntegrable
      rw [← intervalIntegral.integral_add hQi hDi]
      exact intervalIntegral.integral_congr fun v hv => hFeq _ (hmem v hv) (hne v hv)
    have hRF : ∀ T : ℝ, 0 < T → Rect Fp T = Rect Q T + Rect D T := by
      intro T hT
      have hre : ∀ v ∈ Set.uIcc (1 / 2 : ℝ) (5 / 4), 1 / 2 ≤ v := by
        intro v hv
        rw [Set.uIcc_of_le (by norm_num)] at hv
        exact hv.1
      have e1 := hside (1 / 2) (5 / 4) (fun σ : ℝ => (σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        (by fun_prop) (fun v hv => hmemU _ (by simpa using hre v hv))
        (fun v _ h => by
          have := congrArg Complex.im h
          simp at this
          linarith)
      have e2 := hside (1 / 2) (5 / 4) (fun σ : ℝ => (σ : ℂ) + (T : ℂ) * Complex.I)
        (by fun_prop) (fun v hv => hmemU _ (by simpa using hre v hv))
        (fun v _ h => by
          have := congrArg Complex.im h
          simp at this
          linarith)
      have e3 := hside (-T) T (fun y : ℝ => ((5 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        (by fun_prop) (fun v _ => hmemU _ (by norm_num))
        (fun v _ h => by
          have := congrArg Complex.re h
          norm_num at this)
      have e4 := hside (-T) T (fun y : ℝ => ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
        (by fun_prop) (fun v _ => hmemU _ (by norm_num))
        (fun v _ h => by
          have := congrArg Complex.re h
          norm_num at this)
      rw [hRect]
      simp only at e1 e2 e3 e4 ⊢
      rw [e1, e2, e3, e4]
      simp only [smul_add]
      ring
    -- ## The main term `Mn` and the line integrals of `Q`
    obtain ⟨Mn, hMn⟩ : ∃ Mn : ℂ, Mn = ∑ j ∈ Finset.range k,
        b j * ((x * Real.log x ^ (k - 1 - j) / ((k - 1 - j).factorial : ℝ) : ℝ) : ℂ) :=
      ⟨_, rfl⟩
    rw [← hMn]
    have hKline : ∀ m : ℕ, ∀ c : ℝ, c ≠ 1 →
        Continuous fun t : ℝ => Kk m ((c : ℂ) + (t : ℂ) * Complex.I) := by
      intro m c hc
      refine continuous_iff_continuousAt.mpr fun t => ?_
      refine (hKd m _ fun h => hc ?_).continuousAt.comp (by fun_prop : Continuous
        fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I).continuousAt
      have := congrArg Complex.re h
      simpa using this
    have hQline : ∀ c : ℝ, c ≠ 1 →
        Continuous fun t : ℝ => Q ((c : ℂ) + (t : ℂ) * Complex.I) := by
      intro c hc
      refine continuous_iff_continuousAt.mpr fun t => ?_
      refine (hQd _ fun h => hc ?_).continuousAt.comp (by fun_prop : Continuous
        fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I).continuousAt
      have := congrArg Complex.re h
      simpa using this
    have hM4 : ∀ j : ℕ, Tendsto (fun T : ℝ => (1 / (2 * Real.pi)) • ∫ t in (-T)..T,
        Kk (k - 1 - j) (((5 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop
        (nhds ((x * Real.log x ^ (k - 1 - j) / ((k - 1 - j).factorial : ℝ) : ℝ) : ℂ)) := by
      intro j
      have h := Complex.hasVerticalIntegral_cpow_div_sub_one_pow_succ (k := k - 1 - j) hx
        (c := 5 / 4) (by norm_num)
      have hv : (x : ℂ) * (Real.log x : ℂ) ^ (k - 1 - j) / ((k - 1 - j).factorial : ℂ)
          = ((x * Real.log x ^ (k - 1 - j) / ((k - 1 - j).factorial : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hv] at h
      rw [hKk]
      exact h.tendsto
    have hQc : Complex.HasVerticalIntegral (5 / 4) Q Mn := by
      rw [hQ, hMn]
      exact Complex.HasVerticalIntegral.finset_sum (Finset.range k)
        (f := fun j s => b j * Kk (k - 1 - j) s)
        fun j _ => Complex.HasVerticalIntegral.const_mul (Complex.hasVerticalIntegral_of_continuous
          (hKline (k - 1 - j) (5 / 4) (by norm_num)) (hM4 j)) (b j)
    -- on `Re s = 1 / 2` the kernels reflect to Perron kernels with base `1 / x < 1`
    have hq : ∀ m : ℕ, Tendsto (fun T : ℝ => (1 / (2 * Real.pi)) • ∫ t in (-T)..T,
        ((x⁻¹ : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)) atTop (nhds 0) := by
      intro m
      rcases m with _ | m
      · have hδ : PerronKernel.perronStep x⁻¹ = 0 :=
          PerronKernel.perronStep_of_lt_one (inv_lt_one_of_one_lt₀ hx)
        simp only [zero_add, pow_one]
        refine squeeze_zero_norm'
          (a := fun T => x⁻¹ ^ (1 / 2 : ℝ) / |Real.log x⁻¹| / T) ?_
          (tendsto_const_nhds.div_atTop tendsto_id)
        filter_upwards [eventually_gt_atTop 0] with T hT
        have h := PerronKernel.norm_truncated_sub_perronStep_lt (x := x⁻¹) (c := 1 / 2)
          (R := T) (by positivity) (inv_lt_one_of_one_lt₀ hx).ne (by norm_num) hT
        rw [hδ, Complex.ofReal_zero, sub_zero] at h
        refine h.le.trans ?_
        calc x⁻¹ ^ (1 / 2 : ℝ) * min 1 (1 / (T * |Real.log x⁻¹|))
            ≤ x⁻¹ ^ (1 / 2 : ℝ) * (1 / (T * |Real.log x⁻¹|)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
          _ = x⁻¹ ^ (1 / 2 : ℝ) / |Real.log x⁻¹| / T := by ring
      · exact Complex.hasVerticalIntegral_cpow_div_pow_succ_of_le_one (k := m + 1) (by omega)
          (by norm_num) (by positivity) (inv_le_one_of_one_le₀ hx.le) |>.tendsto
    have harg : (x : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hx0.le]
      exact hpi.ne
    have hrefl : ∀ (m : ℕ) (T : ℝ),
        (∫ t in (-T)..T, Kk m (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
          = (x : ℂ) * (-1) ^ (m + 1) * ∫ t in (-T)..T,
            ((x⁻¹ : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              / (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1) := by
      intro m T
      have hpt : ∀ t : ℝ, Kk m (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          = (x : ℂ) * (-1) ^ (m + 1) * (fun t : ℝ =>
            ((x⁻¹ : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              / (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)) (-t) := by
        intro t
        simp only
        set w : ℂ := ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I with hw
        have hw1 : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I - 1 = -w := by
          rw [hw]; push_cast; ring
        have e : (x : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = x * ((x : ℂ) ^ w)⁻¹ := by
          have h := Complex.cpow_add (x := (x : ℂ)) 1 (-w) hxC
          rw [Complex.cpow_one, Complex.cpow_neg] at h
          rw [← h]
          congr 1
          rw [hw]; push_cast; ring
        have hinv : ((x⁻¹ : ℝ) : ℂ) ^ w = ((x : ℂ) ^ w)⁻¹ := by
          rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg]
        have hm : ((-1 : ℂ) ^ (m + 1))⁻¹ = (-1) ^ (m + 1) := by
          rw [← inv_pow, inv_neg, inv_one]
        rw [hKk]
        simp only
        rw [hw1, neg_pow, e, hinv, div_eq_mul_inv, mul_inv, hm]
        ring
      rw [intervalIntegral.integral_congr fun t _ => hpt t, intervalIntegral.integral_const_mul]
      congr 1
      have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) (fun t : ℝ =>
        ((x⁻¹ : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1))
      rw [neg_neg] at h
      exact h
    have hKhalf : ∀ m : ℕ, Tendsto (fun T : ℝ => (1 / (2 * Real.pi)) • ∫ t in (-T)..T,
        Kk m (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := by
      intro m
      have h := (hq m).const_mul ((x : ℂ) * (-1) ^ (m + 1))
      rw [mul_zero] at h
      refine h.congr fun T => ?_
      rw [hrefl, Complex.real_smul, Complex.real_smul]
      ring
    have hQh : Complex.HasVerticalIntegral (1 / 2) Q 0 := by
      have h := Complex.HasVerticalIntegral.finset_sum (Finset.range k) (c := 1 / 2)
        (f := fun j s => b j * Kk (k - 1 - j) s) (v := fun _ => 0)
        fun j _ => by
          simpa using Complex.HasVerticalIntegral.const_mul
            (Complex.hasVerticalIntegral_of_continuous
              (hKline (k - 1 - j) (1 / 2) (by norm_num)) (hKhalf (k - 1 - j))) (b j)
      rw [hQ]
      simpa using h
    -- the horizontal sides of `Q` vanish as `T → ∞`
    have hKb : ∀ m : ℕ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 5 / 4 → 1 ≤ |s.im| →
        ‖Kk m s‖ ≤ x ^ (5 / 4 : ℝ) / |s.im| := by
      intro m s h1 h2 h3
      have hu : (0 : ℝ) < |s.im| := by linarith
      have hn : |s.im| ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        simpa using this
      have hn' : |s.im| ≤ ‖s - 1‖ ^ (m + 1) := by
        calc |s.im| ≤ |s.im| ^ (m + 1) := le_self_pow₀ h3 (by omega)
          _ ≤ ‖s - 1‖ ^ (m + 1) := pow_le_pow_left₀ hu.le hn _
      rw [hKk]
      simp only
      rw [norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      exact div_le_div₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hx.le h2) hu hn'
    have hHq := Complex.tendsto_horizontal_sides_of_norm_le_div_abs_im (f := Q) (a := 1 / 2)
      (b := 5 / 4)
      (M := (∑ j ∈ Finset.range k, ‖b j‖) * x ^ (5 / 4 : ℝ)) (by norm_num) fun s h1 h2 h3 => by
      rw [hQ]
      simp only
      calc ‖∑ j ∈ Finset.range k, b j * Kk (k - 1 - j) s‖
          ≤ ∑ j ∈ Finset.range k, ‖b j‖ * (x ^ (5 / 4 : ℝ) / |s.im|) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hKb _ s h1 h2 h3) (norm_nonneg _)
        _ = (∑ j ∈ Finset.range k, ‖b j‖) * x ^ (5 / 4 : ℝ) / |s.im| := by
            rw [← Finset.sum_mul]; ring
    have hlimQ : Tendsto (fun T : ℝ => Rect Q T) atTop
        (nhds (2 * (Real.pi : ℂ) * Complex.I * Mn)) := by
      have h1 : Tendsto (fun T : ℝ => (1 / (2 * Real.pi)) • ∫ t in (-T)..T,
          Q (((5 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds Mn) := hQc.tendsto
      have h2 : Tendsto (fun T : ℝ => (1 / (2 * Real.pi)) • ∫ t in (-T)..T,
          Q (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := hQh.tendsto
      have h := (hHq.add (h1.const_mul (2 * (Real.pi : ℂ) * Complex.I))).sub
        (h2.const_mul (2 * (Real.pi : ℂ) * Complex.I))
      simp only [zero_add, mul_zero, sub_zero] at h
      refine h.congr fun T => ?_
      rw [hRect]
      simp only [Complex.real_smul, smul_eq_mul]
      have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
      push_cast
      field_simp
    -- the rectangle integral of `Q` does not depend on the height
    have hRQconst : ∀ R T : ℝ, 1 ≤ R → R ≤ T → Rect Q R = Rect Q T := by
      intro R T hR hRT
      have top : (∫ σ in (1 / 2 : ℝ)..(5 / 4), Q ((σ : ℂ) + (R : ℂ) * Complex.I))
          - (∫ σ in (1 / 2 : ℝ)..(5 / 4), Q ((σ : ℂ) + (T : ℂ) * Complex.I))
          + Complex.I • (∫ y in R..T, Q (((5 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
          - Complex.I • (∫ y in R..T, Q (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
        refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn Q ⟨1 / 2, R⟩ ⟨5 / 4, T⟩
          fun s hs => (hQd s fun h => ?_).differentiableWithinAt
        obtain ⟨-, h2⟩ := hs
        change s.im ∈ Set.uIcc R T at h2
        rw [Set.uIcc_of_le hRT] at h2
        rw [h] at h2
        simp at h2
        linarith [h2.1]
      have bot : (∫ σ in (1 / 2 : ℝ)..(5 / 4), Q ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
          - (∫ σ in (1 / 2 : ℝ)..(5 / 4), Q ((σ : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
          + Complex.I • (∫ y in (-T)..(-R), Q (((5 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
          - Complex.I • (∫ y in (-T)..(-R), Q (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
          = 0 := by
        refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn Q ⟨1 / 2, -T⟩
          ⟨5 / 4, -R⟩ fun s hs => (hQd s fun h => ?_).differentiableWithinAt
        obtain ⟨-, h2⟩ := hs
        change s.im ∈ Set.uIcc (-T) (-R) at h2
        rw [Set.uIcc_of_le (by linarith)] at h2
        rw [h] at h2
        simp at h2
        linarith [h2.2]
      have hsplit : ∀ c : ℝ, c ≠ 1 →
          (∫ y in (-T)..T, Q ((c : ℂ) + (y : ℂ) * Complex.I))
            = (∫ y in (-T)..(-R), Q ((c : ℂ) + (y : ℂ) * Complex.I))
              + (∫ y in (-R)..R, Q ((c : ℂ) + (y : ℂ) * Complex.I))
              + ∫ y in R..T, Q ((c : ℂ) + (y : ℂ) * Complex.I) := by
        intro c hc
        have hi : ∀ u v : ℝ, IntervalIntegrable
            (fun y : ℝ => Q ((c : ℂ) + (y : ℂ) * Complex.I)) volume u v :=
          fun u v => (hQline c hc).intervalIntegrable u v
        rw [intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _),
          intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)]
      rw [hRect]
      simp only
      rw [hsplit (5 / 4) (by norm_num), hsplit (1 / 2) (by norm_num)]
      simp only [smul_add] at top bot ⊢
      push_cast at top bot ⊢
      linear_combination -top - bot
    have hRQ : Rect Q x = 2 * (Real.pi : ℂ) * Complex.I * Mn := by
      refine tendsto_nhds_unique ?_ hlimQ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop x] with T hT
      exact hRQconst x T hx.le hT
    -- ## The rectangle identity at height `R = x`
    have hRFx := hRF x hx0
    rw [hRD x hx0, hRQ, add_zero, hRect] at hRFx
    simp only [smul_eq_mul] at hRFx
    obtain ⟨Vr, hVr⟩ : ∃ V : ℂ, V = ∫ y in (-x)..x,
        Fp (((5 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := ⟨_, rfl⟩
    obtain ⟨Vl, hVl⟩ : ∃ V : ℂ, V = ∫ y in (-x)..x,
        Fp (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := ⟨_, rfl⟩
    obtain ⟨Hm, hHm⟩ : ∃ V : ℂ, V = ∫ σ in (1 / 2 : ℝ)..(5 / 4),
        Fp ((σ : ℂ) + ((-x : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
    obtain ⟨Hp, hHp⟩ : ∃ V : ℂ, V = ∫ σ in (1 / 2 : ℝ)..(5 / 4),
        Fp ((σ : ℂ) + (x : ℂ) * Complex.I) := ⟨_, rfl⟩
    rw [← hVr, ← hVl, ← hHm, ← hHp] at hRFx
    have hVr' : Vr = 2 * (Real.pi : ℂ) * Mn + Vl + Complex.I * (Hm - Hp) := by
      linear_combination (-Complex.I) * hRFx + (Vr - Vl - 2 * (Real.pi : ℂ) * Mn) * Complex.I_sq
    have hid : (1 / (2 * Real.pi)) • Vr - Mn
        = ((1 / (2 * Real.pi) : ℝ) : ℂ) * (Vl + Complex.I * (Hm - Hp)) := by
      have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
      rw [hVr', Complex.real_smul]
      push_cast
      field_simp
      ring
    -- ## The truncated Perron formula at `c = 5 / 4`, `R = x`
    have hperron := hC x x hx.le le_rfl hxi
    have hint : (∫ t in (-x)..x,
        LSeries (fun n => (piltz k n : ℂ)) (((5 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          (x : ℂ) ^ (((5 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
            (((5 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) = Vr := by
      rw [hVr]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [LSeries_piltz k (by simp; norm_num), hFp]
    rw [hint] at hperron
    have hS : (((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℝ)) : ℝ) : ℂ)
        = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℂ) := by
      push_cast; rfl
    rw [hS]
    clear hS hint hRFx hVr' hVr hRQ hRQconst hlimQ hHq hKb hQh hKhalf hrefl harg hq hQc hM4
      hQline hKline hMn hRF hside hRD hRect hmemU hDd hQd hKd hcpow hFeq hD hQ hKk hC
      hGg hGg' hg hUdef hGdef hbdef
    -- ## Real-variable facts
    have hxe : ∀ e : ℝ, e ≤ 1 / 2 + ε → x ^ e ≤ x ^ (1 / 2 + ε) :=
      fun e he => Real.rpow_le_rpow_of_exponent_le hx.le he
    have hlogx : Real.log x ≤ x := by
      have := Real.log_le_sub_one_of_pos hx0; linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
    have hP1 : C * (x ^ (5 / 4 + 1 / 4 : ℝ) / x + x ^ (1 / 4 : ℝ) * Real.log x / x)
        ≤ 2 * C * x ^ (1 / 2 + ε) := by
      have e1 : x ^ (5 / 4 + 1 / 4 : ℝ) / x = x ^ (1 / 2 : ℝ) := by
        rw [show (5 / 4 + 1 / 4 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]
        field_simp
      have e2 : x ^ (1 / 4 : ℝ) * Real.log x / x ≤ x ^ (1 / 4 : ℝ) := by
        rw [div_le_iff₀ hx0]
        exact mul_le_mul_of_nonneg_left hlogx (by positivity)
      have e3 := hxe (1 / 2) (by linarith)
      have e4 := hxe (1 / 4) (by linarith)
      rw [e1]
      have h5 : x ^ (1 / 2 : ℝ) + x ^ (1 / 4 : ℝ) * Real.log x / x ≤ 2 * x ^ (1 / 2 + ε) := by
        linarith
      calc C * (x ^ (1 / 2 : ℝ) + x ^ (1 / 4 : ℝ) * Real.log x / x)
          ≤ C * (2 * x ^ (1 / 2 + ε)) := mul_le_mul_of_nonneg_left h5 hC0.le
        _ = 2 * C * x ^ (1 / 2 + ε) := by ring
    -- ## The horizontal sides
    have hHbound : ∀ τ : ℝ, |τ| = x →
        ‖∫ σ in (1 / 2 : ℝ)..(5 / 4), Fp ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
          ≤ A ^ k * x ^ (1 / 2 + ε) := by
      intro τ hτ
      have hpt : ∀ σ ∈ Set.uIoc (1 / 2 : ℝ) (5 / 4),
          ‖Fp ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ A ^ k * x ^ (a + 1 / 4) := by
        intro σ hσ
        rw [Set.uIoc_of_le (by norm_num)] at hσ
        obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (σ : ℂ) + (τ : ℂ) * Complex.I := ⟨_, rfl⟩
        rw [← hs]
        have hre : s.re = σ := by simp [hs]
        have him : s.im = τ := by simp [hs]
        have hz := hζk s (by rw [hre]; linarith [hσ.1]) (by rw [him, hτ]; exact hx.le)
        rw [him, hτ] at hz
        have hns : x ≤ ‖s‖ := by
          have := Complex.abs_im_le_norm s
          rw [him, hτ] at this
          exact this
        rw [hFp]
        simp only
        rw [norm_div, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
        have hxs : x ^ σ ≤ x ^ (5 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le hσ.2
        have heq : A ^ k * x ^ a * x ^ (5 / 4 : ℝ) / x = A ^ k * x ^ (a + 1 / 4) := by
          rw [show (5 / 4 : ℝ) = 1 / 4 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one,
            Real.rpow_add hx0]
          field_simp
        rw [← heq]
        exact div_le_div₀ (by positivity)
          (mul_le_mul hz hxs (by positivity) (by positivity)) hx0 hns
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      have hle := hxe (a + 1 / 4) (by linarith)
      refine h.trans ?_
      rw [show |(5 / 4 : ℝ) - 1 / 2| = 3 / 4 by norm_num]
      have h0 : 0 ≤ A ^ k * x ^ (a + 1 / 4) := by positivity
      have h1 := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ A ^ k)
      linarith
    -- ## The left line
    have hVlb : ‖Vl‖ ≤ 4 * M / a * x ^ (1 / 2 + ε) := by
      have hcontm : Continuous fun t : ℝ => (1 + |t|) ^ (a - 1) :=
        Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity)
      have h2a : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (a - 1) := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith : (-1 : ℝ) ≤ a - 1)
        rw [Real.rpow_neg_one] at h
        linarith
      have hBk : 0 ≤ B ^ k := by positivity
      have hAk : 0 ≤ A ^ k := by positivity
      have hpt : ∀ t : ℝ, ‖Fp (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ x ^ (1 / 2 : ℝ) * (M * (1 + |t|) ^ (a - 1)) := by
        intro t
        obtain ⟨s, hs⟩ : ∃ s : ℂ, s = ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := ⟨_, rfl⟩
        rw [← hs]
        have hre : s.re = 1 / 2 := by simp [hs]
        have him : s.im = t := by simp [hs]
        have hm0 : 0 ≤ (1 + |t|) ^ (a - 1) := by positivity
        rw [hFp]
        simp only
        rw [norm_div, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
        have hxh : 0 < x ^ (1 / 2 : ℝ) := by positivity
        by_cases ht : |t| ≤ 1
        · have hz : ‖riemannZeta s‖ ^ k ≤ B ^ k := by
            rw [hs]; exact pow_le_pow_left₀ (norm_nonneg _) (hB t ht) k
          have hns : 1 / 2 ≤ ‖s‖ := by
            have := Complex.abs_re_le_norm s
            rw [hre] at this
            norm_num at this ⊢
            linarith
          have hm : (1 / 2 : ℝ) ≤ (1 + |t|) ^ (a - 1) :=
            h2a.trans (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith))
          have hkey : B ^ k / (1 / 2) ≤ M * (1 + |t|) ^ (a - 1) := by
            rw [hMdef]
            have h1 := mul_le_mul_of_nonneg_left hm hBk
            have h2 := mul_nonneg hAk hm0
            linarith
          calc ‖riemannZeta s‖ ^ k * x ^ (1 / 2 : ℝ) / ‖s‖
              ≤ B ^ k * x ^ (1 / 2 : ℝ) / (1 / 2) :=
                div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hz hxh.le)
                  (by norm_num) hns
            _ = x ^ (1 / 2 : ℝ) * (B ^ k / (1 / 2)) := by ring
            _ ≤ x ^ (1 / 2 : ℝ) * (M * (1 + |t|) ^ (a - 1)) :=
                mul_le_mul_of_nonneg_left hkey hxh.le
        · rw [not_le] at ht
          have ht1 : 1 ≤ |t| := ht.le
          have hz := hζk s (by rw [hre]) (by rw [him]; exact ht1)
          rw [him] at hz
          have hns : |t| ≤ ‖s‖ := by
            have := Complex.abs_im_le_norm s
            rwa [him] at this
          have htpos : 0 < |t| := by linarith
          have hdiv : |t| ^ a / |t| = |t| ^ (a - 1) := by
            rw [Real.rpow_sub_one htpos.ne']
          have hcmp : |t| ^ (a - 1) ≤ 2 * (1 + |t|) ^ (a - 1) := by
            have h1 : |t| ^ (a - 1) ≤ ((1 + |t|) / 2) ^ (a - 1) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
            rw [Real.div_rpow (by positivity) (by norm_num)] at h1
            have h2 : (1 + |t|) ^ (a - 1) / 2 ^ (a - 1) ≤ 2 * (1 + |t|) ^ (a - 1) := by
              rw [div_le_iff₀ (by positivity)]
              have h3 := mul_le_mul_of_nonneg_left h2a hm0
              linarith
            linarith
          calc ‖riemannZeta s‖ ^ k * x ^ (1 / 2 : ℝ) / ‖s‖
              ≤ A ^ k * |t| ^ a * x ^ (1 / 2 : ℝ) / |t| :=
                div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hz hxh.le) htpos hns
            _ = x ^ (1 / 2 : ℝ) * (A ^ k * (|t| ^ a / |t|)) := by ring
            _ ≤ x ^ (1 / 2 : ℝ) * (M * (1 + |t|) ^ (a - 1)) := by
                rw [hdiv]
                refine mul_le_mul_of_nonneg_left ?_ hxh.le
                rw [hMdef]
                have h1 := mul_le_mul_of_nonneg_left hcmp hAk
                have h2 := mul_nonneg hBk hm0
                linarith
      have hi : ∀ u v : ℝ, IntervalIntegrable (fun t : ℝ => (1 + |t|) ^ (a - 1))
          volume u v := fun u v => hcontm.intervalIntegrable u v
      have hpos : (∫ t in (0 : ℝ)..x, (1 + |t|) ^ (a - 1)) = ((1 + x) ^ a - 1) / a := by
        have e1 : (∫ t in (0 : ℝ)..x, (1 + |t|) ^ (a - 1))
            = ∫ t in (0 : ℝ)..x, (1 + t) ^ (a - 1) := by
          refine intervalIntegral.integral_congr fun t ht => ?_
          rw [Set.uIcc_of_le hx0.le] at ht
          simp only [abs_of_nonneg ht.1]
        have e2 := intervalIntegral.integral_comp_add_left (a := 0) (b := x)
          (fun u : ℝ => u ^ (a - 1)) (1 : ℝ)
        simp only [add_zero] at e2
        rw [e1, e2, integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.one_rpow]
      have hneg : (∫ t in (-x)..0, (1 + |t|) ^ (a - 1))
          = ∫ t in (0 : ℝ)..x, (1 + |t|) ^ (a - 1) := by
        have h := intervalIntegral.integral_comp_neg (a := 0) (b := x)
          (fun t : ℝ => (1 + |t|) ^ (a - 1))
        simp only [abs_neg, neg_zero] at h
        exact h.symm
      have hJ : (∫ t in (-x)..x, (1 + |t|) ^ (a - 1)) = 2 * (((1 + x) ^ a - 1) / a) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-x) 0) (hi 0 x), hneg, hpos]
        ring
      have hJle : 2 * (((1 + x) ^ a - 1) / a) ≤ 4 * x ^ a / a := by
        have h1 : (1 + x) ^ a ≤ (2 * x) ^ a :=
          Real.rpow_le_rpow (by positivity) (by linarith) ha0.le
        rw [Real.mul_rpow (by norm_num) hx0.le] at h1
        have h2 : (2 : ℝ) ^ a ≤ 2 := by
          have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith : a ≤ 1)
          rwa [Real.rpow_one] at this
        have hxa : 0 ≤ x ^ a := by positivity
        have h3 : 2 * ((1 + x) ^ a - 1) ≤ 4 * x ^ a := by
          have := mul_le_mul_of_nonneg_right h2 hxa
          linarith
        rw [mul_div_assoc']
        exact div_le_div_of_nonneg_right h3 ha0.le
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
        (by linarith : -x ≤ x) (Filter.Eventually.of_forall fun t _ => hpt t)
        (((hcontm.const_mul M).const_mul (x ^ (1 / 2 : ℝ))).intervalIntegrable (-x) x)
      rw [hVl]
      refine hnorm.trans ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hJ]
      have hxa' : x ^ (1 / 2 : ℝ) * x ^ a ≤ x ^ (1 / 2 + ε) := by
        rw [← Real.rpow_add hx0]; exact hxe _ (by linarith)
      calc x ^ (1 / 2 : ℝ) * (M * (2 * (((1 + x) ^ a - 1) / a)))
          ≤ x ^ (1 / 2 : ℝ) * (M * (4 * x ^ a / a)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJle hM0) (by positivity)
        _ = 4 * M / a * (x ^ (1 / 2 : ℝ) * x ^ a) := by ring
        _ ≤ 4 * M / a * x ^ (1 / 2 + ε) :=
            mul_le_mul_of_nonneg_left hxa' (div_nonneg (by linarith) ha0.le)
    -- ## Assembly
    have hHm' : ‖Hm‖ ≤ A ^ k * x ^ (1 / 2 + ε) := by
      rw [hHm]; exact hHbound (-x) (by rw [abs_neg, abs_of_pos hx0])
    have hHp' : ‖Hp‖ ≤ A ^ k * x ^ (1 / 2 + ε) := by
      rw [hHp]; exact hHbound x (abs_of_pos hx0)
    have hsecond : ‖(1 / (2 * Real.pi)) • Vr - Mn‖ ≤ ‖Vl‖ + ‖Hm‖ + ‖Hp‖ := by
      rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have hr : 1 / (2 * Real.pi) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
      have h1 : ‖Vl + Complex.I * (Hm - Hp)‖ ≤ ‖Vl‖ + ‖Hm‖ + ‖Hp‖ := by
        calc ‖Vl + Complex.I * (Hm - Hp)‖ ≤ ‖Vl‖ + ‖Complex.I * (Hm - Hp)‖ := norm_add_le _ _
          _ = ‖Vl‖ + ‖Hm - Hp‖ := by rw [norm_mul, Complex.norm_I, one_mul]
          _ ≤ ‖Vl‖ + (‖Hm‖ + ‖Hp‖) := by gcongr; exact norm_sub_le _ _
          _ = ‖Vl‖ + ‖Hm‖ + ‖Hp‖ := by ring
      have h0 : 0 ≤ ‖Vl + Complex.I * (Hm - Hp)‖ := norm_nonneg _
      calc 1 / (2 * Real.pi) * ‖Vl + Complex.I * (Hm - Hp)‖
          ≤ 1 * ‖Vl + Complex.I * (Hm - Hp)‖ := mul_le_mul_of_nonneg_right hr h0
        _ ≤ ‖Vl‖ + ‖Hm‖ + ‖Hp‖ := by rw [one_mul]; exact h1
    calc ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℂ)) - Mn‖
        ≤ ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℂ))
            - (1 / (2 * Real.pi)) • Vr‖ + ‖(1 / (2 * Real.pi)) • Vr - Mn‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * C * x ^ (1 / 2 + ε) + (4 * M / a * x ^ (1 / 2 + ε)
            + A ^ k * x ^ (1 / 2 + ε) + A ^ k * x ^ (1 / 2 + ε)) := by
          refine add_le_add (hperron.trans hP1) (hsecond.trans ?_)
          exact add_le_add (add_le_add hVlb hHm') hHp'
      _ = (2 * C + 4 * M / a + 2 * A ^ k) * x ^ (1 / 2 + ε) := by ring
  -- ## The polynomial and the real part
  obtain ⟨K, hK⟩ := hcore
  set P : Polynomial ℝ := piltzMainPoly k with hP
  have hPev : ∀ y : ℝ, P.eval y = ∑ j ∈ Finset.range k,
      (b j).re * y ^ (k - 1 - j) / ((k - 1 - j).factorial : ℝ) := by
    intro y
    rw [hP, piltzMainPoly, Polynomial.eval_finsetSum, hbdef, hGdef]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  have hreal : ∀ x : ℝ, 1 < x → (∀ n : ℕ, (n : ℝ) ≠ x) →
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℝ)) - x * P.eval (Real.log x)|
        ≤ K * x ^ (1 / 2 + ε) := by
    intro x hx hxi
    have h := hK x hx hxi
    set w : ℂ := (((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℝ)) : ℝ) : ℂ)
        - ∑ j ∈ Finset.range k,
            b j * ((x * Real.log x ^ (k - 1 - j) / ((k - 1 - j).factorial : ℝ) : ℝ) : ℂ) with hw
    have hre : w.re = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℝ))
        - x * P.eval (Real.log x) := by
      simp only [hw, Complex.sub_re, Complex.ofReal_re, Complex.re_sum, Complex.re_mul_ofReal]
      rw [hPev, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [← hre]
    exact (Complex.abs_re_le_norm w).trans h
  -- ## All `x > 1`, by approaching from the right
  have hall : ∀ x : ℝ, 1 < x →
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℝ)) - x * P.eval (Real.log x)|
        ≤ K * x ^ (1 / 2 + ε) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    set S : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℝ) with hS
    have hfl : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have hev : ∀ᶠ y in nhdsWithin x (Set.Ioi x),
        |S - y * P.eval (Real.log y)| ≤ K * y ^ (1 / 2 + ε) := by
      have hmem : Set.Ioo x ((⌊x⌋₊ : ℝ) + 1) ∈ nhdsWithin x (Set.Ioi x) :=
        Ioo_mem_nhdsGT hfl
      filter_upwards [hmem] with y hy
      have hy1 : 1 < y := by linarith [hy.1]
      have hfy : ⌊y⌋₊ = ⌊x⌋₊ := by
        rw [Nat.floor_eq_iff (by linarith)]
        exact ⟨(Nat.floor_le hx0.le).trans hy.1.le, hy.2⟩
      have hyi : ∀ n : ℕ, (n : ℝ) ≠ y := by
        intro n hn
        have h1 : (⌊x⌋₊ : ℝ) < n := by
          rw [hn]; exact lt_of_le_of_lt (Nat.floor_le hx0.le) hy.1
        have h2 : (n : ℝ) < (⌊x⌋₊ : ℝ) + 1 := by rw [hn]; exact hy.2
        have h1' : ⌊x⌋₊ < n := by exact_mod_cast h1
        have h2' : n < ⌊x⌋₊ + 1 := by exact_mod_cast h2
        omega
      have h := hreal y hy1 hyi
      rw [hfy] at h
      exact h
    have hcont : ContinuousAt (fun y : ℝ => |S - y * P.eval (Real.log y)|) x := by
      have : ContinuousAt (fun y : ℝ => Real.log y) x := Real.continuousAt_log hx0.ne'
      have hP' : ContinuousAt (fun y : ℝ => P.eval (Real.log y)) x :=
        (P.continuous.continuousAt).comp this
      exact (continuousAt_const.sub (continuousAt_id.mul hP')).abs
    have hcont2 : ContinuousAt (fun y : ℝ => K * y ^ (1 / 2 + ε)) x :=
      continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne'))
    exact le_of_tendsto_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (hcont2.tendsto.mono_left nhdsWithin_le_nhds) hev
  refine IsBigO.of_bound K ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  exact hall x hx

/-- **The summatory function of `d_k`, conditional on the Lindelöf hypothesis**, in existential
form. Assume the Lindelöf hypothesis (`LindelofHypothesis`, an open conjecture) and let `k ≥ 1`.
Then there is a real polynomial `P` of degree `k - 1` and leading coefficient `1 / (k - 1)!`
such that `∑_{n ≤ x} d_k(n) = x * P (log x) + O(x ^ (1 / 2 + ε))` for every `ε > 0`. The
polynomial is `piltzMainPoly k`; see
`ArithmeticFunction.sum_piltz_sub_mul_piltzMainPoly_isBigO_of_lindelofHypothesis`. -/
theorem exists_polynomial_sum_piltz_isBigO_of_lindelofHypothesis
    (hLindelof : LindelofHypothesis) {k : ℕ} (hk : 1 ≤ k) :
    ∃ P : Polynomial ℝ, P.degree = ((k - 1 : ℕ) : WithBot ℕ) ∧
      P.leadingCoeff = 1 / ((k - 1).factorial : ℝ) ∧ ∀ ε : ℝ, 0 < ε →
        (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (piltz k n : ℝ))
          - x * P.eval (Real.log x)) =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε) :=
  ⟨piltzMainPoly k, piltzMainPoly_degree hk, piltzMainPoly_leadingCoeff hk, fun _ hε =>
    sum_piltz_sub_mul_piltzMainPoly_isBigO_of_lindelofHypothesis hLindelof hk hε⟩

end ArithmeticFunction
