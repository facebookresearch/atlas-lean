/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Basic
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Functions of degree zero in the Selberg class

The theorem of Conrey and Ghosh: a member of the Selberg class whose functional equation has
no Gamma factors (degree `0`) is the constant function `1`.

The proof has an analytic and an arithmetic half. Without Gamma factors the functional equation
reads `Q^s F(s) = w conj (Q^{1 - s̄} F(1 - s̄))`. Comparing the mean values of `F(s) n^s` on the
lines `Re s = 2` and `Re s = -1` (moved across a half-strip by Phragmén–Lindelöf) expresses each
coefficient `a n` through the reflected coefficients; this forces `Q² = q` to be an integer, `a`
to be supported on the divisors of `q`, and `|a q| = √q`. Such a Dirichlet polynomial has an
Euler logarithm `b n = O(n^θ)` with `θ < 1/2` only when `q = 1`: at a prime `p ∣ q` the local
Euler factor would be a polynomial with a root of size `≤ p^{-1/2}`, which the logarithm bound
excludes.

## Main statements

* `SelbergClass.eq_one_of_degree_eq_zero`: **Conrey–Ghosh**, a member of `𝒮` with a functional
  equation of degree `0` is `1`.
-/

open ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClass


/-- A polynomial with constant term `1` and leading coefficient of size at least `c ^ r`
has a root of size at most `c⁻¹`. -/
private theorem exists_root_norm_le_inv (A : ℕ → ℂ) (r : ℕ) (hr : 1 ≤ r) (hA0 : A 0 = 1) (c : ℝ)
    (hc : 0 < c) (hAr : c ^ r ≤ ‖A r‖) :
    ∃ x : ℂ, ‖x‖ ≤ c⁻¹ ∧ ∑ k ∈ Finset.range (r + 1), A k * x ^ k = 0 := by
  classical
  set P : Polynomial ℂ := ∑ k ∈ Finset.range (r + 1), Polynomial.C (A k) * Polynomial.X ^ k
    with hP
  have hcoeff : ∀ n, P.coeff n = if n < r + 1 then A n else 0 := by
    intro n
    simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    split_ifs with h
    · rw [Finset.sum_eq_single n]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro hn; simp [Finset.mem_range] at hn; omega
    · apply Finset.sum_eq_zero
      intro b hb
      simp only [Finset.mem_range] at hb
      have : n ≠ b := by omega
      simp [this]
  have hArne : A r ≠ 0 := by
    intro h; rw [h, norm_zero] at hAr; exact absurd hAr (not_le.2 (pow_pos hc r))
  have hdeg : P.natDegree = r := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      rw [hcoeff]
      have : ¬ n < r + 1 := by
        have := hn
        omega
      simp [this]
    · rw [hcoeff]; simp [hArne]
  have hlc : P.leadingCoeff = A r := by
    rw [Polynomial.leadingCoeff, hdeg, hcoeff]; simp
  have hcard : Multiset.card P.roots = P.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have h0 : P.eval 0 = 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, hcoeff]; simp [hA0]
  have h1 : (1 : ℂ) = A r * (P.roots.map fun a => -a).prod := by
    rw [← h0]
    conv_lhs => rw [← hfac]
    simp [Polynomial.eval_multiset_prod, hlc, Multiset.map_map]
  have hne : P.roots ≠ 0 := by
    intro h; rw [h, hdeg] at hcard; simp at hcard; omega
  obtain ⟨z, hz, hmin⟩ := Multiset.exists_min_image (fun z : ℂ => ‖z‖) hne
  refine ⟨z, ?_, ?_⟩
  · have hn1 : (1 : ℝ) = ‖A r‖ * ((P.roots.map fun a => -a).map fun x => ‖x‖).prod := by
      have := congrArg norm h1
      rw [norm_one, norm_mul] at this
      rw [this]
      congr 1
      exact map_multiset_prod (normHom : ℂ →*₀ ℝ) _
    have hle : ‖z‖ ^ r ≤ ((P.roots.map fun a => -a).map fun x => ‖x‖).prod := by
      rw [Multiset.map_map]
      have hc' : (P.roots.map fun _ => ‖z‖).prod = ‖z‖ ^ r := by
        rw [Multiset.map_const', Multiset.prod_replicate, hcard, hdeg]
      rw [← hc']
      apply Multiset.prod_map_le_prod_map₀
      · intro _ _; positivity
      · intro w hw; simpa using hmin w hw
    by_contra hlt
    push Not at hlt
    have : (1 : ℝ) < ‖A r‖ * ‖z‖ ^ r := by
      calc (1 : ℝ) = c ^ r * c⁻¹ ^ r := by rw [← mul_pow, mul_inv_cancel₀ hc.ne', one_pow]
        _ < ‖A r‖ * ‖z‖ ^ r := by
          apply mul_lt_mul' hAr (pow_lt_pow_left₀ hlt (by positivity) (by omega)) (by positivity)
            (lt_of_lt_of_le (by positivity) hAr)
    have := mul_le_mul_of_nonneg_left hle (norm_nonneg (A r))
    linarith
  · have := (Polynomial.mem_roots (Polynomial.ne_zero_of_natDegree_gt (n := 0)
      (by omega))).1 hz
    rw [Polynomial.IsRoot, hP, Polynomial.eval_finsetSum] at this
    simpa using this

/-- The local step: an Euler factor `∑ A k x ^ k` of degree `r` with `|A r| ≥ p ^ (r / 2)`
cannot have a logarithm `∑ B j x ^ j` (in the sense of the recursion `hrec`) with
`B j = O(p ^ (j θ))`, `θ < 1 / 2`. -/
private theorem false_of_eulerFactor_log (p : ℕ) (hp : 2 ≤ p) (A B : ℕ → ℂ) (r : ℕ) (hr : 1 ≤ r)
    (hA0 : A 0 = 1) (hAr : Real.sqrt p ^ r ≤ ‖A r‖) (hAz : ∀ k, r < k → A k = 0)
    (hB0 : B 0 = 0) (θ C : ℝ) (hθ : θ < 1 / 2) (hB : ∀ j, ‖B j‖ ≤ C * ((p : ℝ) ^ θ) ^ j)
    (hrec : ∀ k : ℕ, (k : ℂ) * A k = ∑ x ∈ Finset.antidiagonal k, (x.1 : ℂ) * B x.1 * A x.2) :
    False := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hC : 0 ≤ C := by
    have := hB 0
    simp only [pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  set θ' : ℝ := (θ + 1 / 2) / 2 with hθ'
  set ρ : ℝ := (p : ℝ) ^ (-θ') with hρ
  set s : ℝ := (p : ℝ) ^ θ with hs
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hp0 _
  have hs0 : 0 < s := Real.rpow_pos_of_pos hp0 _
  have hq0 : s * ρ < 1 := by
    rw [hs, hρ, ← Real.rpow_add hp0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by rw [hθ']; linarith)
  have hq0n : 0 ≤ s * ρ := by positivity
  -- the root
  obtain ⟨x0, hx0, hPx0⟩ := exists_root_norm_le_inv A r hr hA0 (Real.sqrt p)
    (Real.sqrt_pos.2 hp0) hAr
  have hx0ρ : ‖x0‖ < ρ := by
    refine lt_of_le_of_lt hx0 ?_
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hp0.le, hρ]
    exact Real.rpow_lt_rpow_of_exponent_lt hp1 (by rw [hθ']; linarith)
  set U : Set ℂ := Metric.ball 0 ρ with hU
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUc : IsPreconnected U := (convex_ball _ _).isPreconnected
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self hρ0
  -- the logarithm series and its derivative
  set Bf : ℂ → ℂ := fun x => ∑' j : ℕ, B j * x ^ j with hBf
  set u : ℕ → ℝ := fun j => C * ρ⁻¹ * ((j : ℝ) ^ 1 * (s * ρ) ^ j) with hu
  have hus : Summable u := by
    refine Summable.mul_left _ ?_
    have hn : ‖s * ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0n]; exact hq0
    exact summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have hbd : ∀ j : ℕ, ∀ y ∈ U, ‖(j : ℂ) * B j * y ^ (j - 1)‖ ≤ u j := by
    intro j y hy
    have hy' : ‖y‖ ≤ ρ := (mem_ball_zero_iff.1 hy).le
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; simp [hu]
    · have h1 : ‖y ^ (j - 1)‖ ≤ ρ ^ (j - 1) := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hy' _
      have h2 : ρ ^ (j - 1) = ρ⁻¹ * ρ ^ j := by
        rw [← pow_sub_one_mul hj.ne' ρ] ; field_simp
      calc ‖(j : ℂ) * B j * y ^ (j - 1)‖ = j * ‖B j‖ * ‖y ^ (j - 1)‖ := by
            rw [norm_mul, norm_mul, Complex.norm_natCast]
        _ ≤ j * (C * s ^ j) * ρ ^ (j - 1) := by
            gcongr
            exact hB j
        _ = u j := by rw [hu, h2]; simp only; rw [mul_pow]; ring
  have hderB : ∀ x ∈ U, HasDerivAt Bf (∑' j : ℕ, (j : ℂ) * B j * x ^ (j - 1)) x := by
    intro x hx
    refine hasDerivAt_tsum_of_isPreconnected (u := u) hus hUo hUc
      (g := fun j x => B j * x ^ j) (g' := fun j x => (j : ℂ) * B j * x ^ (j - 1))
      ?_ hbd h0U ?_ hx
    · intro j y _
      refine ((hasDerivAt_pow j y).const_mul (B j)).congr_deriv ?_
      ring
    · simpa using (summable_of_ne_finset_zero (s := {0}) (f := fun j => B j * (0 : ℂ) ^ j)
        (by intro j hj; simp at hj; simp [hj]))
  have hus1 : Summable (fun j : ℕ => u (j + 1)) := (summable_nat_add_iff 1).2 hus
  have hbd1 : ∀ j : ℕ, ∀ y ∈ U, ‖((j : ℂ) + 1) * B (j + 1) * y ^ j‖ ≤ u (j + 1) := by
    intro j y hy
    have := hbd (j + 1) y hy
    simpa using this
  have hderB' : ∀ x ∈ U, HasDerivAt Bf (∑' j : ℕ, ((j : ℂ) + 1) * B (j + 1) * x ^ j) x := by
    intro x hx
    have hsm : Summable (fun j : ℕ => (j : ℂ) * B j * x ^ (j - 1)) :=
      Summable.of_norm_bounded hus (fun j => hbd j x hx)
    have := hderB x hx
    rw [hsm.tsum_eq_zero_add] at this
    simpa using this
  set P : ℂ → ℂ := fun x => ∑ k ∈ Finset.range (r + 1), A k * x ^ k with hPdef
  have hderP : ∀ x, HasDerivAt P (∑ k ∈ Finset.range r, ((k : ℂ) + 1) * A (k + 1) * x ^ k) x := by
    intro x
    have := HasDerivAt.fun_sum (u := Finset.range (r + 1)) (A := fun k x => A k * x ^ k)
      (A' := fun k => A k * ((k : ℂ) * x ^ (k - 1)))
      (fun k _ => (hasDerivAt_pow k x).const_mul (A k))
    refine this.congr_deriv ?_
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hkey : ∀ x ∈ U, (∑ k ∈ Finset.range r, ((k : ℂ) + 1) * A (k + 1) * x ^ k) =
      (∑' j : ℕ, ((j : ℂ) + 1) * B (j + 1) * x ^ j) * P x := by
    intro x hx
    have hterm : ∀ n : ℕ, ∑ kl ∈ Finset.antidiagonal n,
        ((kl.1 : ℂ) + 1) * B (kl.1 + 1) * x ^ kl.1 * (A kl.2 * x ^ kl.2) =
        ((n : ℂ) + 1) * A (n + 1) * x ^ n := by
      intro n
      have h := hrec (n + 1)
      rw [Finset.Nat.sum_antidiagonal_succ] at h
      simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one] at h
      have : ∑ kl ∈ Finset.antidiagonal n,
          ((kl.1 : ℂ) + 1) * B (kl.1 + 1) * x ^ kl.1 * (A kl.2 * x ^ kl.2) =
          (∑ kl ∈ Finset.antidiagonal n, ((kl.1 : ℂ) + 1) * B (kl.1 + 1) * A kl.2) * x ^ n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro kl hkl
        rw [Finset.mem_antidiagonal] at hkl
        rw [← hkl, pow_add]
        ring
      rw [this, ← h]
    have hPt : P x = ∑' i : ℕ, A i * x ^ i := by
      rw [tsum_eq_sum (s := Finset.range (r + 1))]
      intro i hi
      simp only [Finset.mem_range, not_lt] at hi
      rw [hAz i (by omega), zero_mul]
    have hf : Summable (fun j : ℕ => ‖((j : ℂ) + 1) * B (j + 1) * x ^ j‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => hbd1 j x hx) hus1
    have hg : Summable (fun i : ℕ => ‖A i * x ^ i‖) := by
      apply summable_of_ne_finset_zero (s := Finset.range (r + 1))
      intro i hi
      simp only [Finset.mem_range, not_lt] at hi
      rw [hAz i (by omega), zero_mul, norm_zero]
    rw [hPt, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
    rw [tsum_eq_sum (s := Finset.range r)]
    · apply Finset.sum_congr rfl
      intro n _
      exact (hterm n).symm
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      rw [hterm n, hAz (n + 1) (by omega)]
      simp
  set E : ℂ → ℂ := fun x => P x * Complex.exp (-Bf x) with hE
  have hderE : ∀ x ∈ U, HasDerivAt E 0 x := by
    intro x hx
    have h1 := (hderP x).mul ((hderB' x hx).neg.cexp)
    refine h1.congr_deriv ?_
    rw [hkey x hx]
    ring
  have hEc : ∀ x ∈ U, E x = E 0 := fun x hx =>
    hUo.is_const_of_deriv_eq_zero hUc
      (fun y hy => (hderE y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hderE y hy).deriv) hx h0U
  have hBf0 : Bf 0 = 0 := by
    rw [hBf]
    simp only
    rw [tsum_eq_single 0 (fun j hj => by simp [hj])]
    simp [hB0]
  have hE0 : E 0 = 1 := by
    simp only [hE, hPdef, hBf0, neg_zero, Complex.exp_zero, mul_one]
    rw [Finset.sum_range_succ']
    simp [hA0]
  have := hEc x0 (mem_ball_zero_iff.2 hx0ρ)
  rw [hE0] at this
  simp only [hE, hPdef, hPx0, zero_mul] at this
  exact zero_ne_one this

open LSeries LSeries.notation in
/-- Differentiating `∑ a n n^{-s} = exp (∑ b n n^{-s})` gives `log · a = (log · b) ⍟ a`. -/
private theorem logMul_eq_convolution_of_abscissaOfAbsConv_le (a : ArithmeticFunction ℂ) (b : ℕ → ℂ)
    (ha : abscissaOfAbsConv (fun n => a n) ≤ (2 : ℝ))
    (hab : ∀ s : ℂ, 1 < s.re →
      LSeriesSummable b s ∧ LSeries (fun n => a n) s = Complex.exp (LSeries b s))
    (n : ℕ) (hn : n ≠ 0) :
    logMul (fun n => a n) n = (logMul b ⍟ fun n => a n) n := by
  have hb : abscissaOfAbsConv b ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => (hab y (by simpa using hy)).1)
  refine LSeries.eq_of_LSeries_eventually_eq ?_ ?_ ?_ hn
  · rw [LSeries.abscissaOfAbsConv_logMul]; exact lt_of_le_of_lt ha (EReal.coe_lt_top _)
  · refine lt_of_le_of_lt (LSeries.abscissaOfAbsConv_convolution_le _ _) (max_lt ?_ ?_)
    · rw [LSeries.abscissaOfAbsConv_logMul]; exact hb.trans_lt (EReal.coe_lt_top _)
    · exact ha.trans_lt (EReal.coe_lt_top _)
  · filter_upwards [Filter.eventually_gt_atTop (2 : ℝ)] with x hx
    have hxa : abscissaOfAbsConv (fun n => a n) < ((x : ℂ)).re := by
      simp only [Complex.ofReal_re]; exact ha.trans_lt (by exact_mod_cast hx)
    have hxb : abscissaOfAbsConv b < ((x : ℂ)).re := by
      simp only [Complex.ofReal_re]; exact hb.trans_lt (by exact_mod_cast (by linarith : 1 < x))
    have hx1 : 1 < ((x : ℂ)).re := by simp only [Complex.ofReal_re]; linarith
    have hloc : LSeries (fun n => a n) =ᶠ[nhds (x : ℂ)] fun s => Complex.exp (LSeries b s) := by
      have : {s : ℂ | 1 < s.re} ∈ nhds (x : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx1
      filter_upwards [this] with s hs using (hab s hs).2
    have h1 := LSeries_deriv hxa
    have h2 : deriv (fun s => Complex.exp (LSeries b s)) x =
        Complex.exp (LSeries b x) * (-LSeries (logMul b) x) :=
      ((LSeries_hasDerivAt hxb).cexp).deriv
    rw [hloc.deriv_eq, h2, ← (hab x hx1).2] at h1
    rw [LSeries_convolution (by rwa [LSeries.abscissaOfAbsConv_logMul]) hxa]
    linear_combination h1

/-- A recursion `lg n · a n = ∑_{d ∣ n} L d · a (n / d)` with `L` supported on prime powers and
`lg` additive forces `a` to be multiplicative. -/
private theorem isMultiplicative_of_logMul_eq_sum (a : ArithmeticFunction ℂ) (L lg : ℕ → ℂ) (ha1 : a
    1 = 1)
    (hL : ∀ n, L n ≠ 0 → IsPrimePow n)
    (hlg : ∀ m n, m ≠ 0 → n ≠ 0 → lg (m * n) = lg m + lg n) (hlg0 : ∀ n, 2 ≤ n → lg n ≠ 0)
    (hrec : ∀ n, n ≠ 0 → lg n * a n = ∑ d ∈ n.divisors, L d * a (n / d)) :
    a.IsMultiplicative := by
  classical
  have hL1 : L 1 = 0 := by
    by_contra h; exact not_isPrimePow_one (hL 1 h)
  refine ⟨ha1, ?_⟩
  suffices H : ∀ N m n, m * n < N → m.Coprime n → a (m * n) = a m * a n from
    fun {m n} h => H _ m n (Nat.lt_succ_self _) h
  intro N
  induction N with
  | zero => intro m n h; omega
  | succ N ih =>
    intro m n hmn hcop
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · simp
      · simp [ha1]
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp
      · simp [ha1]
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm0 hn0
    set f : ℕ → ℂ := fun d => L d * a (m * n / d) with hf
    have hsplit : ∑ d ∈ (m * n).divisors, f d = ∑ d ∈ m.divisors, f d + ∑ d ∈ n.divisors, f d := by
      have hsub : m.divisors ∪ n.divisors ⊆ (m * n).divisors := by
        intro d hd
        rw [Finset.mem_union, Nat.mem_divisors, Nat.mem_divisors] at hd
        rw [Nat.mem_divisors]
        rcases hd with ⟨h, _⟩ | ⟨h, _⟩
        · exact ⟨h.mul_right n, hmn0⟩
        · exact ⟨h.mul_left m, hmn0⟩
      rw [← Finset.sum_subset hsub, ← Finset.sum_union_inter]
      · have : ∑ d ∈ m.divisors ∩ n.divisors, f d = 0 := by
          apply Finset.sum_eq_zero
          intro d hd
          rw [Finset.mem_inter, Nat.mem_divisors, Nat.mem_divisors] at hd
          have : d = 1 := Nat.eq_one_of_dvd_coprimes hcop hd.1.1 hd.2.1
          simp [hf, this, hL1]
        rw [this, add_zero]
      · intro d hd hnot
        by_contra hfd
        have hLd : L d ≠ 0 := by
          intro h; apply hfd; simp [hf, h]
        have hdvd := (Nat.mem_divisors.1 hd).1
        rcases (hcop.isPrimePow_dvd_mul (hL d hLd)).1 hdvd with h | h
        · exact hnot (Finset.mem_union_left _ (Nat.mem_divisors.2 ⟨h, hm0⟩))
        · exact hnot (Finset.mem_union_right _ (Nat.mem_divisors.2 ⟨h, hn0⟩))
    have hA : ∑ d ∈ m.divisors, f d = a n * (lg m * a m) := by
      rw [hrec m hm0, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨e, rfl⟩ := (Nat.mem_divisors.1 hd).1
      have hd0 : d ≠ 0 := by rintro rfl; simp at hm0
      have he0 : e ≠ 0 := by rintro rfl; simp at hm0
      rcases eq_or_ne d 1 with rfl | hd1
      · simp [hf, hL1]
      have h1 : d * e * n / d = e * n := by
        rw [mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
      have h2 : d * e / d = e := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)
      have hlt : e * n < N := by
        have : e * n < d * e * n := by
          have : 2 ≤ d := by omega
          have : 0 < e * n := Nat.pos_of_ne_zero (Nat.mul_ne_zero he0 hn0)
          nlinarith
        omega
      have hcop' : e.Coprime n := Nat.Coprime.coprime_dvd_left (Dvd.intro_left d rfl) hcop
      simp only [hf, h1, h2, ih e n hlt hcop']
      ring
    have hB : ∑ d ∈ n.divisors, f d = a m * (lg n * a n) := by
      rw [hrec n hn0, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨e, rfl⟩ := (Nat.mem_divisors.1 hd).1
      have hd0 : d ≠ 0 := by rintro rfl; simp at hn0
      have he0 : e ≠ 0 := by rintro rfl; simp at hn0
      rcases eq_or_ne d 1 with rfl | hd1
      · simp [hf, hL1]
      have h1 : m * (d * e) / d = m * e := by
        rw [Nat.mul_left_comm, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
      have h2 : d * e / d = e := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)
      have hlt : m * e < N := by
        have : m * e < m * (d * e) := by
          have : 2 ≤ d := by omega
          have : 0 < m * e := Nat.pos_of_ne_zero (Nat.mul_ne_zero hm0 he0)
          nlinarith
        omega
      have hcop' : m.Coprime e := Nat.Coprime.coprime_dvd_right (Dvd.intro_left d rfl) hcop
      simp only [hf, h1, h2, ih m e hlt hcop']
      ring
    have hmain := hrec (m * n) hmn0
    rw [hsplit, hA, hB, hlg m n hm0 hn0] at hmain
    have hne : lg m + lg n ≠ 0 := by
      rw [← hlg m n hm0 hn0]; exact hlg0 _ (by nlinarith)
    apply mul_left_cancel₀ hne
    linear_combination hmain

/-- The arithmetic half of Conrey–Ghosh: a Dirichlet polynomial supported on the divisors of
`q ≥ 2`, with `a 1 = 1` and `|a q| = √q`, has no Euler logarithm `b n = O(n ^ θ)`, `θ < 1/2`. -/
private theorem false_of_isEulerLog_of_support_dvd (a : ArithmeticFunction ℂ) (b : ℕ → ℂ)
    (θ C : ℝ) (hθ : θ < 1 / 2)
    (hlog : IsEulerLog a b) (hbC : ∀ n, ‖b n‖ ≤ C * (n : ℝ) ^ θ)
    (ha_abs : LSeries.abscissaOfAbsConv (fun n => a n) ≤ (2 : ℝ)) (ha1 : a 1 = 1)
    (q : ℕ) (hq : 2 ≤ q) (hsupp : ∀ n, ¬ n ∣ q → a n = 0) (haq : ‖a q‖ = Real.sqrt q) :
    False := by
  classical
  have hb1 : b 1 = 0 := by
    by_contra h; exact not_isPrimePow_one (hlog.1 1 h)
  -- the recursion `log n · a n = ∑ log d · b d · a (n / d)`
  have hrec : ∀ n : ℕ, n ≠ 0 → Complex.log n * a n =
      ∑ d ∈ n.divisors, Complex.log d * b d * a (n / d) := by
    intro n hn
    have := logMul_eq_convolution_of_abscissaOfAbsConv_le a b ha_abs hlog.2 n hn
    simp only [LSeries.logMul, LSeries.convolution_def] at this
    rw [this, Nat.sum_divisorsAntidiagonal (fun i j => Complex.log i * b i * a j)]
  have hmul : a.IsMultiplicative := by
    refine isMultiplicative_of_logMul_eq_sum a (fun d => Complex.log d * b d) (fun n => Complex.log
        n) ha1
      ?_ ?_ ?_ hrec
    · intro n hn
      exact hlog.1 n (right_ne_zero_of_mul hn)
    · intro m n hm hn
      rw [← Complex.natCast_log, ← Complex.natCast_log, ← Complex.natCast_log, Nat.cast_mul,
        Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)]
      push_cast; ring
    · intro n hn
      rw [← Complex.natCast_log]
      exact_mod_cast (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  -- a prime power `p ^ k ∥ q` with `|a (p ^ k)| ≥ p ^ (k / 2)`
  have hq0 : q ≠ 0 := by omega
  obtain ⟨p, hpq, hbig⟩ : ∃ p ∈ q.primeFactors,
      Real.sqrt ((p : ℝ) ^ q.factorization p) ≤ ‖a (p ^ q.factorization p)‖ := by
    by_contra hcon
    push Not at hcon
    have h1 : ‖a q‖ = ∏ p ∈ q.primeFactors, ‖a (p ^ q.factorization p)‖ := by
      rw [hmul.multiplicative_factorization a hq0, Finsupp.prod, Nat.support_factorization]
      exact norm_prod _ _
    have h2 : Real.sqrt q = ∏ p ∈ q.primeFactors, Real.sqrt ((p : ℝ) ^ q.factorization p) := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hq0]
      rw [Finsupp.prod, Nat.support_factorization]
      push_cast
      exact Real.sqrt_prod _ (fun i _ => by positivity)
    have hpos : ∀ p ∈ q.primeFactors, 0 < ‖a (p ^ q.factorization p)‖ := by
      intro p hp
      rcases (norm_nonneg (a (p ^ q.factorization p))).lt_or_eq with h | h
      · exact h
      · exfalso
        have : ‖a q‖ = 0 := by
          rw [h1]; exact Finset.prod_eq_zero hp h.symm
        rw [haq] at this
        exact (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < q))).ne' this
    have hne : q.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
    have := Finset.prod_lt_prod_of_nonempty₀ hpos hcon hne
    rw [← h1, ← h2, haq] at this
    exact lt_irrefl _ this
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpq
  have hpdvd : p ∣ q := Nat.dvd_of_mem_primeFactors hpq
  set r := q.factorization p with hr
  have hr1 : 1 ≤ r := hp.factorization_pos_of_dvd hq0 hpdvd
  have hp2 : 2 ≤ p := hp.two_le
  have hlogp : Complex.log p ≠ 0 := by
    rw [← Complex.natCast_log]
    exact_mod_cast (Real.log_pos (by exact_mod_cast (by omega : 1 < p))).ne'
  refine false_of_eulerFactor_log p hp2 (fun j => a (p ^ j)) (fun j => b (p ^ j)) r hr1
    (by simp [ha1]) ?_ ?_ (by simp [hb1]) θ C hθ ?_ ?_
  · have e : Real.sqrt ((p : ℝ) ^ r) = Real.sqrt p ^ r := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt p ^ r)]
      congr 1
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by positivity)]
    rw [e] at hbig
    simpa using hbig
  · intro k hk
    apply hsupp
    intro hdvd
    have := (hp.pow_dvd_iff_le_factorization hq0).1 hdvd
    omega
  · intro j
    have := hbC (p ^ j)
    push_cast at this
    have e : ((p : ℝ) ^ j) ^ θ = ((p : ℝ) ^ θ) ^ j := by
      rw [← Real.rpow_natCast (p : ℝ) j, ← Real.rpow_mul (by positivity), mul_comm,
        Real.rpow_mul (by positivity), Real.rpow_natCast]
    rw [e] at this
    exact this
  · intro k
    have h := hrec (p ^ k) (pow_ne_zero _ hp.ne_zero)
    rw [Nat.sum_divisors_prime_pow hp] at h
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply mul_left_cancel₀ hlogp
    have hl : ∀ i : ℕ, Complex.log ((p ^ i : ℕ) : ℂ) = i * Complex.log p := by
      intro i
      rw [← Complex.natCast_log, ← Complex.natCast_log, Nat.cast_pow, Real.log_pow]
      push_cast; ring
    rw [hl k] at h
    rw [Finset.mul_sum]
    calc Complex.log p * (k * a (p ^ k)) = ↑k * Complex.log ↑p * a (p ^ k) := by ring
      _ = _ := h
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [Nat.pow_div hik hp.pos, hl i]
        ring

/-- Mean values of an absolutely convergent trigonometric series over `[1, T]`. -/
private theorem tendsto_average_tsum_exp_mul_I (u : ℕ → ℂ) (ω : ℕ → ℝ) (hu : Summable (fun k => ‖u
    k‖)) :
    Filter.Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
        ∫ y in (1 : ℝ)..T, ∑' k, u k * Complex.exp (((ω k * y : ℝ) : ℂ) * Complex.I))
      Filter.atTop (nhds (∑' k, if ω k = 0 then u k else 0)) := by
  have hint : ∀ T : ℝ, (T : ℂ)⁻¹ *
      ∫ y in (1 : ℝ)..T, ∑' k, u k * Complex.exp (((ω k * y : ℝ) : ℂ) * Complex.I) =
      ∑' k, (T : ℂ)⁻¹ * ∫ y in (1 : ℝ)..T, u k * Complex.exp (((ω k * y : ℝ) : ℂ) * Complex.I) := by
    intro T
    rw [tsum_mul_left]
    congr 1
    let f : ℕ → C(ℝ, ℂ) := fun k =>
      ⟨fun y => u k * Complex.exp (((ω k * y : ℝ) : ℂ) * Complex.I), by fun_prop⟩
    have := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm (a := 1) (b := T)
      (f := f) ?_
    · exact this.symm
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hu
      refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 (fun x => ?_)
      simp only [f, ContinuousMap.restrict_apply, ContinuousMap.coe_mk]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  simp_rw [hint]
  apply tendsto_tsum_of_dominated_convergence (bound := fun k => ‖u k‖) hu
  · intro k
    split_ifs with h
    · have e : ∀ T : ℝ, T ≠ 0 → (T : ℂ)⁻¹ *
          ∫ y in (1 : ℝ)..T, u k * Complex.exp (((ω k * y : ℝ) : ℂ) * Complex.I) =
          u k - u k * (T : ℂ)⁻¹ := by
        intro T hT
        simp only [h, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one,
          intervalIntegral.integral_const, Complex.real_smul]
        have : (T : ℂ) ≠ 0 := by exact_mod_cast hT
        field_simp
        push_cast
        ring
      have hlim : Filter.Tendsto (fun T : ℝ => u k - u k * (T : ℂ)⁻¹) Filter.atTop
          (nhds (u k)) := by
        have : Filter.Tendsto (fun T : ℝ => (T : ℂ)⁻¹) Filter.atTop (nhds 0) := by
          have h1 := tendsto_inv_atTop_zero (𝕜 := ℝ)
          have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
          simpa [Function.comp_def] using h2
        simpa using (tendsto_const_nhds (x := u k)).sub (this.const_mul (u k))
      refine hlim.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with T hT
      exact (e T hT.ne').symm
    · have hc : ((ω k : ℂ) * Complex.I) ≠ 0 := by
        apply mul_ne_zero (by exact_mod_cast h) Complex.I_ne_zero
      have e : ∀ T : ℝ,
          ∫ y in (1 : ℝ)..T, u k * Complex.exp (((ω k * y : ℝ) : ℂ) * Complex.I) =
          u k * ((Complex.exp ((ω k : ℂ) * Complex.I * T) -
            Complex.exp ((ω k : ℂ) * Complex.I * (1 : ℝ))) / ((ω k : ℂ) * Complex.I)) := by
        intro T
        have : ∀ y : ℝ, (((ω k * y : ℝ) : ℂ) * Complex.I) = (ω k : ℂ) * Complex.I * y := by
          intro y; push_cast; ring
        simp_rw [this]
        rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
      have hb : ∀ T : ℝ, ‖(T : ℂ)⁻¹ *
          ∫ y in (1 : ℝ)..T, u k * Complex.exp (((ω k * y : ℝ) : ℂ) * Complex.I)‖ ≤
          (‖u k‖ * (2 / ‖(ω k : ℂ) * Complex.I‖)) * |T|⁻¹ := by
        intro T
        rw [e, norm_mul, norm_mul, norm_div, norm_inv, Complex.norm_real, Real.norm_eq_abs]
        have h1 : ‖Complex.exp ((ω k : ℂ) * Complex.I * T) -
            Complex.exp ((ω k : ℂ) * Complex.I * (1 : ℝ))‖ ≤ 2 := by
          refine (norm_sub_le _ _).trans ?_
          have a1 : ‖Complex.exp ((ω k : ℂ) * Complex.I * T)‖ = 1 := by
            rw [show (ω k : ℂ) * Complex.I * T = ((ω k * T : ℝ) : ℂ) * Complex.I by
              push_cast; ring]
            exact Complex.norm_exp_ofReal_mul_I _
          have a2 : ‖Complex.exp ((ω k : ℂ) * Complex.I * (1 : ℝ))‖ = 1 := by
            rw [show (ω k : ℂ) * Complex.I * (1 : ℝ) = ((ω k * 1 : ℝ) : ℂ) * Complex.I by
              push_cast; ring]
            exact Complex.norm_exp_ofReal_mul_I _
          rw [a1, a2]; norm_num
        have h2 : 0 < ‖(ω k : ℂ) * Complex.I‖ := norm_pos_iff.2 hc
        rw [mul_comm]
        gcongr
      apply squeeze_zero_norm hb
      have : Filter.Tendsto (fun T : ℝ => |T|⁻¹) Filter.atTop (nhds 0) := by
        refine tendsto_inv_atTop_zero.comp ?_
        exact Filter.tendsto_abs_atTop_atTop
      simpa using this.const_mul (‖u k‖ * (2 / ‖(ω k : ℂ) * Complex.I‖))
  · filter_upwards [Filter.eventually_ge_atTop 1] with T hT k
    have hT0 : 0 < T := by linarith
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := T)
      (C := ‖u k‖) (f := fun y => u k * Complex.exp (((ω k * y : ℝ) : ℂ) * Complex.I))
      (fun y _ => by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one])
    rw [abs_of_nonneg (by linarith)] at this
    calc T⁻¹ * ‖∫ y in (1 : ℝ)..T, u k * Complex.exp (((ω k * y : ℝ) : ℂ) * Complex.I)‖
        ≤ T⁻¹ * (‖u k‖ * (T - 1)) := by gcongr
      _ ≤ ‖u k‖ := by
        rw [← mul_assoc, mul_comm T⁻¹, mul_assoc]
        have : T⁻¹ * (T - 1) ≤ 1 := by
          rw [inv_mul_le_iff₀ hT0]; linarith
        calc ‖u k‖ * (T⁻¹ * (T - 1)) ≤ ‖u k‖ * 1 := by gcongr
          _ = ‖u k‖ := mul_one _

/-- Phragmén–Lindelöf: if `(s - 1) ^ m F(s)` is entire of finite order and `F` is bounded on
the lines `Re s = -1` and `Re s = 2`, then `F` is bounded on `-1 ≤ Re s ≤ 2`, `Im s ≥ 1`. -/
private theorem exists_bound_strip_of_bound_lines (F G : ℂ → ℂ) (m : ℕ) (β : ℝ) (hGd :
    Differentiable ℂ G)
    (hGo : Complex.HasGrowthOrderLE G β) (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s) (K : ℝ)
    (hb : ∀ s : ℂ, (s.re = -1 ∨ s.re = 2) → ‖F s‖ ≤ K) :
    ∃ M, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 1 ≤ s.im → ‖F s‖ ≤ M := by
  set f : ℂ → ℂ := fun z => G z / (z + 2) ^ m with hf
  have hz2 : ∀ z : ℂ, -1 ≤ z.re → 1 ≤ ‖z + 2‖ := by
    intro z hz
    calc (1 : ℝ) ≤ |(z + 2).re| := by
          rw [Complex.add_re]; norm_num; rw [abs_of_nonneg (by linarith)]; linarith
      _ ≤ ‖z + 2‖ := Complex.abs_re_le_norm _
  -- the boundary bound
  have hK : 0 ≤ K := (norm_nonneg _).trans (hb 2 (Or.inr (by norm_num)))
  have hbd : ∀ z : ℂ, (z.re = -1 ∨ z.re = 2) → ‖f z‖ ≤ 4 ^ m * K := by
    intro z hz
    have hre : -1 ≤ z.re := by rcases hz with h | h <;> (rw [h]; try norm_num)
    have hz1 : z ≠ 1 := by
      rintro rfl; rcases hz with h | h <;> norm_num at h
    have h2 := hz2 z hre
    have h3 : ‖z - 1‖ ≤ 4 * ‖z + 2‖ := by
      calc ‖z - 1‖ = ‖(z + 2) - 3‖ := by ring_nf
        _ ≤ ‖z + 2‖ + ‖(3 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 4 * ‖z + 2‖ := by norm_num; linarith
    simp only [hf, hGF z hz1, norm_div, norm_mul, norm_pow]
    rw [div_le_iff₀ (by positivity)]
    calc ‖z - 1‖ ^ m * ‖F z‖ ≤ (4 * ‖z + 2‖) ^ m * K := by
          gcongr
          exact hb z hz
      _ = 4 ^ m * K * ‖z + 2‖ ^ m := by ring
  -- the growth condition
  set ε : ℝ := |β| + 1 with hε
  set k : ℝ := β + ε with hk
  have hk1 : 1 ≤ k := by rw [hk, hε]; have := neg_abs_le β; linarith
  obtain ⟨c0, hc0⟩ := (hGo ε (by positivity)).bound
  rw [← comap_norm_atTop, Filter.eventually_comap, Filter.eventually_atTop] at hc0
  obtain ⟨R, hR⟩ := hc0
  have hlim : ∀ᶠ x : ℝ in Filter.atTop, (x + 2) ^ k ≤ Real.exp x := by
    have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k 1 one_pos).comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop 2 Filter.tendsto_id)
    have h2 := h1.eventually (gt_mem_nhds (show (0 : ℝ) < Real.exp (-2) by positivity))
    filter_upwards [h2] with x hx
    simp only [Function.comp_apply, id] at hx
    have : Real.exp (-1 * (x + 2)) = Real.exp (-2) * Real.exp (-x) := by
      rw [← Real.exp_add]; ring_nf
    rw [this] at hx
    have hx' : (x + 2) ^ k * Real.exp (-x) < 1 := by
      have := Real.exp_pos (-2)
      nlinarith [Real.exp_pos (-x)]
    have := Real.exp_pos x
    calc (x + 2) ^ k = (x + 2) ^ k * Real.exp (-x) * Real.exp x := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ 1 * Real.exp x := by gcongr
      _ = Real.exp x := one_mul _
  rw [Filter.eventually_atTop] at hlim
  obtain ⟨X0, hX0⟩ := hlim
  have hgrowth : ∃ c < Real.pi / (2 - -1), ∃ B, f =O[Filter.comap (_root_.abs ∘ Complex.im)
      Filter.atTop ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo (-1) 2)]
      fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1, ?_, 1, ?_⟩
    · have := Real.pi_gt_three
      rw [lt_div_iff₀ (by norm_num)]; linarith
    refine Asymptotics.IsBigO.of_bound c0 ?_
    rw [Filter.eventually_inf_principal, Filter.eventually_comap, Filter.eventually_atTop]
    refine ⟨max (max R X0) 0, fun y hy z hz hzs => ?_⟩
    simp only [Function.comp_apply] at hz
    simp only [Set.mem_preimage, Set.mem_Ioo] at hzs
    have hyR : R ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
    have hyX : X0 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
    have hy0 : 0 ≤ y := le_trans (le_max_right _ _) hy
    have hnz : ‖z‖ ≤ y + 2 := by
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 2 + y := by
          rw [hz]; gcongr; rw [abs_le]; constructor <;> linarith
        _ = y + 2 := by ring
    have hRz : R ≤ ‖z‖ := hyR.trans (hz ▸ Complex.abs_im_le_norm z)
    have hG := hR ‖z‖ hRz z rfl
    have h2 := hz2 z hzs.1.le
    have hfz : ‖f z‖ ≤ ‖G z‖ := by
      simp only [hf, norm_div, norm_pow]
      exact div_le_self (norm_nonneg _) (one_le_pow₀ h2)
    have hc0' : 0 ≤ c0 := by
      by_contra hneg
      push Not at hneg
      have hep : 0 < ‖Real.exp (‖z‖ ^ (β + ε))‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_pos _
      have : c0 * ‖Real.exp (‖z‖ ^ (β + ε))‖ < 0 := mul_neg_of_neg_of_pos hneg hep
      linarith [norm_nonneg (G z)]
    calc ‖f z‖ ≤ ‖G z‖ := hfz
      _ ≤ c0 * ‖Real.exp (‖z‖ ^ (β + ε))‖ := hG
      _ ≤ c0 * ‖Real.exp (1 * Real.exp (1 * |z.im|))‖ := by
          gcongr
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.2
          rw [hz, one_mul, one_mul, ← hk]
          calc ‖z‖ ^ k ≤ (y + 2) ^ k :=
                Real.rpow_le_rpow (norm_nonneg _) hnz (by linarith)
            _ ≤ Real.exp y := hX0 y hyX
  have hdc : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo (-1) 2) := by
    apply DifferentiableOn.diffContOnCl
    have hcl : closure (Complex.re ⁻¹' Set.Ioo (-1 : ℝ) 2) ⊆ Complex.re ⁻¹' Set.Icc (-1) 2 :=
      closure_minimal (Set.preimage_mono Set.Ioo_subset_Icc_self)
        (isClosed_Icc.preimage Complex.continuous_re)
    intro z hz
    have hz' := hcl hz
    simp only [Set.mem_preimage, Set.mem_Icc] at hz'
    have hne : (z + 2) ^ m ≠ 0 := by
      apply pow_ne_zero
      intro h0
      have := hz2 z hz'.1
      rw [h0, norm_zero] at this
      linarith
    exact ((hGd z).div ((differentiableAt_id.add_const 2).pow m) hne).differentiableWithinAt
  have hPL : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖f z‖ ≤ 4 ^ m * K := fun z h1 h2 =>
    PhragmenLindelof.vertical_strip hdc hgrowth (fun z hz => hbd z (Or.inl hz))
      (fun z hz => hbd z (Or.inr hz)) h1 h2
  refine ⟨4 ^ m * K * 4 ^ m, fun z h1 h2 h3 => ?_⟩
  have hz1 : z ≠ 1 := by rintro rfl; norm_num at h3
  have hzn : 1 ≤ ‖z - 1‖ := by
    calc (1 : ℝ) ≤ |(z - 1).im| := by
          rw [Complex.sub_im, Complex.one_im, sub_zero, abs_of_nonneg (by linarith)]; exact h3
      _ ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
  have h4 : ‖z + 2‖ ≤ 4 * ‖z - 1‖ := by
    calc ‖z + 2‖ = ‖(z - 1) + 3‖ := by ring_nf
      _ ≤ ‖z - 1‖ + ‖(3 : ℂ)‖ := norm_add_le _ _
      _ ≤ 4 * ‖z - 1‖ := by norm_num; linarith
  have hfz := hPL z h1 h2
  have h2' := hz2 z h1
  simp only [hf, hGF z hz1, norm_div, norm_mul, norm_pow] at hfz
  rw [div_le_iff₀ (by positivity)] at hfz
  have hpos : 0 < ‖z - 1‖ ^ m := by positivity
  rw [← mul_le_mul_iff_of_pos_left hpos]
  calc ‖z - 1‖ ^ m * ‖F z‖ ≤ 4 ^ m * K * ‖z + 2‖ ^ m := hfz
    _ ≤ 4 ^ m * K * (4 * ‖z - 1‖) ^ m := by gcongr
    _ = ‖z - 1‖ ^ m * (4 ^ m * K * 4 ^ m) := by ring

/-- Moving a vertical mean value from `Re s = 2` to `Re s = -1` across a rectangle in
`Im s ≥ 1`, for a function bounded and holomorphic on that half-strip. -/
private theorem norm_mean_line_two_sub_line_neg_one_le (h : ℂ → ℂ) (M : ℝ)
    (hd : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 1 ≤ z.im → DifferentiableAt ℂ h z)
    (hM : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 1 ≤ z.im → ‖h z‖ ≤ M) :
    Filter.Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ((∫ y in (1 : ℝ)..T, h (2 + y * Complex.I)) -
      ∫ y in (1 : ℝ)..T, h (-1 + y * Complex.I))) Filter.atTop (nhds 0) := by
  have key : ∀ T : ℝ, 1 ≤ T → ‖(∫ y in (1 : ℝ)..T, h (2 + y * Complex.I)) -
      ∫ y in (1 : ℝ)..T, h (-1 + y * Complex.I)‖ ≤ 6 * M := by
    intro T hT
    have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn h ⟨-1, 1⟩ ⟨2, T⟩ ?_
    · simp only [smul_eq_mul] at H
      push_cast at H
      have e : Complex.I * ((∫ y in (1 : ℝ)..T, h (2 + y * Complex.I)) -
          ∫ y in (1 : ℝ)..T, h (-1 + y * Complex.I)) =
          (∫ x in (-1 : ℝ)..2, h (x + T * Complex.I)) -
            ∫ x in (-1 : ℝ)..2, h (x + 1 * Complex.I) := by
        linear_combination H
      have hn : ‖(∫ y in (1 : ℝ)..T, h (2 + y * Complex.I)) -
          ∫ y in (1 : ℝ)..T, h (-1 + y * Complex.I)‖ =
          ‖Complex.I * ((∫ y in (1 : ℝ)..T, h (2 + y * Complex.I)) -
          ∫ y in (1 : ℝ)..T, h (-1 + y * Complex.I))‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      rw [hn, e]
      have hbd : ∀ t : ℝ, 1 ≤ t → ‖∫ x in (-1 : ℝ)..2, h (x + t * Complex.I)‖ ≤ 3 * M := by
        intro t ht
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -1) (b := 2) (C := M)
          (f := fun x : ℝ => h (x + t * Complex.I)) (fun x hx => by
            rw [Set.uIoc_of_le (by norm_num)] at hx
            apply hM <;> simp <;> linarith [hx.1, hx.2])
        norm_num at this
        linarith
      calc ‖(∫ x in (-1 : ℝ)..2, h (x + T * Complex.I)) -
            ∫ x in (-1 : ℝ)..2, h (x + 1 * Complex.I)‖
          ≤ ‖∫ x in (-1 : ℝ)..2, h (x + T * Complex.I)‖ +
            ‖∫ x in (-1 : ℝ)..2, h (x + 1 * Complex.I)‖ := norm_sub_le _ _
        _ ≤ 3 * M + 3 * M := by
            gcongr
            · exact hbd T hT
            · have := hbd 1 le_rfl; push_cast at this; exact this
        _ = 6 * M := by ring
    · intro z hz
      simp only [Complex.mem_reProdIm, Set.uIcc_of_le (show (-1 : ℝ) ≤ 2 by norm_num),
        Set.uIcc_of_le hT, Set.mem_Icc] at hz
      exact (hd z hz.1.1 hz.1.2 hz.2.1).differentiableWithinAt
  have hlim : Filter.Tendsto (fun T : ℝ => 6 * M * T⁻¹) Filter.atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (6 * M)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with T hT
  have hT0 : 0 < T := by linarith
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0, mul_comm]
  exact mul_le_mul_of_nonneg_right (key T hT) (inv_nonneg.2 hT0.le)

/-- Rewrite a positive real base as an exponential: `x ^ z = exp (z log x)`. -/
private theorem ofReal_cpow_eq_exp (x : ℝ) (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = Complex.exp (z * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le, mul_comm]

/-- The integrand on the line `Re s = 2` as a trigonometric series. -/
private theorem LSeries_mul_cpow_line_two (a : ArithmeticFunction ℂ) (n : ℕ) (hn : n ≠ 0) (y : ℝ) :
    LSeries (fun k => a k) (2 + y * Complex.I) * (n : ℂ) ^ (2 + y * Complex.I) =
      ∑' k : ℕ, (if k = 0 then 0 else
        a k * Complex.exp (2 * ((Real.log n - Real.log k : ℝ) : ℂ))) *
        Complex.exp ((((Real.log n - Real.log k) * y : ℝ) : ℂ) * Complex.I) := by
  rw [LSeries, ← tsum_mul_right]
  apply tsum_congr
  intro k
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rw [LSeries.term_of_ne_zero hk, ite_eq_right hk]
  have ek : (k : ℂ) = ((k : ℝ) : ℂ) := by push_cast; rfl
  have en : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; rfl
  rw [ek, en, ofReal_cpow_eq_exp _ (by positivity), ofReal_cpow_eq_exp _ (by positivity),
    div_eq_mul_inv, ← Complex.exp_neg, mul_assoc, ← Complex.exp_add, mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The integrand on the line `Re s = -1`, rewritten through the functional equation, as a
trigonometric series. -/
private theorem mul_cpow_line_neg_one (a : ArithmeticFunction ℂ) (Q : ℝ) (hQ : 0 < Q) (w : ℂ)
    (n : ℕ) (hn : n ≠ 0) (y : ℝ) (X : ℂ)
    (hX : (Q : ℂ) ^ (-1 + y * Complex.I) * X = w * starRingEnd ℂ
      ((Q : ℂ) ^ (2 + y * Complex.I) * LSeries (fun k => a k) (2 + y * Complex.I))) :
    X * (n : ℂ) ^ (-1 + y * Complex.I) =
      ∑' k : ℕ, (if k = 0 then 0 else w * starRingEnd ℂ (a k) *
        Complex.exp (((3 * Real.log Q - Real.log n - 2 * Real.log k : ℝ) : ℂ))) *
        Complex.exp ((((Real.log n + Real.log k - 2 * Real.log Q) * y : ℝ) : ℂ) *
          Complex.I) := by
  have hQs : (Q : ℂ) ^ (-1 + y * Complex.I) ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
      intro h; simpa using congrArg Complex.re h)).2 (by exact_mod_cast hQ.ne')
  have hX' : X = w * starRingEnd ℂ ((Q : ℂ) ^ (2 + y * Complex.I)) *
      (starRingEnd ℂ (LSeries (fun k => a k) (2 + y * Complex.I))) /
      (Q : ℂ) ^ (-1 + y * Complex.I) := by
    rw [eq_div_iff hQs, mul_comm X, hX, map_mul]; ring
  rw [hX', LSeries, Complex.conj_tsum]
  rw [show ∀ A B C D E : ℂ, A * B * C / D * E = C * (A * B * E / D) from
    fun A B C D E => by ring, ← tsum_mul_right]
  apply tsum_congr
  intro k
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rw [LSeries.term_of_ne_zero hk, ite_eq_right hk]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have e : ∀ x : ℝ, 0 < x → ∀ s : ℂ, (x : ℂ) ^ s = Complex.exp (Real.log x * s) :=
    fun x hx s => by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]
  rw [← Complex.ofReal_natCast k, ← Complex.ofReal_natCast n, e _ hk0, e _ hn0, e _ hQ, e _ hQ,
    map_div₀, ← Complex.exp_conj, ← Complex.exp_conj]
  calc _ = w * starRingEnd ℂ (a k) *
        (Complex.exp (starRingEnd ℂ (Real.log Q * (2 + y * Complex.I))) *
          Complex.exp (Real.log n * (-1 + y * Complex.I)) *
          (Complex.exp (Real.log Q * (-1 + y * Complex.I)))⁻¹ *
          (Complex.exp (starRingEnd ℂ (Real.log k * (2 + y * Complex.I))))⁻¹) := by ring
    _ = _ := by
      rw [← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add,
        ← Complex.exp_add, mul_assoc (w * starRingEnd ℂ (a k)), ← Complex.exp_add]
      congr 2
      apply Complex.ext <;> simp [Complex.log_im] <;> ring

/-- The analytic half of Conrey–Ghosh: comparing mean values on `Re s = 2` and `Re s = -1`
expresses each `a n` through the coefficients of the reflected series. -/
private theorem apply_eq_tsum_of_gammaFree_functionalEquation (a : ArithmeticFunction ℂ)
    (F G : ℂ → ℂ) (m : ℕ) (β : ℝ)
    (hF : IsLSeriesContinuation a F)
    (hsum : ∀ s : ℂ, 3 / 2 < s.re → LSeriesSummable (fun n => a n) s)
    (hGd : Differentiable ℂ G) (hGo : Complex.HasGrowthOrderLE G β)
    (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s) (Q : ℝ) (hQ : 0 < Q) (w : ℂ) (hw : ‖w‖ = 1)
    (heqn : ∀ s : ℂ, 0 < s.re → s.re < 1 → (Q : ℂ) ^ s * F s =
      w * starRingEnd ℂ ((Q : ℂ) ^ (1 - starRingEnd ℂ s) * F (1 - starRingEnd ℂ s)))
    (n : ℕ) (hn : n ≠ 0) :
    a n = ∑' k : ℕ, if Real.log n + Real.log k - 2 * Real.log Q = 0 then
      (if k = 0 then 0 else w * starRingEnd ℂ (a k) *
        Complex.exp (((3 * Real.log Q - Real.log n - 2 * Real.log k : ℝ) : ℂ))) else 0 := by
  have hFd : ∀ s, s ≠ 1 → DifferentiableAt ℂ F s := fun s hs =>
    hF.2.differentiableAt (isOpen_compl_singleton.mem_nhds hs)
  set Φ : ℂ → ℂ := fun s => (Q : ℂ) ^ s * F s with hΦ
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hΦd : ∀ s, s ≠ 1 → DifferentiableAt ℂ Φ s := fun s hs =>
    (differentiableAt_id.const_cpow (Or.inl hQ0)).mul (hFd s hs)
  set Ψ : ℂ → ℂ := fun s => w * starRingEnd ℂ (Φ (starRingEnd ℂ (1 - s))) with hΨ
  have hΨd : ∀ s, s ≠ 0 → DifferentiableAt ℂ Ψ s := by
    intro s hs
    have hne : starRingEnd ℂ (1 - s) ≠ 1 := by
      intro h
      apply hs
      have : 1 - s = 1 := by
        have := congrArg (starRingEnd ℂ) h
        simpa using this
      linear_combination -this
    have h1 : DifferentiableAt ℂ (starRingEnd ℂ ∘ Φ ∘ starRingEnd ℂ) (1 - s) := by
      have := (hΦd _ hne).conj_conj
      simpa using this
    have h2 : DifferentiableAt ℂ (fun s : ℂ => 1 - s) s :=
      (differentiableAt_const 1).sub differentiableAt_id
    exact (h1.comp s h2).const_mul w
  have hext : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Φ s = Ψ s := by
    set U : Set ℂ := ({0, 1} : Set ℂ)ᶜ with hU
    have hUo : IsOpen U := (Set.toFinite ({0, 1} : Set ℂ)).isClosed.isOpen_compl
    have hpc : IsPreconnected U :=
      (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
        (Set.toFinite ({0, 1} : Set ℂ)).countable).isPreconnected
    have hmem : ∀ s, s ∈ U ↔ s ≠ 0 ∧ s ≠ 1 := by intro s; simp [hU]
    have hΦa : AnalyticOnNhd ℂ Φ U := DifferentiableOn.analyticOnNhd
      (fun z hz => (hΦd z ((hmem z).1 hz).2).differentiableWithinAt) hUo
    have hΨa : AnalyticOnNhd ℂ Ψ U := DifferentiableOn.analyticOnNhd
      (fun z hz => (hΨd z ((hmem z).1 hz).1).differentiableWithinAt) hUo
    have hloc : Φ =ᶠ[nhds (1 / 2 : ℂ)] Ψ := by
      have hstrip : {s : ℂ | 0 < s.re ∧ s.re < 1} ∈ nhds (1 / 2 : ℂ) :=
        ((isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds (by norm_num)
      filter_upwards [hstrip] with s hs
      simp only [hΦ, hΨ, map_sub, map_one]
      exact heqn s hs.1 hs.2
    intro s h0 h1
    exact hΦa.eqOn_of_preconnected_of_eventuallyEq hΨa hpc ((hmem _).2 (by norm_num)) hloc
      ((hmem s).2 ⟨h0, h1⟩)
  -- bounds on the two boundary lines
  have hsum2 : Summable (fun k => ‖LSeries.term (fun n => a n) 2 k‖) :=
    (hsum 2 (by norm_num)).norm
  set K : ℝ := ∑' k, ‖LSeries.term (fun n => a n) 2 k‖ with hK
  have hK2 : ∀ s : ℂ, s.re = 2 → ‖F s‖ ≤ K := by
    intro s hs
    rw [hF.1 s (by rw [hs]; norm_num), LSeries]
    have hsm : Summable (fun k => ‖LSeries.term (fun n => a n) s k‖) :=
      (hsum s (by rw [hs]; norm_num)).norm
    refine (norm_tsum_le_tsum_norm hsm).trans (le_of_eq ?_)
    apply tsum_congr
    intro k
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hs]
    simp
  have hK0 : 0 ≤ K := tsum_nonneg (fun _ => norm_nonneg _)
  have hKm1 : ∀ s : ℂ, s.re = -1 → ‖F s‖ ≤ Q ^ 3 * K := by
    intro s hs
    have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
    have e := congrArg norm (hext s h0 h1)
    simp only [hΦ, hΨ, norm_mul, Complex.norm_conj, hw, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ] at e
    have hre : (starRingEnd ℂ (1 - s)).re = 2 := by
      simp only [map_sub, map_one, Complex.sub_re, Complex.one_re, Complex.conj_re, hs]
      norm_num
    rw [hs, hre] at e
    have hb := hK2 _ hre
    have e' : ‖F s‖ = Q ^ 3 * ‖F (starRingEnd ℂ (1 - s))‖ := by
      rw [Real.rpow_neg_one, Real.rpow_two] at e
      field_simp at e
      linear_combination e
    rw [e']
    gcongr
  obtain ⟨M, hM⟩ := exists_bound_strip_of_bound_lines F G m β hGd hGo hGF (max K (Q ^ 3 * K)) (fun s
      hs => by
    rcases hs with h | h
    · exact (hKm1 s h).trans (le_max_right _ _)
    · exact (hK2 s h).trans (le_max_left _ _))
  -- the function `F(s) n^s` and the line shift
  set h : ℂ → ℂ := fun s => F s * (n : ℂ) ^ s with hh
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have hhd : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 1 ≤ z.im → DifferentiableAt ℂ h z := by
    intro z _ _ h3
    have hz1 : z ≠ 1 := by rintro rfl; norm_num at h3
    exact (hFd z hz1).mul (differentiableAt_id.const_cpow (Or.inl hn0))
  have en : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; rfl
  have hhM : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 1 ≤ z.im → ‖h z‖ ≤ M * (n : ℝ) ^ (2 : ℝ) := by
    intro z h1 h2 h3
    simp only [hh, norm_mul]
    rw [en, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    exact mul_le_mul (hM z h1 h2 h3) (Real.rpow_le_rpow_of_exponent_le hn1 h2) (by positivity)
      ((norm_nonneg _).trans (hM z h1 h2 h3))
  have hshift := norm_mean_line_two_sub_line_neg_one_le h _ hhd hhM
  -- the line `Re s = 2`
  set ω2 : ℕ → ℝ := fun k => Real.log n - Real.log k with hω2
  set u2 : ℕ → ℂ := fun k => if k = 0 then 0 else
    a k * Complex.exp (2 * ((Real.log n - Real.log k : ℝ) : ℂ)) with hu2
  have hu2s : Summable (fun k => ‖u2 k‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      (hsum2.mul_left (Real.exp (Real.log n * 2)))
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hu2]
    · apply le_of_eq
      have hk0 : (0 : ℝ) < k := by positivity
      simp only [hu2, ite_eq_right hk, norm_mul, Complex.norm_exp, LSeries.norm_term_eq]
      rw [Real.rpow_def_of_pos hk0]
      simp only [Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.im_ofNat, mul_zero, sub_zero]
      rw [show 2 * (Real.log n - Real.log k) = Real.log n * 2 - Real.log k * 2 by ring,
        Real.exp_sub]
      ring
  have hfun2 : ∀ y : ℝ, h (2 + y * Complex.I) =
      ∑' k, u2 k * Complex.exp (((ω2 k * y : ℝ) : ℂ) * Complex.I) := by
    intro y
    simp only [hh]
    rw [hF.1 _ (by simp), LSeries_mul_cpow_line_two a n hn y]
  have hMV2 := tendsto_average_tsum_exp_mul_I u2 ω2 hu2s
  have hL2 : (∑' k, if ω2 k = 0 then u2 k else 0) = a n := by
    rw [tsum_eq_single n]
    · simp [hω2, hu2, hn]
    · intro k hkn
      rcases eq_or_ne k 0 with rfl | hk
      · simp [hu2]
      · have : ω2 k ≠ 0 := by
          simp only [hω2]
          intro h0
          apply hkn
          have := Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity : (0 : ℝ) < k))
            (Set.mem_Ioi.2 (by positivity : (0 : ℝ) < n)) (by linarith)
          exact_mod_cast this
        simp [this]
  -- the line `Re s = -1`
  set ω1 : ℕ → ℝ := fun k => Real.log n + Real.log k - 2 * Real.log Q with hω1
  set u1 : ℕ → ℂ := fun k => if k = 0 then 0 else w * starRingEnd ℂ (a k) *
    Complex.exp (((3 * Real.log Q - Real.log n - 2 * Real.log k : ℝ) : ℂ)) with hu1
  have hu1s : Summable (fun k => ‖u1 k‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      (hsum2.mul_left (Real.exp (3 * Real.log Q - Real.log n)))
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hu1]
    · apply le_of_eq
      have hk0 : (0 : ℝ) < k := by positivity
      simp only [hu1, ite_eq_right hk, norm_mul, Complex.norm_exp, Complex.ofReal_re,
        Complex.norm_conj, hw, one_mul, LSeries.norm_term_eq]
      rw [Real.rpow_def_of_pos hk0]
      simp only [Complex.re_ofNat]
      rw [show 3 * Real.log Q - Real.log n - 2 * Real.log k =
        (3 * Real.log Q - Real.log n) - Real.log k * 2 by ring, Real.exp_sub]
      ring
  have hfun1 : ∀ y : ℝ, h (-1 + y * Complex.I) =
      ∑' k, u1 k * Complex.exp (((ω1 k * y : ℝ) : ℂ) * Complex.I) := by
    intro y
    simp only [hh]
    apply mul_cpow_line_neg_one a Q hQ w n hn y
    have hs0 : (-1 + y * Complex.I) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this
    have hs1 : (-1 + y * Complex.I) ≠ 1 := by
      intro h0; have := congrArg Complex.re h0; simp at this; norm_num at this
    have e := hext _ hs0 hs1
    have hc : starRingEnd ℂ (1 - (-1 + y * Complex.I)) = 2 + y * Complex.I := by
      apply Complex.ext <;> (simp; try norm_num)
    simp only [hΦ, hΨ, hc] at e
    rw [e, hF.1 _ (by simp)]
  have hMV1 := tendsto_average_tsum_exp_mul_I u1 ω1 hu1s
  simp only [hfun2, hfun1] at hshift
  have hlim := hMV2.sub hMV1
  have hlim' : Filter.Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
      ((∫ y in (1 : ℝ)..T, ∑' k, u2 k * Complex.exp (((ω2 k * y : ℝ) : ℂ) * Complex.I)) -
        ∫ y in (1 : ℝ)..T, ∑' k, u1 k * Complex.exp (((ω1 k * y : ℝ) : ℂ) * Complex.I)))
      Filter.atTop (nhds ((∑' k, if ω2 k = 0 then u2 k else 0) -
        ∑' k, if ω1 k = 0 then u1 k else 0)) := by
    refine hlim.congr (fun T => ?_)
    ring
  have hfin := tendsto_nhds_unique hlim' hshift
  rw [← hL2]
  exact sub_eq_zero.1 hfin





/-- **Conrey–Ghosh.** If `a ∈ 𝒮` has continuation `F` with a functional equation of degree `0`,
then `a = 1`. -/
theorem eq_one_of_degree_eq_zero {a : ArithmeticFunction ℂ} {F : ℂ → ℂ}
    (ha : a ∈ selbergClass) (hF : IsLSeriesContinuation a F) (D : FunctionalEquation F) (hD :
        D.degree = 0) :
    a = 1 := by
  classical
  obtain ⟨ha1, ⟨F₀, hF₀, ⟨m, G, β, hGd, hGo, hGF₀⟩, _⟩, ⟨b, θ, hθ, hlog, Cb, hbC⟩, hram⟩ := ha
  obtain ⟨Ca, hCa⟩ := hram (1 / 2) (by norm_num)
  have hsum : ∀ s : ℂ, 3 / 2 < s.re → LSeriesSummable (fun n => a n) s := fun s hs =>
    LSeriesSummable_of_le_const_mul_rpow hs ⟨Ca, fun n _ => by
      have := hCa n; convert this using 3; norm_num⟩
  have habs : LSeries.abscissaOfAbsConv (fun n => a n) ≤ (2 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      hsum y (by simp only [Complex.ofReal_re]; linarith)
  have hFF₀ : ∀ s, s ≠ 1 → F s = F₀ s := hF.eqOn_compl_one hF₀
  have hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s := fun s hs => by
    rw [hFF₀ s hs]; exact hGF₀ s hs
  obtain ⟨d, Q, α, r, w, hQ, hα, hr, hw, heqn⟩ := D
  have hd : d = 0 := by
    by_contra hd
    have hpos : 0 < ∑ i, α i := Finset.sum_pos (fun i _ => hα i)
      (Finset.univ_nonempty_iff.2 ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩)
    simp only [FunctionalEquation.degree] at hD
    linarith
  subst hd
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at heqn
  have key := apply_eq_tsum_of_gammaFree_functionalEquation a F G m β hF hsum hGd hGo hGF Q hQ w hw
      heqn
  -- the frequency `Q ^ 2` is an integer `q`
  have h1 := key 1 one_ne_zero
  rw [ha1] at h1
  obtain ⟨q, hq0, hqQ⟩ : ∃ q : ℕ, q ≠ 0 ∧
      Real.log ((1 : ℕ) : ℝ) + Real.log q - 2 * Real.log Q = 0 := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ k : ℕ, (if Real.log ((1 : ℕ) : ℝ) + Real.log k - 2 * Real.log Q = 0 then
        (if k = 0 then 0 else w * starRingEnd ℂ (a k) *
          Complex.exp (((3 * Real.log Q - Real.log ((1 : ℕ) : ℝ) - 2 * Real.log k : ℝ) : ℂ)))
        else 0) = 0 := by
      intro k
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · rw [ite_eq_right (hcon k hk)]
    simp only [hz, tsum_zero] at h1
    exact one_ne_zero h1
  have hqR : (q : ℝ) = Q ^ 2 := by
    have hlq : Real.log q = Real.log (Q ^ 2) := by
      rw [Real.log_pow]; push_cast at hqQ ⊢; simp at hqQ; linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) hlq
  have hlogeq : ∀ n k : ℕ, n ≠ 0 → k ≠ 0 →
      (Real.log n + Real.log k - 2 * Real.log Q = 0 ↔ n * k = q) := by
    intro n k hn hk
    have h2 : 2 * Real.log Q = Real.log q := by rw [hqR, Real.log_pow]; push_cast; ring
    rw [h2, ← Real.log_mul (by positivity) (by positivity), sub_eq_zero]
    constructor
    · intro h
      have := Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity))
        (Set.mem_Ioi.2 (by positivity)) h
      exact_mod_cast this
    · intro h; rw [← h]; push_cast; rfl
  -- `a` is supported on the divisors of `q`
  have hsupp : ∀ n, ¬ n ∣ q → a n = 0 := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · exact a.map_zero
    rw [key n hn0]
    have hz : ∀ k : ℕ, (if Real.log n + Real.log k - 2 * Real.log Q = 0 then
        (if k = 0 then 0 else w * starRingEnd ℂ (a k) *
          Complex.exp (((3 * Real.log Q - Real.log n - 2 * Real.log k : ℝ) : ℂ)))
        else 0) = 0 := by
      intro k
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · rw [ite_eq_right]
        rw [hlogeq n k hn0 hk]
        rintro rfl
        exact hn (Dvd.intro k rfl)
    simp only [hz, tsum_zero]
  -- `|a q| = Q = √q`
  have haq : ‖a q‖ = Real.sqrt q := by
    rw [tsum_eq_single q] at h1
    · rw [ite_eq_left (by simpa using (hlogeq 1 q one_ne_zero hq0).2 (one_mul q)), ite_eq_right hq0]
        at h1
      have e := congrArg norm h1
      rw [norm_one, norm_mul, norm_mul, hw, one_mul, Complex.norm_conj, Complex.norm_exp,
        Complex.ofReal_re] at e
      have hlq : Real.log q = 2 * Real.log Q := by rw [hqR, Real.log_pow]; push_cast; ring
      rw [hlq, Nat.cast_one, Real.log_one,
        show 3 * Real.log Q - 0 - 2 * (2 * Real.log Q) = -Real.log Q by ring,
        Real.exp_neg, Real.exp_log hQ] at e
      rw [hqR, Real.sqrt_sq hQ.le]
      field_simp at e
      linarith
    · intro k hk
      rcases eq_or_ne k 0 with rfl | hk0
      · simp
      · rw [ite_eq_right]
        rw [hlogeq 1 k one_ne_zero hk0, one_mul]
        exact hk
  rcases Nat.lt_or_ge q 2 with hq | hq
  · -- `q = 1`
    have hq1 : q = 1 := by omega
    subst hq1
    ext n
    rw [ArithmeticFunction.one_apply]
    split_ifs with hn
    · rw [hn, ha1]
    · exact hsupp n (fun h => hn (Nat.dvd_one.1 h))
  · exact (false_of_isEulerLog_of_support_dvd a b θ Cb hθ hlog hbC habs ha1 q hq hsupp haq).elim


end SelbergClass
