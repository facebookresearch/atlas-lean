/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeCounting.MertensFunctionBound
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import MathlibExt.NumberTheory.ArithmeticFunction.DirichletHyperbola

/-!
# Summatory functions of `μ * μ` and of `μ d`

From the bound `M(x) = O(x exp(-c (log x)^{1/10}))` for the Mertens function we deduce the
same quality of bound for two related summatory functions.

## Main statements

* `ArithmeticFunction.sum_moebius_mul_moebius_isBigO_mul_exp_neg_mul_log_rpow`: the
  summatory function of the Dirichlet convolution `μ * μ` (the coefficients of `1 / ζ(s)²`)
  is `O(x exp(-c (log x)^{1/10}))`, by Dirichlet's hyperbola method at `y = √x`.
* `ArithmeticFunction.sum_moebius_mul_sigma_zero_isBigO_mul_exp_neg_mul_log_rpow`:
  `∑_{n ≤ x} μ(n) d(n) = O(x exp(-c (log x)^{1/10}))`, writing `μ d = (μ * μ) * h` with
  `∑ |h(n)| n^{-3/4} < ∞`.
-/

@[expose] public section

open Asymptotics Filter

namespace ArithmeticFunction

/-- **The summatory function of `μ * μ`.** The Dirichlet convolution `μ * μ`, whose
Dirichlet series is `1 / ζ(s) ^ 2`, satisfies
`∑_{n ≤ x} (μ * μ)(n) = O(x exp(-c (log x) ^ (1 / 10)))` for some `c > 0`. -/
theorem sum_moebius_mul_moebius_isBigO_mul_exp_neg_mul_log_rpow :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (((ArithmeticFunction.moebius * ArithmeticFunction.moebius) n : ℤ) : ℝ))
        =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) := by
  classical
  set Mr : ℝ → ℝ := fun y => ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ)
    with hMr
  have htriv : ∀ y : ℝ, 0 ≤ y → |Mr y| ≤ y := by
    intro y hy
    calc |Mr y| ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, |((ArithmeticFunction.moebius n : ℤ) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [← Int.cast_abs]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      _ = (⌊y⌋₊ : ℝ) := by simp
      _ ≤ y := Nat.floor_le hy
  -- ## Step 1: Dirichlet's hyperbola method at `y = √x`
  have hhyp : ∀ x : ℝ, 0 < x → ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      (((ArithmeticFunction.moebius * ArithmeticFunction.moebius) n : ℤ) : ℝ)
      = ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Mr (x / d)
        + ∑ e ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
            ((ArithmeticFunction.moebius e : ℤ) : ℝ) * Mr (x / e)
        - Mr (Real.sqrt x) * Mr (Real.sqrt x) := by
    intro x hx
    have hI : ∀ n : ℕ, Finset.Ioc 0 n = Finset.Icc 1 n := fun n => by ext; simp; omega
    have h := sum_Ioc_mul_eq_hyperbola (moebius : ArithmeticFunction ℝ)
      (moebius : ArithmeticFunction ℝ) x (Real.sqrt_pos.2 hx)
    simp only [← intCoe_mul, intCoe_apply, hI, Real.div_sqrt] at h
    rw [h]
    simp only [hMr]
    congr 2
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  -- ## Step 2: insert the bound for the Mertens function
  obtain ⟨c, hc, hM⟩ := sum_moebius_isBigO_mul_exp_neg_mul_log_rpow
  obtain ⟨C, hC, hCw⟩ := hM.exists_pos
  obtain ⟨y0, hy0⟩ := eventually_atTop.1 (isBigOWith_iff.1 hCw)
  have hc4 : (0 : ℝ) < c / 4 := by positivity
  -- `u ≤ A * exp ((c / 4) * u ^ (1 / 10))` absorbs the harmonic `log x`
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ, 0 ≤ u →
      u ≤ A * Real.exp (c / 4 * u ^ (1 / 10 : ℝ)) := by
    refine ⟨(Nat.factorial 10 : ℝ) / (c / 4) ^ 10, by positivity, fun u hu => ?_⟩
    have hv0 : (0 : ℝ) ≤ u ^ (1 / 10 : ℝ) := Real.rpow_nonneg hu _
    have hav : (0 : ℝ) ≤ c / 4 * u ^ (1 / 10 : ℝ) := mul_nonneg hc4.le hv0
    have hfn : (0 : ℝ) < (Nat.factorial 10 : ℝ) := by exact_mod_cast Nat.factorial_pos 10
    have h := Real.pow_div_factorial_le_exp _ hav 10
    have h10 : (u ^ (1 / 10 : ℝ)) ^ (10 : ℕ) = u := by
      rw [← Real.rpow_natCast (u ^ (1 / 10 : ℝ)) 10, ← Real.rpow_mul hu]
      norm_num
    rw [mul_pow, h10, div_le_iff₀ hfn] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc4 10)]
    linarith
  refine ⟨c / 4, hc4, ?_⟩
  refine IsBigO.of_bound (C * (3 + 2 * A)) ?_
  filter_upwards [eventually_ge_atTop (max (max y0 1 ^ 2) (Real.exp 1))] with x hx
  have hxe : Real.exp 1 ≤ x := le_of_max_le_right hx
  have hxm : max y0 1 ^ 2 ≤ x := le_of_max_le_left hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  rw [hhyp x hxpos]
  set L := Real.log x with hL
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hxe
  set s := Real.sqrt x with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hxpos
  have hss : s * s = x := Real.mul_self_sqrt hxpos.le
  have hsm : max y0 1 ≤ s := by
    rw [hs, Real.le_sqrt (by positivity) hxpos.le]
    exact hxm
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hsm
  have hy0s : y0 ≤ s := le_trans (le_max_left _ _) hsm
  have hlogs : Real.log s = L / 2 := by
    rw [hs, Real.log_sqrt hxpos.le]
  set E2 := Real.exp (-(c / 2) * L ^ (1 / 10 : ℝ)) with hE2
  set E := Real.exp (-(c / 4) * L ^ (1 / 10 : ℝ)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE2pos : 0 < E2 := Real.exp_pos _
  -- the bound for the Mertens function above `s`
  have hbig : ∀ y : ℝ, s ≤ y → |Mr y| ≤ C * y * E2 := by
    intro y hy
    have hy1 : 1 ≤ y := le_trans hs1 hy
    have hypos : 0 < y := by linarith
    have hb := hy0 y (le_trans hy0s hy)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (mul_pos hypos (Real.exp_pos _))] at hb
    have hlogy : L / 2 ≤ Real.log y := by
      rw [← hlogs]
      exact Real.log_le_log hspos hy
    have hexp : Real.exp (-c * Real.log y ^ (1 / 10 : ℝ)) ≤ E2 := by
      rw [hE2, Real.exp_le_exp]
      have h1 : (L / 2) ^ (1 / 10 : ℝ) ≤ Real.log y ^ (1 / 10 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hlogy (by norm_num)
      have h2 : (L / 2) ^ (1 / 10 : ℝ) = L ^ (1 / 10 : ℝ) / 2 ^ (1 / 10 : ℝ) :=
        Real.div_rpow (by linarith) (by norm_num) _
      have h3 : (2 : ℝ) ^ (1 / 10 : ℝ) ≤ 2 := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 / 10 : ℝ) ≤ 1)
        simpa using this
      have h3pos : (0 : ℝ) < 2 ^ (1 / 10 : ℝ) := by positivity
      have hLr : 0 ≤ L ^ (1 / 10 : ℝ) := by positivity
      have h4 : L ^ (1 / 10 : ℝ) / 2 ≤ L ^ (1 / 10 : ℝ) / 2 ^ (1 / 10 : ℝ) :=
        div_le_div_of_nonneg_left hLr h3pos h3
      nlinarith
    calc |Mr y| ≤ C * (y * Real.exp (-c * Real.log y ^ (1 / 10 : ℝ))) := hb
      _ ≤ C * (y * E2) := by gcongr
      _ = C * y * E2 := by ring
  -- the harmonic sum up to `√x`
  set K := ⌊s⌋₊ with hK
  have hK1 : 1 ≤ K := Nat.le_floor (by simpa using hs1)
  have hKs : (K : ℝ) ≤ s := Nat.floor_le hspos.le
  have hharm : ∑ d ∈ Finset.Icc 1 K, ((d : ℝ))⁻¹ ≤ 1 + L := by
    have h1 := harmonic_le_one_add_log K
    rw [harmonic_eq_sum_Icc] at h1
    push_cast at h1
    have h2 : Real.log K ≤ L := by
      calc Real.log K ≤ Real.log s := Real.log_le_log (Nat.cast_pos.2 hK1) hKs
        _ = L / 2 := hlogs
        _ ≤ L := by linarith
    linarith
  have hsum : |∑ d ∈ Finset.Icc 1 K, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Mr (x / d)|
      ≤ C * x * E2 * (1 + L) := by
    calc _ ≤ ∑ d ∈ Finset.Icc 1 K, |((ArithmeticFunction.moebius d : ℤ) : ℝ) * Mr (x / d)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 K, C * x * E2 * ((d : ℝ))⁻¹ := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.1 hd).1
          have hdK : (d : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.1 hd).2
          have hdpos : (0 : ℝ) < d := by linarith
          have hsd : s ≤ x / d := by
            rw [le_div_iff₀ hdpos]
            nlinarith
          have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
            rw [← Int.cast_abs]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          rw [abs_mul]
          calc |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |Mr (x / d)|
              ≤ 1 * (C * (x / d) * E2) :=
                mul_le_mul hmu (hbig _ hsd) (abs_nonneg _) zero_le_one
            _ = C * x * E2 * ((d : ℝ))⁻¹ := by ring
      _ = C * x * E2 * ∑ d ∈ Finset.Icc 1 K, ((d : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ C * x * E2 * (1 + L) := by gcongr
  have hsq : |Mr s * Mr s| ≤ C * x * E2 := by
    rw [abs_mul]
    calc |Mr s| * |Mr s| ≤ (C * s * E2) * s :=
          mul_le_mul (hbig s le_rfl) (htriv s hspos.le) (abs_nonneg _) (by positivity)
      _ = C * x * E2 := by rw [← hss]; ring
  -- absorbing `log x` into the exponent
  have hL0 : 0 ≤ L ^ (1 / 10 : ℝ) := Real.rpow_nonneg (by linarith) _
  have he1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hLe : L * E ≤ A := by
    have h := hA L (by linarith)
    have hprod : Real.exp (c / 4 * L ^ (1 / 10 : ℝ)) * E = 1 := by
      rw [hE, ← Real.exp_add, ← Real.exp_zero]
      congr 1
      ring
    calc L * E ≤ A * Real.exp (c / 4 * L ^ (1 / 10 : ℝ)) * E :=
          mul_le_mul_of_nonneg_right h hEpos.le
      _ = A := by rw [mul_assoc, hprod, mul_one]
  have hsplit : E2 = E * E := by
    rw [hE2, hE, ← Real.exp_add]
    congr 1
    ring
  have hfinal : (3 + 2 * L) * E2 ≤ (3 + 2 * A) * E := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left he1 hEpos.le, mul_le_mul_of_nonneg_left hLe hEpos.le]
  have hkey : C * x * ((3 + 2 * L) * E2) ≤ C * x * ((3 + 2 * A) * E) :=
    mul_le_mul_of_nonneg_left hfinal (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (mul_pos hxpos hEpos)]
  obtain ⟨h1, h2⟩ := abs_le.1 hsum
  obtain ⟨h3, h4⟩ := abs_le.1 hsq
  rw [abs_le]
  constructor <;> linarith

/-- **The summatory function of `μ d`.** There is `c > 0` with
`∑_{n ≤ x} μ(n) d(n) = O(x exp(-c (log x) ^ (1 / 10)))`, where `d = σ₀` counts divisors and
the product is pointwise. -/
theorem sum_moebius_mul_sigma_zero_isBigO_mul_exp_neg_mul_log_rpow :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ))
        =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) := by
  classical
  -- ## Step 1: `μ d = (μ * μ) * h` with `h = μ d * ζ * ζ`, and `h (p ^ k) = 1 - k`
  set g : ArithmeticFunction ℤ := ArithmeticFunction.moebius.pmul
    (((ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ)) : ArithmeticFunction ℤ) with hg
  set h : ArithmeticFunction ℤ := g * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)
    * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) with hh
  have hgm : g.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_moebius.pmul
      ArithmeticFunction.isMultiplicative_sigma.natCast
  have hhm : h.IsMultiplicative :=
    (hgm.mul ArithmeticFunction.isMultiplicative_zeta.natCast).mul
      ArithmeticFunction.isMultiplicative_zeta.natCast
  have hgp : ∀ p : ℕ, p.Prime → ∀ i : ℕ,
      g (p ^ i) = if i = 0 then 1 else if i = 1 then -2 else 0 := by
    intro p hp i
    rw [hg, ArithmeticFunction.pmul_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · rw [ArithmeticFunction.moebius_apply_prime_pow hp hi.ne']
      split_ifs <;> simp_all
  have hgz : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      (g * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) (p ^ k)
        = if k = 0 then 1 else -1 := by
    intro p hp k
    rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    induction k with
    | zero => simp [hgp p hp]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hgp p hp]
      rcases k with _ | k <;> simp
  have hhp : ∀ p : ℕ, p.Prime → ∀ k : ℕ, h (p ^ k) = 1 - k := by
    intro p hp k
    rw [hh, ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    induction k with
    | zero => simp [hgz p hp]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hgz p hp]
      simp; ring
  have hgah : g = h * (ArithmeticFunction.moebius * ArithmeticFunction.moebius) := by
    calc g = g * (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ))
          * (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) := by
          rw [ArithmeticFunction.moebius_mul_coe_zeta, mul_one, mul_one]
      _ = h * (ArithmeticFunction.moebius * ArithmeticFunction.moebius) := by rw [hh]; ring
  clear_value h g
  -- ## Step 2: `∑ |h n| n ^ (-3/4)` is bounded, through the Euler product
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ N : ℕ,
      ∑ n ∈ Finset.Icc 1 N, |((h n : ℤ) : ℝ)| * ((n : ℝ) ^ (3 / 4 : ℝ))⁻¹ ≤ S := by
    set F : ℕ → ℝ := fun n => |((h n : ℤ) : ℝ)| * ((n : ℝ) ^ (3 / 4 : ℝ))⁻¹ with hF
    have hF0 : ∀ n, 0 ≤ F n := fun n => by positivity
    have hF1 : F 1 = 1 := by simp [hF, hhm.map_one]
    have hFm : ∀ {m n : ℕ}, m.Coprime n → F (m * n) = F m * F n := by
      intro m n hmn
      simp only [hF, hhm.map_mul_of_coprime hmn, Nat.cast_mul, Int.cast_mul, abs_mul,
        Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), mul_inv]
      ring
    have hFp : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
        F (p ^ k) = |1 - (k : ℝ)| * ((p : ℝ) ^ (3 / 4 : ℝ))⁻¹ ^ k := by
      intro p hp k
      simp only [hF, hhp p hp k, Nat.cast_pow]
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p),
        Real.inv_rpow (Real.rpow_nonneg (Nat.cast_nonneg p) _),
        ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm (k : ℝ) (3 / 4)]
    have hr : ∀ p : ℕ, p.Prime →
        0 ≤ ((p : ℝ) ^ (3 / 4 : ℝ))⁻¹ ∧ ((p : ℝ) ^ (3 / 4 : ℝ))⁻¹ ≤ 3 / 5 := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      set r := ((p : ℝ) ^ (3 / 4 : ℝ))⁻¹ with hr
      have hr0 : 0 ≤ r := by positivity
      have hr4 : r ^ 4 = ((p : ℝ) ^ 3)⁻¹ := by
        rw [hr, inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      have hp3 : (8 : ℝ) ≤ (p : ℝ) ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num) hp2 3
        norm_num at this
        exact this
      have : ((p : ℝ) ^ 3)⁻¹ ≤ 1 / 8 := by
        rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      refine ⟨hr0, ?_⟩
      nlinarith [sq_nonneg r, sq_nonneg (r - 3/5), sq_nonneg (r + 3/5)]
    have hsumF : ∀ p : ℕ, p.Prime → HasSum (fun k => F (p ^ k))
        (1 + ((p : ℝ) ^ (3 / 4 : ℝ))⁻¹ ^ 2 / (1 - ((p : ℝ) ^ (3 / 4 : ℝ))⁻¹) ^ 2) := by
      intro p hp
      obtain ⟨hr0, hr1⟩ := hr p hp
      set r := ((p : ℝ) ^ (3 / 4 : ℝ))⁻¹ with hr
      have hn : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0]; linarith
      have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hn
      have h2 := hasSum_geometric_of_lt_one hr0 (by linarith : r < 1)
      have h3 := hasSum_ite_eq 0 (2 : ℝ)
      have h4 := (h1.sub h2).add h3
      have hval : r / (1 - r) ^ 2 - (1 - r)⁻¹ + 2 = 1 + r ^ 2 / (1 - r) ^ 2 := by
        have : (1 - r) ≠ 0 := by linarith
        field_simp
        ring
      rw [hval] at h4
      have hfun : (fun k => F (p ^ k))
          = fun k : ℕ => (k : ℝ) * r ^ k - r ^ k + if k = 0 then 2 else 0 := by
        funext k
        rw [hFp p hp k]
        rcases k with _ | k
        · norm_num
        · have : |1 - ((k + 1 : ℕ) : ℝ)| = (k : ℝ) := by
            push_cast; rw [abs_of_nonpos (by linarith)]; ring
          rw [this]; simp; ring
      rw [hfun]
      exact h4
    clear_value F
    have hT := Real.summable_nat_rpow_inv.2 (by norm_num : (1 : ℝ) < 3 / 2)
    refine ⟨Real.exp (7 * ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹), fun N => ?_⟩
    obtain ⟨-, hprod⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hF1 hFm (fun hp => (hsumF _ hp).summable.abs) (N + 1)
    have hind := hasSum_subtype_iff_indicator.1 hprod
    have hle := sum_le_hasSum (Finset.Icc 1 N)
      (fun n _ => Set.indicator_nonneg (fun n _ => hF0 n) n) hind
    have heq : ∑ n ∈ Finset.Icc 1 N, Set.indicator ((N + 1).smoothNumbers) F n
        = ∑ n ∈ Finset.Icc 1 N, F n := by
      refine Finset.sum_congr rfl fun n hn => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
      exact Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt (by omega) (by omega)) F
    rw [heq] at hle
    refine hle.trans ?_
    calc ∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, F (p ^ k)
        ≤ ∏ p ∈ (N + 1).primesBelow, Real.exp (7 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
          refine Finset.prod_le_prod₀ (fun p _ => tsum_nonneg fun k => hF0 _) fun p hp => ?_
          have hpp := Nat.prime_of_mem_primesBelow hp
          rw [(hsumF p hpp).tsum_eq]
          obtain ⟨hr0, hr1⟩ := hr p hpp
          have hsq : ((p : ℝ) ^ (3 / 4 : ℝ))⁻¹ ^ 2 = ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
            norm_num
          set r := ((p : ℝ) ^ (3 / 4 : ℝ))⁻¹
          rw [← hsq]
          have h1 : r ^ 2 / (1 - r) ^ 2 ≤ 7 * r ^ 2 := by
            have h16 : 4 / 25 ≤ (1 - r) ^ 2 := by nlinarith
            rw [div_le_iff₀ (by nlinarith)]
            nlinarith [mul_le_mul_of_nonneg_left h16 (sq_nonneg r)]
          linarith [Real.add_one_le_exp (7 * r ^ 2)]
      _ = Real.exp (7 * ∑ p ∈ (N + 1).primesBelow, ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
          rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ Real.exp (7 * ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
          gcongr
          exact hT.sum_le_tsum _ (fun n _ => by positivity)
  -- ## Step 3: insert the bound for `μ * μ`
  set a : ℕ → ℝ := fun n =>
    (((ArithmeticFunction.moebius * ArithmeticFunction.moebius) n : ℤ) : ℝ) with ha
  set hr : ℕ → ℝ := fun n => ((h n : ℤ) : ℝ) with hhr
  have hf : ∀ n : ℕ, ((ArithmeticFunction.moebius n : ℤ) : ℝ)
      * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) = ∑ d ∈ n.divisors, hr d * a (n / d) := by
    intro n
    have hgn : g n = ∑ d ∈ n.divisors,
        h d * (ArithmeticFunction.moebius * ArithmeticFunction.moebius) (n / d) := by
      rw [hgah, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
        (fun x y => h x * (ArithmeticFunction.moebius * ArithmeticFunction.moebius) y)]
    have hgn' : g n = ArithmeticFunction.moebius n * ((ArithmeticFunction.sigma 0 n : ℕ) : ℤ) := by
      rw [hg, ArithmeticFunction.pmul_apply, ArithmeticFunction.natCoe_apply]
    rw [hgn'] at hgn
    have := congrArg (fun z : ℤ => (z : ℝ)) hgn
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sum] at this
    rw [this]
  obtain ⟨c, hc, hA⟩ := sum_moebius_mul_moebius_isBigO_mul_exp_neg_mul_log_rpow
  obtain ⟨C, hC, hCw⟩ := hA.exists_pos
  obtain ⟨y0, hy0⟩ := eventually_atTop.1 (isBigOWith_iff.1 hCw)
  set A : ℝ → ℝ := fun y => ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n with hAdef
  set Y := max y0 1 with hY
  set C2 := C + ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, |a n| with hC2
  have hS0 : 0 ≤ S := by simpa using hS 0
  have hsa0 : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, |a n| := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hCC2 : C ≤ C2 := by linarith
  have hlin : ∀ y : ℝ, 1 ≤ y → |A y| ≤ C2 * y := by
    intro y hy
    rcases le_or_gt Y y with hYy | hYy
    · have hb := hy0 y (le_trans (le_max_left _ _) hYy)
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (mul_pos (by linarith) (Real.exp_pos _))] at hb
      have he : Real.exp (-c * Real.log y ^ (1 / 10 : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ Real.log y ^ (1 / 10 : ℝ) := Real.rpow_nonneg (Real.log_nonneg hy) _
        have := mul_nonneg hc.le this
        linarith
      calc |A y| ≤ C * (y * Real.exp (-c * Real.log y ^ (1 / 10 : ℝ))) := hb
        _ ≤ C * (y * 1) := by gcongr
        _ = C * y := by ring
        _ ≤ C2 * y := mul_le_mul_of_nonneg_right hCC2 (by linarith)
    · calc |A y| ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, |a n| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, |a n| :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hYy.le))
            (fun _ _ _ => abs_nonneg _)
        _ ≤ (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, |a n|) * y := le_mul_of_one_le_right hsa0 hy
        _ ≤ C2 * y := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  -- ## Step 4: the bound, splitting at `e = √x` term by term
  set c' := min (c / 2) (1 / 8 : ℝ) with hc'
  have hc'0 : 0 < c' := lt_min (by positivity) (by norm_num)
  refine ⟨c', hc'0, ?_⟩
  refine IsBigO.of_bound (S * (C + C2)) ?_
  filter_upwards [eventually_ge_atTop (max (Y ^ 2) (Real.exp 1))] with x hx
  have hxe : Real.exp 1 ≤ x := le_of_max_le_right hx
  have hxm : Y ^ 2 ≤ x := le_of_max_le_left hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  set L := Real.log x with hL
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hxe
  set s := Real.sqrt x with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hxpos
  have hss : s * s = x := Real.mul_self_sqrt hxpos.le
  have hsm : Y ≤ s := by
    rw [hs, Real.le_sqrt (by rw [hY]; positivity) hxpos.le]
    exact hxm
  have hy0s : y0 ≤ s := le_trans (by rw [hY]; exact le_max_left _ _) hsm
  have hlogs : Real.log s = L / 2 := by
    rw [hs, Real.log_sqrt hxpos.le]
  set E := Real.exp (-c' * L ^ (1 / 10 : ℝ)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hL0 : 0 ≤ L ^ (1 / 10 : ℝ) := Real.rpow_nonneg (by linarith) _
  set X8 := (x ^ (1 / 8 : ℝ))⁻¹ with hX8
  have hX8E : X8 ≤ E := by
    rw [hX8, Real.rpow_def_of_pos hxpos, ← Real.exp_neg, hE, Real.exp_le_exp]
    have h1 : L ^ (1 / 10 : ℝ) ≤ L := by
      have := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 10 : ℝ) ≤ 1)
      simpa using this
    have h2 : c' ≤ 1 / 8 := min_le_right _ _
    rw [← hL]
    have h3 : c' * L ^ (1 / 10 : ℝ) ≤ 1 / 8 * L := mul_le_mul h2 h1 hL0 (by norm_num)
    linarith
  have hX80 : 0 ≤ X8 := by positivity
  have hCE : 0 ≤ C * E := (mul_pos hC hEpos).le
  have hC2X8 : 0 ≤ C2 * X8 := mul_nonneg (by linarith) hX80
  clear_value X8 E
  have hterm : ∀ e ∈ Finset.Icc 1 ⌊x⌋₊,
      |hr e * A (x / e)| ≤ |hr e| * ((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ * (x * (C * E + C2 * X8)) := by
    intro e he
    obtain ⟨he1, heN⟩ := Finset.mem_Icc.1 he
    have he1' : (1 : ℝ) ≤ e := by exact_mod_cast he1
    have hepos : (0 : ℝ) < e := by linarith
    have hex : (e : ℝ) ≤ x := le_trans (by exact_mod_cast heN) (Nat.floor_le hxpos.le)
    have he34 : 0 < (e : ℝ) ^ (3 / 4 : ℝ) := by positivity
    rw [abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rcases le_or_gt (e : ℝ) s with hes | hes
    · have hsxe : s ≤ x / e := by
        rw [le_div_iff₀ hepos]
        calc s * e ≤ s * s := mul_le_mul_of_nonneg_left hes hspos.le
          _ = x := hss
      have hb := hy0 (x / e) (le_trans hy0s hsxe)
      have hxe0 : 0 < x / e := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (mul_pos hxe0 (Real.exp_pos _))] at hb
      have hexp : Real.exp (-c * Real.log (x / e) ^ (1 / 10 : ℝ)) ≤ E := by
        rw [hE, Real.exp_le_exp]
        have hlogy : L / 2 ≤ Real.log (x / e) := by
          rw [← hlogs]
          exact Real.log_le_log hspos hsxe
        have h1 : (L / 2) ^ (1 / 10 : ℝ) ≤ Real.log (x / e) ^ (1 / 10 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hlogy (by norm_num)
        have h2 : (L / 2) ^ (1 / 10 : ℝ) = L ^ (1 / 10 : ℝ) / 2 ^ (1 / 10 : ℝ) :=
          Real.div_rpow (by linarith) (by norm_num) _
        have h3 : (2 : ℝ) ^ (1 / 10 : ℝ) ≤ 2 := by
          have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            (by norm_num : (1 / 10 : ℝ) ≤ 1)
          simpa using this
        have h3pos : (0 : ℝ) < 2 ^ (1 / 10 : ℝ) := by positivity
        have h4 : L ^ (1 / 10 : ℝ) / 2 ≤ L ^ (1 / 10 : ℝ) / 2 ^ (1 / 10 : ℝ) :=
          div_le_div_of_nonneg_left hL0 h3pos h3
        have h5 : c' ≤ c / 2 := min_le_left _ _
        have h6 : c' * L ^ (1 / 10 : ℝ) ≤ c / 2 * L ^ (1 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_right h5 hL0
        have h7 : c * (L ^ (1 / 10 : ℝ) / 2) ≤ c * Real.log (x / e) ^ (1 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_left (by rw [h2] at h1; linarith) hc.le
        linarith
      have hinv : (e : ℝ)⁻¹ ≤ ((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ := by
        have := Real.rpow_le_rpow_of_exponent_le he1' (by norm_num : (3 / 4 : ℝ) ≤ 1)
        rw [Real.rpow_one] at this
        exact inv_anti₀ he34 this
      calc |A (x / e)| ≤ C * (x / e * Real.exp (-c * Real.log (x / e) ^ (1 / 10 : ℝ))) := hb
        _ ≤ C * (x / e * E) := by gcongr
        _ = (e : ℝ)⁻¹ * (x * (C * E)) := by ring
        _ ≤ ((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ * (x * (C * E + C2 * X8)) := by
          apply mul_le_mul hinv _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) hxpos.le
    · have hxe1 : 1 ≤ x / e := by rw [le_div_iff₀ hepos]; linarith
      have hsplit : (e : ℝ)⁻¹ = ((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ * ((e : ℝ) ^ (1 / 4 : ℝ))⁻¹ := by
        rw [← mul_inv, ← Real.rpow_add hepos]; norm_num
      have hs4 : x ^ (1 / 8 : ℝ) ≤ (e : ℝ) ^ (1 / 4 : ℝ) := by
        have : x ^ (1 / 8 : ℝ) = s ^ (1 / 4 : ℝ) := by
          rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]; norm_num
        rw [this]
        exact Real.rpow_le_rpow hspos.le hes.le (by norm_num)
      have hinv : (e : ℝ)⁻¹ ≤ ((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ * X8 := by
        rw [hsplit, hX8]
        gcongr
      calc |A (x / e)| ≤ C2 * (x / e) := hlin _ hxe1
        _ = (e : ℝ)⁻¹ * (x * C2) := by ring
        _ ≤ (((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ * X8) * (x * C2) :=
          mul_le_mul_of_nonneg_right hinv (mul_nonneg hxpos.le (by linarith))
        _ ≤ ((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ * (x * (C * E + C2 * X8)) := by
          have h0 : 0 ≤ ((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ * x := by positivity
          calc (((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ * X8) * (x * C2)
              = ((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ * x * (C2 * X8) := by ring
            _ ≤ ((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ * x * (C * E + C2 * X8) :=
                mul_le_mul_of_nonneg_left (by linarith) h0
            _ = ((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ * (x * (C * E + C2 * X8)) := by ring
  have hrw : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.moebius n : ℤ) : ℝ)
      * ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) = ∑ e ∈ Finset.Icc 1 ⌊x⌋₊, hr e * A (x / e) := by
    calc _ = ∑ r ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ r.divisors, hr d * a (r / d) :=
          Finset.sum_congr rfl fun n _ => hf n
      _ = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, ∑ m ∈ Finset.Icc 1 (⌊x⌋₊ / d), hr d * a m :=
          (Nat.sum_Icc_sum_Icc_div_eq_sum_Icc_sum_divisors _ fun d m => hr d * a m).symm
      _ = ∑ e ∈ Finset.Icc 1 ⌊x⌋₊, hr e * A (x / e) :=
          Finset.sum_congr rfl fun d _ => by
            rw [hAdef]; dsimp only; rw [Nat.floor_div_natCast, Finset.mul_sum]
  rw [hrw, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (mul_pos hxpos hEpos)]
  calc |∑ e ∈ Finset.Icc 1 ⌊x⌋₊, hr e * A (x / e)|
      ≤ ∑ e ∈ Finset.Icc 1 ⌊x⌋₊, |hr e * A (x / e)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ Finset.Icc 1 ⌊x⌋₊,
          |hr e| * ((e : ℝ) ^ (3 / 4 : ℝ))⁻¹ * (x * (C * E + C2 * X8)) :=
        Finset.sum_le_sum hterm
    _ = (∑ e ∈ Finset.Icc 1 ⌊x⌋₊, |hr e| * ((e : ℝ) ^ (3 / 4 : ℝ))⁻¹)
          * (x * (C * E + C2 * X8)) := by
        rw [Finset.sum_mul]
    _ ≤ S * (x * (C * E + C2 * X8)) := by
        apply mul_le_mul_of_nonneg_right (hS _)
        exact mul_nonneg hxpos.le (by linarith)
    _ ≤ S * (C + C2) * (x * E) := by
        have h1 : C2 * X8 ≤ C2 * E := mul_le_mul_of_nonneg_left hX8E (by linarith)
        have h2 : x * (C * E + C2 * X8) ≤ x * ((C + C2) * E) :=
          mul_le_mul_of_nonneg_left (by rw [add_mul]; linarith) hxpos.le
        calc S * (x * (C * E + C2 * X8)) ≤ S * (x * ((C + C2) * E)) :=
              mul_le_mul_of_nonneg_left h2 hS0
          _ = S * (C + C2) * (x * E) := by ring

end ArithmeticFunction
