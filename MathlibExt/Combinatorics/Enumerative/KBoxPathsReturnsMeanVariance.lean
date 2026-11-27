/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.KBoxReturnGF
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import MathlibExt.RingTheory.PowerSeries.LagrangeBurmannCoefficient

/-!
# Mean and variance of the number of returns of $k$-box paths

The main result is `kBoxPaths_returns_mean_variance`: the mean and variance of
the number of returns over the $k$-box paths of size $n$. It is proved by
differentiating the functional equation for the returns generating function
with respect to the return-marking variable and extracting coefficients with
the Lagrange–Bürmann formula for the augmented Dyck generating function.
-/

namespace MetaMathlibExt

namespace kBoxPaths_returns_mean_variance

open PowerSeries SkewDyckStep

/-- The generating function of augmented $(k+1)$-Dyck paths, over `ℚ`. -/
private noncomputable abbrev dyckGF (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) (augmentedKDyckGF k)

private theorem dyckGF_eq {k : ℕ} (hk : 1 ≤ k) :
    dyckGF (k + 1) = 1 + PowerSeries.X * dyckGF (k + 1) ^ (k + 2) := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) (augmentedKDyckGF_eq hk)
  simpa [dyckGF] using h

private theorem constantCoeff_dyckGF {k : ℕ} (hk : 1 ≤ k) :
    constantCoeff (dyckGF (k + 1)) = 1 := by
  have h := congrArg constantCoeff (dyckGF_eq hk)
  simpa using h

private theorem coeff_one_add_X_pow (N n : ℕ) :
    coeff n ((1 + PowerSeries.X : PowerSeries ℚ) ^ N) = (N.choose n : ℚ) := by
  calc coeff n ((1 + PowerSeries.X : PowerSeries ℚ) ^ N)
      = coeff n (binomialSeries ℚ (N : ℚ)) := by rw [binomialSeries_nat]
    _ = Ring.choose (N : ℚ) n • (1 : ℚ) := binomialSeries_coeff _ _
    _ = (N.choose n : ℚ) := by simp [Ring.choose_natCast]

private theorem derivative_one_add_X_pow (m : ℕ) :
    derivative ((1 + PowerSeries.X : PowerSeries ℚ) ^ m) =
      C (m : ℚ) * (1 + PowerSeries.X) ^ (m - 1) := by
  cases m with
  | zero => simp
  | succ m =>
    rw [derivative_pow]
    simp

private theorem subst_one_add_X_pow (A : PowerSeries ℚ) (hA : HasSubst A) (p : ℕ) :
    subst A ((1 + PowerSeries.X : PowerSeries ℚ) ^ p) = (1 + A) ^ p := by
  rw [subst_pow hA, subst_add hA, subst_X hA]
  rw [show (1 : PowerSeries ℚ) = C 1 by simp, subst_C]
  simp

/-- **Cleared Lagrange–Bürmann coefficient formula.** For $n \ge 1$, the coefficient of
$x^n$ in $G_{k+1}^m$ satisfies $n [x^n] G_{k+1}^m =
m \binom{(k+2)n + m - 1}{n - 1}$. -/
private theorem coeff_dyckGF_pow_mul {k m N : ℕ} (hk : 1 ≤ k) (hN : 0 < N) :
    (N : ℚ) * coeff N (dyckGF (k + 1) ^ m) =
      (m : ℚ) * (((k + 2) * N + m - 1).choose (N - 1) : ℚ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  let A : PowerSeries ℚ := dyckGF (k + 1) - 1
  have hA0 : constantCoeff A = 0 := by
    simp [A, constantCoeff_dyckGF hk]
  have hsubstA : HasSubst A := HasSubst.of_constantCoeff_zero' hA0
  have hone : (1 : PowerSeries ℚ) + A = dyckGF (k + 1) := by simp [A]
  have hfix : A = PowerSeries.X *
      subst A ((1 + PowerSeries.X : PowerSeries ℚ) ^ (k + 2)) := by
    rw [subst_one_add_X_pow A hsubstA, hone]
    rw [sub_eq_iff_eq_add]
    nth_rewrite 1 [dyckGF_eq hk]
    ring
  have hlag := fps_lagrange_burmann_coeff' A ((1 + PowerSeries.X : PowerSeries ℚ) ^ (k + 2))
    ((1 + PowerSeries.X : PowerSeries ℚ) ^ m) hfix N hN
  rw [subst_one_add_X_pow A hsubstA, hone, derivative_one_add_X_pow, ← pow_mul,
    mul_assoc, ← pow_add] at hlag
  have hexp : m - 1 + (k + 2) * N = (k + 2) * N + m - 1 := by omega
  rw [hexp, coeff_C_mul, coeff_one_add_X_pow] at hlag
  exact hlag

/-- **Raney coefficient formula.** For $m \ge 1$, the coefficient of $x^N$ in
$G_{k+1}^m$ is $\frac{m}{(k+2)N + m} \binom{(k+2)N + m}{N}$. -/
private theorem coeff_dyckGF_pow {k m N : ℕ} (hk : 1 ≤ k) (hm : 0 < m) :
    coeff N (dyckGF (k + 1) ^ m) =
      (m : ℚ) / ((k + 2) * N + m) * (((k + 2) * N + m).choose N : ℚ) := by
  cases N with
  | zero =>
    have h0 : coeff 0 (dyckGF (k + 1) ^ m) = 1 := by
      rw [coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_dyckGF hk,
        one_pow]
    rw [h0]
    simp [hm.ne']
  | succ N =>
    have hden : ((k : ℚ) + 2) * ((N + 1 : ℕ) : ℚ) + (m : ℚ) ≠ 0 := by positivity
    have hlag := coeff_dyckGF_pow_mul (k := k) (m := m) (N := N + 1) hk (Nat.succ_pos N)
    simp only [Nat.add_sub_cancel] at hlag
    have hchoose : (((k + 2) * (N + 1) + m : ℕ) : ℚ) *
          ((((k + 2) * (N + 1) + m - 1).choose N : ℕ) : ℚ) =
        ((N + 1 : ℕ) : ℚ) * ((((k + 2) * (N + 1) + m).choose (N + 1) : ℕ) : ℚ) := by
      have h := Nat.add_one_mul_choose_eq ((k + 2) * (N + 1) + m - 1) N
      have he : (k + 2) * (N + 1) + m - 1 + 1 = (k + 2) * (N + 1) + m := by omega
      rw [he] at h
      have h' : ((k + 2) * (N + 1) + m) * ((k + 2) * (N + 1) + m - 1).choose N =
          (N + 1) * ((k + 2) * (N + 1) + m).choose (N + 1) := h.trans (mul_comm _ _)
      exact_mod_cast h'
    rw [div_mul_eq_mul_div, eq_comm, div_eq_iff hden]
    have h3 : ((N + 1 : ℕ) : ℚ) * (coeff (N + 1) (dyckGF (k + 1) ^ m) *
          (((k + 2) * (N + 1) + m : ℕ) : ℚ)) =
        ((N + 1 : ℕ) : ℚ) * ((m : ℚ) * ((((k + 2) * (N + 1) + m).choose (N + 1) : ℕ) : ℚ)) := by
      calc ((N + 1 : ℕ) : ℚ) * (coeff (N + 1) (dyckGF (k + 1) ^ m) *
              (((k + 2) * (N + 1) + m : ℕ) : ℚ))
          = (((N + 1 : ℕ) : ℚ) * coeff (N + 1) (dyckGF (k + 1) ^ m)) *
              (((k + 2) * (N + 1) + m : ℕ) : ℚ) := by ring
        _ = ((m : ℚ) * ((((k + 2) * (N + 1) + m - 1).choose N : ℕ) : ℚ)) *
              (((k + 2) * (N + 1) + m : ℕ) : ℚ) := by rw [hlag]
        _ = (m : ℚ) * ((((k + 2) * (N + 1) + m : ℕ) : ℚ) *
              ((((k + 2) * (N + 1) + m - 1).choose N : ℕ) : ℚ)) := by ring
        _ = (m : ℚ) * (((N + 1 : ℕ) : ℚ) *
              ((((k + 2) * (N + 1) + m).choose (N + 1) : ℕ) : ℚ)) := by rw [hchoose]
        _ = ((N + 1 : ℕ) : ℚ) * ((m : ℚ) *
              ((((k + 2) * (N + 1) + m).choose (N + 1) : ℕ) : ℚ)) := by ring
    have hfin : coeff (N + 1) (dyckGF (k + 1) ^ m) *
          (((k + 2) * (N + 1) + m : ℕ) : ℚ) =
        (m : ℚ) * ((((k + 2) * (N + 1) + m).choose (N + 1) : ℕ) : ℚ) :=
      mul_left_cancel₀ (by positivity : ((N + 1 : ℕ) : ℚ) ≠ 0) h3
    rw [← hfin]
    push_cast
    ring

/-! ### Differentiating the returns series in the return-marking variable -/

/-- The returns generating function over `ℚ[t]`. -/
private noncomputable abbrev returnGF (k : ℕ) : PowerSeries (Polynomial ℚ) :=
  PowerSeries.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) (kBoxReturnGF k)

/-- The augmented Dyck generating function over `ℚ[t]`, with constant coefficients. -/
private noncomputable abbrev dyckGFPoly (k : ℕ) : PowerSeries (Polynomial ℚ) :=
  PowerSeries.map Polynomial.C (dyckGF k)

/-- Coefficientwise differentiation in the polynomial variable. -/
private noncomputable def derivT (F : PowerSeries (Polynomial ℚ)) :
    PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk fun n => Polynomial.derivative (coeff n F)

private theorem coeff_derivT (F : PowerSeries (Polynomial ℚ)) (n : ℕ) :
    coeff n (derivT F) = Polynomial.derivative (coeff n F) := by
  simp [derivT]

private theorem derivT_add (F G : PowerSeries (Polynomial ℚ)) :
    derivT (F + G) = derivT F + derivT G := by
  ext n
  simp [coeff_derivT, Polynomial.derivative_add]

private theorem derivT_mul (F G : PowerSeries (Polynomial ℚ)) :
    derivT (F * G) = derivT F * G + F * derivT G := by
  apply PowerSeries.ext
  intro n
  have hL : coeff n (derivT (F * G)) =
      ∑ i ∈ Finset.range (n + 1),
        Polynomial.derivative (coeff i F * coeff (n - i) G) := by
    rw [coeff_derivT, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i F * coeff j G),
      Polynomial.derivative_sum]
  have hR : coeff n (derivT F * G + F * derivT G) =
      ∑ i ∈ Finset.range (n + 1),
        (Polynomial.derivative (coeff i F) * coeff (n - i) G +
          coeff i F * Polynomial.derivative (coeff (n - i) G)) := by
    rw [map_add, coeff_mul, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (derivT F) * coeff j G),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i F * coeff j (derivT G)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_derivT, coeff_derivT]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.derivative_mul]

private theorem derivT_sub (F G : PowerSeries (Polynomial ℚ)) :
    derivT (F - G) = derivT F - derivT G := by
  ext n
  simp [coeff_derivT, Polynomial.derivative_sub]

private theorem derivT_one : derivT (1 : PowerSeries (Polynomial ℚ)) = 0 := by
  ext n
  cases n with
  | zero => simp [coeff_derivT]
  | succ n => simp [coeff_derivT]

private theorem derivT_X : derivT (PowerSeries.X : PowerSeries (Polynomial ℚ)) = 0 := by
  ext n
  rw [coeff_derivT, coeff_X]
  by_cases hn : n = 1 <;> simp [hn]

private theorem derivT_C (p : Polynomial ℚ) :
    derivT (PowerSeries.C p : PowerSeries (Polynomial ℚ)) =
      PowerSeries.C (Polynomial.derivative p) := by
  ext n
  cases n with
  | zero => simp [coeff_derivT]
  | succ n => simp [coeff_derivT]

private theorem derivT_smul_C (p : Polynomial ℚ) (F : PowerSeries (Polynomial ℚ)) :
    derivT (PowerSeries.C p * F) =
      PowerSeries.C (Polynomial.derivative p) * F + PowerSeries.C p * derivT F := by
  rw [derivT_mul, derivT_C]

private theorem derivT_dyckGFPoly {k : ℕ} :
    derivT (dyckGFPoly k) = 0 := by
  ext n
  simp [coeff_derivT, dyckGFPoly]

private theorem derivT_pow_dyckGFPoly {k m : ℕ} :
    derivT (dyckGFPoly k ^ m) = 0 := by
  induction m with
  | zero => simp [derivT_one]
  | succ m ih => rw [pow_succ, derivT_mul, derivT_dyckGFPoly, ih]; simp

private theorem derivT_X_pow_dyckGFPoly {k m : ℕ} :
    derivT (PowerSeries.X * dyckGFPoly k ^ m : PowerSeries (Polynomial ℚ)) = 0 := by
  rw [derivT_mul, derivT_X, derivT_pow_dyckGFPoly]
  simp

private theorem derivT_t_mul {k m : ℕ} :
    derivT (PowerSeries.C (Polynomial.X : Polynomial ℚ) *
        (PowerSeries.X * dyckGFPoly k ^ m) : PowerSeries (Polynomial ℚ)) =
      PowerSeries.X * dyckGFPoly k ^ m := by
  rw [derivT_mul, derivT_X_pow_dyckGFPoly, derivT_C]
  simp [Polynomial.derivative_X]

/-- The returns functional equation over `ℚ[t]`. -/
private theorem returnGF_eq {k : ℕ} (hk : 1 ≤ k) :
    (1 - PowerSeries.C (Polynomial.X : Polynomial ℚ) * PowerSeries.X *
          dyckGFPoly (k + 1) ^ (k + 1)) * returnGF k =
      PowerSeries.C (Polynomial.X : Polynomial ℚ) * PowerSeries.X *
        dyckGFPoly (k + 1) ^ k := by
  have h := congrArg
    (PowerSeries.map (Polynomial.mapRingHom (Int.castRingHom ℚ))) (kBoxReturnGF_eq hk)
  have hmap : PowerSeries.map (Polynomial.mapRingHom (Int.castRingHom ℚ))
        (PowerSeries.map Polynomial.C (augmentedKDyckGF (k + 1))) =
      dyckGFPoly (k + 1) := by
    ext n
    simp [coeff_map, dyckGFPoly, dyckGF]
  simpa [returnGF, hmap] using h

/-- The first derivative of the returns equation, evaluated in the series variable. -/
private theorem derivT_returnGF_eq {k : ℕ} (hk : 1 ≤ k) :
    -(PowerSeries.X * dyckGFPoly (k + 1) ^ (k + 1)) * returnGF k +
        (1 - PowerSeries.C (Polynomial.X : Polynomial ℚ) * PowerSeries.X *
          dyckGFPoly (k + 1) ^ (k + 1)) * derivT (returnGF k) =
      PowerSeries.X * dyckGFPoly (k + 1) ^ k := by
  have hH : derivT (1 - PowerSeries.C (Polynomial.X : Polynomial ℚ) *
        PowerSeries.X * dyckGFPoly (k + 1) ^ (k + 1) :
        PowerSeries (Polynomial ℚ)) =
      -(PowerSeries.X * dyckGFPoly (k + 1) ^ (k + 1)) := by
    rw [derivT_sub, derivT_one, mul_assoc, derivT_t_mul, zero_sub]
  have hR : derivT (PowerSeries.C (Polynomial.X : Polynomial ℚ) *
        PowerSeries.X * dyckGFPoly (k + 1) ^ k : PowerSeries (Polynomial ℚ)) =
      PowerSeries.X * dyckGFPoly (k + 1) ^ k := by
    rw [mul_assoc]
    exact derivT_t_mul
  have h := congrArg derivT (returnGF_eq hk)
  nth_rewrite 1 [derivT_mul] at h
  rw [hH, hR] at h
  exact h

private theorem derivT_neg (F : PowerSeries (Polynomial ℚ)) :
    derivT (-F) = -derivT F := by
  ext n
  simp [coeff_derivT]

/-- The second derivative of the returns equation. -/
private theorem derivT_derivT_returnGF_eq {k : ℕ} (hk : 1 ≤ k) :
    (1 - PowerSeries.C (Polynomial.X : Polynomial ℚ) * PowerSeries.X *
          dyckGFPoly (k + 1) ^ (k + 1)) * derivT (derivT (returnGF k)) =
      2 * (PowerSeries.X * dyckGFPoly (k + 1) ^ (k + 1)) * derivT (returnGF k) := by
  have hH : derivT (1 - PowerSeries.C (Polynomial.X : Polynomial ℚ) *
        PowerSeries.X * dyckGFPoly (k + 1) ^ (k + 1) :
        PowerSeries (Polynomial ℚ)) =
      -(PowerSeries.X * dyckGFPoly (k + 1) ^ (k + 1)) := by
    rw [derivT_sub, derivT_one, mul_assoc, derivT_t_mul, zero_sub]
  have e1 : derivT (-(PowerSeries.X * dyckGFPoly (k + 1) ^ (k + 1)) * returnGF k) =
      -(PowerSeries.X * dyckGFPoly (k + 1) ^ (k + 1)) * derivT (returnGF k) := by
    rw [derivT_mul, derivT_neg, derivT_X_pow_dyckGFPoly]
    simp
  have e2 : derivT ((1 - PowerSeries.C (Polynomial.X : Polynomial ℚ) *
        PowerSeries.X * dyckGFPoly (k + 1) ^ (k + 1)) * derivT (returnGF k)) =
      -(PowerSeries.X * dyckGFPoly (k + 1) ^ (k + 1)) * derivT (returnGF k) +
        (1 - PowerSeries.C (Polynomial.X : Polynomial ℚ) * PowerSeries.X *
          dyckGFPoly (k + 1) ^ (k + 1)) * derivT (derivT (returnGF k)) := by
    rw [derivT_mul, hH]
  have h2 := congrArg derivT (derivT_returnGF_eq hk)
  rw [derivT_add, e1, e2, derivT_X_pow_dyckGFPoly] at h2
  linear_combination h2

/-- Evaluation at `t = 1`. -/
private abbrev ev1 : Polynomial ℚ →+* ℚ := Polynomial.evalRingHom 1

private theorem map_ev1_dyckGFPoly (k : ℕ) :
    PowerSeries.map ev1 (dyckGFPoly k) = dyckGF k := by
  ext n
  simp [coeff_map, dyckGFPoly]

private theorem map_ev1_C_X :
    PowerSeries.map ev1 (PowerSeries.C (Polynomial.X : Polynomial ℚ)) =
      (1 : PowerSeries ℚ) := by
  ext n
  simp [ev1]

private theorem mul_inv_dyckGF {k : ℕ} (hk : 1 ≤ k) :
    (1 - PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) * dyckGF (k + 1) = 1 := by
  have hG := dyckGF_eq hk
  have hpow : PowerSeries.X * dyckGF (k + 1) ^ (k + 2) =
      (PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) * dyckGF (k + 1) := by
    rw [pow_succ]
    ring
  rw [sub_mul, one_mul, ← hpow]
  linear_combination hG

/-- The total-count series, evaluated at `t = 1`. -/
private theorem eval_returnGF {k : ℕ} (hk : 1 ≤ k) :
    PowerSeries.map ev1 (returnGF k) =
      PowerSeries.X * dyckGF (k + 1) ^ (k + 1) := by
  have eq0 := congrArg (PowerSeries.map ev1) (returnGF_eq hk)
  simp only [map_mul, map_sub, map_one, map_pow, map_ev1_C_X, one_mul,
    PowerSeries.map_X, map_ev1_dyckGFPoly] at eq0
  calc PowerSeries.map ev1 (returnGF k)
      = PowerSeries.map ev1 (returnGF k) *
          ((1 - PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) * dyckGF (k + 1)) := by
        rw [mul_inv_dyckGF hk, mul_one]
    _ = ((1 - PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) *
          PowerSeries.map ev1 (returnGF k)) * dyckGF (k + 1) := by ring
    _ = (PowerSeries.X * dyckGF (k + 1) ^ k) * dyckGF (k + 1) := by rw [eq0]
    _ = PowerSeries.X * dyckGF (k + 1) ^ (k + 1) := by
        rw [mul_assoc, ← pow_succ]

/-- The first-moment series, evaluated at `t = 1`. -/
private theorem eval_derivT_returnGF {k : ℕ} (hk : 1 ≤ k) :
    PowerSeries.map ev1 (derivT (returnGF k)) =
      PowerSeries.X * dyckGF (k + 1) ^ (k + 2) := by
  have eq1 := congrArg (PowerSeries.map ev1) (derivT_returnGF_eq hk)
  simp only [map_mul, map_sub, map_one, map_pow, map_neg, map_ev1_C_X, one_mul,
    PowerSeries.map_X, map_ev1_dyckGFPoly, map_add] at eq1
  have hF0 := eval_returnGF hk
  have hD1eq : (1 - PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) *
        PowerSeries.map ev1 (derivT (returnGF k)) =
      PowerSeries.X * dyckGF (k + 1) ^ k +
        (PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) *
          PowerSeries.map ev1 (returnGF k) := by
    linear_combination eq1
  calc PowerSeries.map ev1 (derivT (returnGF k))
      = PowerSeries.map ev1 (derivT (returnGF k)) *
          ((1 - PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) * dyckGF (k + 1)) := by
        rw [mul_inv_dyckGF hk, mul_one]
    _ = ((1 - PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) *
          PowerSeries.map ev1 (derivT (returnGF k))) * dyckGF (k + 1) := by ring
    _ = (PowerSeries.X * dyckGF (k + 1) ^ k +
          (PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) *
            PowerSeries.map ev1 (returnGF k)) * dyckGF (k + 1) := by rw [hD1eq]
    _ = PowerSeries.X * dyckGF (k + 1) ^ (k + 1) +
          PowerSeries.X ^ 2 * dyckGF (k + 1) ^ (2 * k + 3) := by
        rw [hF0, add_mul]
        have e1 : (PowerSeries.X * dyckGF (k + 1) ^ k) * dyckGF (k + 1) =
            PowerSeries.X * dyckGF (k + 1) ^ (k + 1) := by
          rw [mul_assoc, ← pow_succ]
        have e2 : ((PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) *
              (PowerSeries.X * dyckGF (k + 1) ^ (k + 1))) * dyckGF (k + 1) =
            PowerSeries.X ^ 2 * dyckGF (k + 1) ^ (2 * k + 3) := by
          have hp : dyckGF (k + 1) ^ (k + 1) * dyckGF (k + 1) ^ (k + 1) *
              dyckGF (k + 1) = dyckGF (k + 1) ^ (2 * k + 3) := by
            rw [← pow_add (dyckGF (k + 1)) (k + 1) (k + 1),
              ← pow_succ (dyckGF (k + 1)) ((k + 1) + (k + 1))]
            congr 1
            omega
          calc ((PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) *
                  (PowerSeries.X * dyckGF (k + 1) ^ (k + 1))) * dyckGF (k + 1)
              = PowerSeries.X ^ 2 * (dyckGF (k + 1) ^ (k + 1) *
                  dyckGF (k + 1) ^ (k + 1) * dyckGF (k + 1)) := by ring
            _ = PowerSeries.X ^ 2 * dyckGF (k + 1) ^ (2 * k + 3) := by rw [hp]
        rw [e1, e2]
    _ = PowerSeries.X * dyckGF (k + 1) ^ (k + 1) *
          (1 + PowerSeries.X * dyckGF (k + 1) ^ (k + 2)) := by
        have hp : dyckGF (k + 1) ^ (2 * k + 3) =
            dyckGF (k + 1) ^ (k + 1) * dyckGF (k + 1) ^ (k + 2) := by
          rw [← pow_add (dyckGF (k + 1)) (k + 1) (k + 2)]
          congr 1
          omega
        rw [hp]
        ring
    _ = PowerSeries.X * dyckGF (k + 1) ^ (k + 1) * dyckGF (k + 1) := by
        rw [← dyckGF_eq hk]
    _ = PowerSeries.X * dyckGF (k + 1) ^ (k + 2) := by
        rw [mul_assoc, ← pow_succ]

/-- The falling-factorial-moment series, evaluated at `t = 1`. -/
private theorem eval_derivT_derivT_returnGF {k : ℕ} (hk : 1 ≤ k) :
    PowerSeries.map ev1 (derivT (derivT (returnGF k))) =
      2 * PowerSeries.X ^ 2 * dyckGF (k + 1) ^ (2 * k + 4) := by
  have eq2 := congrArg (PowerSeries.map ev1) (derivT_derivT_returnGF_eq hk)
  simp only [map_mul, map_sub, map_one, map_pow, map_ev1_C_X, one_mul, map_ofNat,
    PowerSeries.map_X, map_ev1_dyckGFPoly] at eq2
  have hD1 := eval_derivT_returnGF hk
  calc PowerSeries.map ev1 (derivT (derivT (returnGF k)))
      = PowerSeries.map ev1 (derivT (derivT (returnGF k))) *
          ((1 - PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) * dyckGF (k + 1)) := by
        rw [mul_inv_dyckGF hk, mul_one]
    _ = ((1 - PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) *
          PowerSeries.map ev1 (derivT (derivT (returnGF k)))) * dyckGF (k + 1) :=
        by ring
    _ = (2 * (PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) *
          PowerSeries.map ev1 (derivT (returnGF k))) * dyckGF (k + 1) := by rw [eq2]
    _ = 2 * PowerSeries.X ^ 2 * dyckGF (k + 1) ^ (2 * k + 4) := by
        rw [hD1]
        have hp : dyckGF (k + 1) ^ (k + 1) * dyckGF (k + 1) ^ (k + 2) *
            dyckGF (k + 1) = dyckGF (k + 1) ^ (2 * k + 4) := by
          rw [← pow_add (dyckGF (k + 1)) (k + 1) (k + 2),
            ← pow_succ (dyckGF (k + 1)) ((k + 1) + (k + 2))]
          congr 1
          omega
        calc (2 * (PowerSeries.X * dyckGF (k + 1) ^ (k + 1)) *
                (PowerSeries.X * dyckGF (k + 1) ^ (k + 2))) * dyckGF (k + 1)
            = 2 * PowerSeries.X ^ 2 * (dyckGF (k + 1) ^ (k + 1) *
                dyckGF (k + 1) ^ (k + 2) * dyckGF (k + 1)) := by ring
          _ = 2 * PowerSeries.X ^ 2 * dyckGF (k + 1) ^ (2 * k + 4) := by rw [hp]

/-! ### Extracting the moments as coefficients -/

private theorem eval_derivative_X_pow (r : ℕ) :
    Polynomial.eval 1 (Polynomial.derivative ((Polynomial.X : Polynomial ℚ) ^ r)) =
      (r : ℚ) := by
  rw [Polynomial.derivative_X_pow]
  simp

private theorem eval_derivative_derivative_X_pow (r : ℕ) :
    Polynomial.eval 1
        (Polynomial.derivative (Polynomial.derivative
          ((Polynomial.X : Polynomial ℚ) ^ r))) =
      (r : ℚ) * ((r : ℚ) - 1) := by
  cases r with
  | zero => simp
  | succ r =>
    cases r with
    | zero => simp
    | succ m =>
      rw [Polynomial.derivative_X_pow, Polynomial.derivative_mul,
        Polynomial.derivative_C, Polynomial.derivative_X_pow]
      simp only [zero_mul, zero_add, Nat.cast_add, Nat.cast_one]
      have e1 : m + 2 - 1 = m + 1 := by omega
      have e2 : m + 1 - 1 = m := by omega
      rw [e1, e2]
      simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

private theorem coeff_returnGF (k n : ℕ) :
    coeff n (returnGF k) =
      if n = 0 then 0 else
        ∑ w ∈ kBoxPaths k n, (Polynomial.X : Polynomial ℚ) ^ skewReturns w := by
  by_cases hn : n = 0
  · simp [hn, returnGF, kBoxReturnGF]
  · simp only [hn, ite_false, returnGF, kBoxReturnGF, PowerSeries.coeff_map,
      PowerSeries.coeff_mk]
    rw [map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_pow]
    simp

private theorem coeff_eval_returnGF (k N : ℕ) :
    coeff (N + 1) (PowerSeries.map ev1 (returnGF k)) =
      ((kBoxPaths k (N + 1)).card : ℚ) := by
  rw [coeff_map, coeff_returnGF]
  simp [ev1]

private theorem coeff_eval_derivT_returnGF (k N : ℕ) :
    coeff (N + 1) (PowerSeries.map ev1 (derivT (returnGF k))) =
      ∑ w ∈ kBoxPaths k (N + 1), (skewReturns w : ℚ) := by
  rw [coeff_map, coeff_derivT, coeff_returnGF]
  simp [ev1, eval_derivative_X_pow]

private theorem coeff_eval_derivT_derivT_returnGF (k N : ℕ) :
    coeff (N + 1) (PowerSeries.map ev1 (derivT (derivT (returnGF k)))) =
      ∑ w ∈ kBoxPaths k (N + 1), (skewReturns w : ℚ) * ((skewReturns w : ℚ) - 1) := by
  rw [coeff_map, coeff_derivT, coeff_derivT, coeff_returnGF]
  simp [ev1, eval_derivative_derivative_X_pow]

end kBoxPaths_returns_mean_variance

open kBoxPaths_returns_mean_variance PowerSeries

/-- **Mean and variance of the number of returns of $k$-box paths.** Let $k \ge 1$ and $n \ge 1$,
and let $R(\mu)$ be the number of returns (steps ending on the $x$-axis) of a path $\mu$. The
average of $R$ over the $k$-box paths of size $n$ is
$$\frac{(k+2)((k+2)n-1)}{(k+1)((k+1)n+1)},$$
and the average of $R^2$ over these paths minus the square of the average of $R$ is
$$\frac{(k+2)((k+2)n-1)((2k+1)(k+1)n-2)(n-1)}{(k+1)^2((k+1)n+1)^2((k+1)n+2)}.$$

Source: Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary
Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Corollary 11
(`jis-2024-24.2.4-cor-11`). -/
public theorem kBoxPaths_returns_mean_variance {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∑ w ∈ kBoxPaths k n, (skewReturns w : ℚ)) / (kBoxPaths k n).card =
        ((k + 2) * ((k + 2) * n - 1) : ℚ) / ((k + 1) * ((k + 1) * n + 1)) ∧
      (∑ w ∈ kBoxPaths k n, (skewReturns w : ℚ) ^ 2) / (kBoxPaths k n).card -
          ((∑ w ∈ kBoxPaths k n, (skewReturns w : ℚ)) / (kBoxPaths k n).card) ^ 2 =
        ((k + 2) * ((k + 2) * n - 1) * ((2 * k + 1) * (k + 1) * n - 2) * (n - 1) : ℚ) /
          ((k + 1) ^ 2 * ((k + 1) * n + 1) ^ 2 * ((k + 1) * n + 2)) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- The central binomial atom.
  set C0 : ℚ := (((k + 2) * (N + 1) - 1).choose N : ℚ) with hC0
  have hge : N + 1 ≤ (k + 2) * (N + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hA2 : 2 * (N + 1) ≤ (k + 2) * (N + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hC0pos : 0 < C0 := by
    rw [hC0]
    exact_mod_cast Nat.choose_pos (by omega : N ≤ (k + 2) * (N + 1) - 1)
  have hD1ne : (((k + 2) * (N + 1) - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : (k + 2) * (N + 1) - 1 ≠ 0)
  have hD2ne : (((k + 1) * (N + 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hD3ne : (((k + 1) * (N + 1) + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  have hk1ne : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hk2ne : ((k + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  have hD1cast : (((k + 2) * (N + 1) - 1 : ℕ) : ℚ) =
      ((k : ℚ) + 2) * (↑N + 1) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ (k + 2) * (N + 1))]
    push_cast
    ring
  have hD2cast : (((k + 1) * (N + 1) + 1 : ℕ) : ℚ) =
      ((k : ℚ) + 1) * (↑N + 1) + 1 := by
    push_cast
    ring
  have hD3cast : (((k + 1) * (N + 1) + 2 : ℕ) : ℚ) =
      ((k : ℚ) + 1) * (↑N + 1) + 2 := by
    push_cast
    ring
  have hSubcast : (((2 * k + 1) * (k + 1) * (N + 1) - 2 : ℕ) : ℚ) =
      (2 * (k : ℚ) + 1) * ((k : ℚ) + 1) * (↑N + 1) - 2 := by
    rw [Nat.cast_sub (by
      calc (2 : ℕ) = 2 * 1 * 1 := by norm_num
        _ ≤ (2 * k + 1) * (k + 1) * (N + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      : 2 ≤ (2 * k + 1) * (k + 1) * (N + 1))]
    push_cast
    ring
  have hcastN : (((N + 1) - 1 : ℕ) : ℚ) = (N : ℚ) := by
    rw [Nat.add_sub_cancel]
  have hD1ne' : ((k : ℚ) + 2) * (↑N + 1) - 1 ≠ 0 := by
    rw [← hD1cast]
    exact hD1ne
  have hD2ne' : ((k : ℚ) + 1) * (↑N + 1) + 1 ≠ 0 := by
    rw [← hD2cast]
    exact hD2ne
  have hD3ne' : ((k : ℚ) + 1) * (↑N + 1) + 2 ≠ 0 := by
    rw [← hD3cast]
    exact hD3ne
  have hk1ne' : (k : ℚ) + 1 ≠ 0 := by positivity
  have hk2ne' : (k : ℚ) + 2 ≠ 0 := by positivity
  -- The total count, from the first moment series.
  have hA : ((kBoxPaths k (N + 1)).card : ℚ) =
      ((k + 1 : ℕ) : ℚ) / (((k + 2) * (N + 1) - 1 : ℕ) : ℚ) * C0 := by
    have hcoeff : ((kBoxPaths k (N + 1)).card : ℚ) =
        coeff N (dyckGF (k + 1) ^ (k + 1)) := by
      rw [← coeff_eval_returnGF, eval_returnGF hk, coeff_succ_X_mul]
    have hF := coeff_dyckGF_pow (k := k) (m := k + 1) (N := N) hk (by omega)
    have e : (k + 2) * N + (k + 1) = (k + 2) * (N + 1) - 1 := by
      have e2 : (k + 2) * (N + 1) = (k + 2) * N + (k + 2) := by ring
      omega
    rw [e] at hF
    have hcast : (↑k + 2) * (↑N : ℚ) + ↑(k + 1) =
        (((k + 2) * (N + 1) - 1 : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ (k + 2) * (N + 1))]
      push_cast
      ring
    rw [hcoeff, hF, ← hC0, hcast]
  -- A ratio of binomial coefficients.
  have hR1 : (((k + 2) * (N + 1)).choose N : ℚ) =
      (((k + 2) * (N + 1) : ℕ) : ℚ) / (((k + 1) * (N + 1) + 1 : ℕ) : ℚ) * C0 := by
    have hℕ := Nat.choose_mul_succ_eq ((k + 2) * (N + 1) - 1) N
    have e1 : (k + 2) * (N + 1) - 1 + 1 = (k + 2) * (N + 1) :=
      Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))
    have e2 : (k + 2) * (N + 1) - N = (k + 1) * (N + 1) + 1 := by
      have hsplit : (k + 2) * (N + 1) = (k + 1) * (N + 1) + (N + 1) := by ring
      omega
    rw [e1, e2] at hℕ
    have hℚ : (C0 : ℚ) * (((k + 2) * (N + 1) : ℕ) : ℚ) =
        ((((k + 2) * (N + 1)).choose N : ℕ) : ℚ) *
          (((k + 1) * (N + 1) + 1 : ℕ) : ℚ) := by
      rw [hC0]
      exact_mod_cast hℕ
    rw [div_mul_eq_mul_div, eq_div_iff hD2ne]
    linear_combination -hℚ
  -- The first moment, from the first derivative series.
  have hS : (∑ w ∈ kBoxPaths k (N + 1), (skewReturns w : ℚ)) =
      ((k + 2 : ℕ) : ℚ) / (((k + 1) * (N + 1) + 1 : ℕ) : ℚ) * C0 := by
    have hcoeff : (∑ w ∈ kBoxPaths k (N + 1), (skewReturns w : ℚ)) =
        coeff N (dyckGF (k + 1) ^ (k + 2)) := by
      rw [← coeff_eval_derivT_returnGF, eval_derivT_returnGF hk, coeff_succ_X_mul]
    have hF := coeff_dyckGF_pow (k := k) (m := k + 2) (N := N) hk (by omega)
    have e : (k + 2) * N + (k + 2) = (k + 2) * (N + 1) := by ring
    rw [e] at hF
    rw [hcoeff, hF, hR1]
    have hDne : (((k + 2) * (N + 1) : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  -- The second ratio of binomial coefficients, for `N ≥ 1`.
  have hR2 (hN : 1 ≤ N) : (((k + 2) * (N + 1)).choose (N - 1) : ℚ) =
      ((N : ℚ) / (((k + 1) * (N + 1) + 2 : ℕ) : ℚ)) *
        (((k + 2) * (N + 1)).choose N : ℚ) := by
    have h := Nat.choose_succ_right_eq ((k + 2) * (N + 1)) (N - 1)
    rw [Nat.sub_add_cancel hN] at h
    have e2 : (k + 2) * (N + 1) - (N - 1) = (k + 1) * (N + 1) + 2 := by
      have hsplit : (k + 2) * (N + 1) = (k + 1) * (N + 1) + (N + 1) := by ring
      omega
    rw [e2] at h
    have hℚ : ((((k + 2) * (N + 1)).choose (N - 1) : ℕ) : ℚ) *
          (((k + 1) * (N + 1) + 2 : ℕ) : ℚ) =
        ((((k + 2) * (N + 1)).choose N : ℕ) : ℚ) * ((N : ℚ)) := by
      exact_mod_cast h.symm
    rw [div_mul_eq_mul_div, eq_div_iff hD3ne]
    linear_combination hℚ
  -- The falling factorial moment, from the second derivative series.
  have hQf : (∑ w ∈ kBoxPaths k (N + 1),
        (skewReturns w : ℚ) * ((skewReturns w : ℚ) - 1)) =
      4 * ((k + 2 : ℕ) : ℚ) * (N : ℚ) /
        ((((k + 1) * (N + 1) + 1 : ℕ) : ℚ) * (((k + 1) * (N + 1) + 2 : ℕ) : ℚ)) *
        C0 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [← coeff_eval_derivT_derivT_returnGF, eval_derivT_derivT_returnGF hk]
      rw [show (2 * PowerSeries.X ^ 2 * dyckGF (k + 1) ^ (2 * k + 4) :
          PowerSeries ℚ) = 2 * (PowerSeries.X ^ 2 *
          dyckGF (k + 1) ^ (2 * k + 4)) by rw [mul_assoc], coeff_ofNat_mul,
        coeff_X_pow_mul']
      simp [show ¬ (2 ≤ 0 + 1) by omega]
    · have hcoeff : (∑ w ∈ kBoxPaths k (N + 1),
          (skewReturns w : ℚ) * ((skewReturns w : ℚ) - 1)) =
          2 * coeff (N - 1) (dyckGF (k + 1) ^ (2 * k + 4)) := by
        rw [← coeff_eval_derivT_derivT_returnGF, eval_derivT_derivT_returnGF hk]
        rw [show (2 * PowerSeries.X ^ 2 * dyckGF (k + 1) ^ (2 * k + 4) :
            PowerSeries ℚ) = 2 * (PowerSeries.X ^ 2 *
            dyckGF (k + 1) ^ (2 * k + 4)) by rw [mul_assoc], coeff_ofNat_mul,
          coeff_X_pow_mul']
        simp [show 2 ≤ N + 1 by omega, show N + 1 - 2 = N - 1 by omega]
      have hF := coeff_dyckGF_pow (k := k) (m := 2 * k + 4) (N := N - 1) hk
        (by omega)
      have e : (k + 2) * (N - 1) + (2 * k + 4) = (k + 2) * (N + 1) := by
        obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
        rw [Nat.succ_eq_add_one, Nat.add_sub_cancel]
        ring
      have hcast : (↑k + 2) * (↑(N - 1) : ℚ) + ↑(2 * k + 4) =
          (((k + 2) * (N + 1) : ℕ) : ℚ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ N)]
        push_cast
        ring
      rw [e, hcast] at hF
      rw [hcoeff, hF, hR2 hN, hR1]
      have hDne : (((k + 2) * (N + 1) : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
  have hQ2 : (∑ w ∈ kBoxPaths k (N + 1), (skewReturns w : ℚ) ^ 2) =
      (∑ w ∈ kBoxPaths k (N + 1),
        (skewReturns w : ℚ) * ((skewReturns w : ℚ) - 1)) +
        ∑ w ∈ kBoxPaths k (N + 1), (skewReturns w : ℚ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  have hAne : ((kBoxPaths k (N + 1)).card : ℚ) ≠ 0 := by
    rw [hA]
    exact mul_ne_zero (div_ne_zero hk1ne hD1ne) (ne_of_gt hC0pos)
  have hA' : ((kBoxPaths k (N + 1)).card : ℚ) =
      ((k + 1 : ℕ) : ℚ) / (((k : ℚ) + 2) * (↑N + 1) - 1) * C0 := by
    rw [hA, hD1cast]
  have hS' : (∑ w ∈ kBoxPaths k (N + 1), (skewReturns w : ℚ)) =
      ((k + 2 : ℕ) : ℚ) / (((k : ℚ) + 1) * (↑N + 1) + 1) * C0 := by
    rw [hS, hD2cast]
  have hQf' : (∑ w ∈ kBoxPaths k (N + 1),
        (skewReturns w : ℚ) * ((skewReturns w : ℚ) - 1)) =
      4 * ((k + 2 : ℕ) : ℚ) * (N : ℚ) /
        ((((k : ℚ) + 1) * (↑N + 1) + 1) * (((k : ℚ) + 1) * (↑N + 1) + 2)) *
        C0 := by
    rw [hQf, hD2cast, hD3cast]
  constructor
  · rw [hS', hA']
    push_cast
    field_simp
  · rw [hQ2, hQf', hS', hA']
    push_cast
    field_simp
    ring

end MetaMathlibExt
