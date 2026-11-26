/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.PowerSeries.UnifiedCatalanTypePolynomials

/-!
# Hermite-shifted Catalan-type convolutions

The shifted Hermite kernel is obtained by iterating the formal derivative of the
quadratic exponential. Its product with any series then has the claimed coefficient
convolution, without needing to expand either trinomial.
-/

namespace MetaMathlibExt

open PowerSeries

private noncomputable def quadraticExp {A : Type*} [CommRing A] [Algebra ℚ A]
    (x y : A) : PowerSeries A :=
  (exp A).subst (C x * X + C y * X ^ 2 : PowerSeries A)

private theorem derivative_quadraticExp {A : Type*} [CommRing A] [Algebra ℚ A] (x y : A) :
    d⁄dX (quadraticExp x y) = (C x + C (2 * y) * X) * quadraticExp x y := by
  unfold quadraticExp
  rw [derivative_subst (HasSubst.of_constantCoeff_zero' (by simp)), derivative_exp,
    map_add, derivative_C_mul_X, derivative_C_mul_X_sq, mul_comm y 2, mul_comm]

private theorem isUnit_natCast_succ {A : Type*} [CommRing A] [Algebra ℚ A] (n : ℕ) :
    IsUnit ((n + 1 : ℕ) : A) := by
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simpa using hn.isUnit.map (algebraMap ℚ A)

-- The differential equation `F' = (x + bt)F` determines the coefficients from `F(0)`.
private theorem eq_of_derivative_linear_mul {A : Type*} [CommRing A] [Algebra ℚ A]
    (x b : A) {F G : PowerSeries A} (hF : d⁄dX F = (C x + C b * X) * F)
    (hG : d⁄dX G = (C x + C b * X) * G)
    (h0 : constantCoeff F = constantCoeff G) : F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simpa using h0
    | succ n =>
      apply (isUnit_natCast_succ (A := A) n).mul_right_cancel
      rw [Nat.cast_succ, ← coeff_derivative, ← coeff_derivative, hF, hG]
      simp only [add_mul, map_add, mul_assoc, coeff_C_mul]
      rw [ih n (Nat.lt_succ_self n)]
      cases n with
      | zero => simp
      | succ j => rw [coeff_succ_X_mul, coeff_succ_X_mul, ih j (by omega)]

-- Splitting the exponential reduces the generating-function calculation to a convolution
-- in which the quadratic factor contributes only at even indices.
private theorem quadraticExp_eq_mul {A : Type*} [CommRing A] [Algebra ℚ A] (x y : A) :
    quadraticExp x y = rescale x (exp A) *
      (rescale y (exp A)).subst (X ^ 2 : PowerSeries A) := by
  have hX2 : HasSubst (X ^ 2 : PowerSeries A) := HasSubst.X_pow (by decide)
  have hquad : (rescale y (exp A)).subst (X ^ 2 : PowerSeries A) =
      (exp A).subst (C y * X ^ 2 : PowerSeries A) := by
    rw [rescale_eq_subst y, subst_comp_subst_apply (HasSubst.smul_X' y) hX2,
      subst_smul hX2, subst_X hX2, smul_eq_C_mul]
  have hconst (u : PowerSeries A) (hu : constantCoeff u = 0) :
      constantCoeff ((exp A).subst u) = 1 := by
    change MvPowerSeries.constantCoeff ((exp A).subst u) = 1
    rw [constantCoeff_subst_of_constantCoeff_zero hu]
    simp
  rw [rescale_eq_subst x, smul_eq_C_mul, hquad]
  apply eq_of_derivative_linear_mul x (2 * y) (derivative_quadraticExp x y)
  · rw [Derivation.leibniz,
      derivative_subst (g := C y * X ^ 2) (HasSubst.of_constantCoeff_zero' (by simp)),
      derivative_subst (g := C x * X) (HasSubst.of_constantCoeff_zero' (by simp)),
      derivative_exp, derivative_C_mul_X, derivative_C_mul_X_sq, mul_comm y 2]
    simp only [smul_eq_mul]
    ring
  · rw [quadraticExp, map_mul, hconst _ (by simp), hconst _ (by simp), hconst _ (by simp), mul_one]

private theorem coeff_rescale_exp {A : Type*} [CommRing A] [Algebra ℚ A] [Algebra ℝ A]
    [IsScalarTower ℚ ℝ A] (x : A) (n : ℕ) :
    coeff n (rescale x (exp A)) = x ^ n * algebraMap ℝ A (1 / (n.factorial : ℝ)) := by
  rw [coeff_rescale, coeff_exp, IsScalarTower.algebraMap_apply ℚ ℝ A]
  change x ^ n * algebraMap ℝ A (↑(1 / (n.factorial : ℚ)) : ℝ) = _
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]

private theorem factorial_mul_coeff_quadraticExp {A : Type*} [CommRing A] [Algebra ℚ A]
    [Algebra ℝ A] [IsScalarTower ℚ ℝ A] (x y : A) (n : ℕ) :
    (n.factorial : A) * coeff n (quadraticExp x y) = kampeDeFerietHermite 2 n x y := by
  rw [quadraticExp_eq_mul, mul_comm (rescale x (exp A)), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  simp only [coeff_subst_X_pow (by decide : (2 : ℕ) ≠ 0), Algebra.algebraMap_self_apply,
    ite_mul, zero_mul, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  unfold kampeDeFerietHermite
  symm
  refine Finset.sum_nbij' (fun r ↦ 2 * r) (fun j ↦ j / 2) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_range, Finset.mem_filter] at hr ⊢
    exact ⟨by omega, dvd_mul_right 2 r⟩
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_filter] at hj ⊢
    omega
  · intro r _
    omega
  · intro j hj
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hj).2
  · intro r _
    rw [show 2 * r / 2 = r by omega, coeff_rescale_exp, coeff_rescale_exp, Algebra.smul_def]
    have h : (n.factorial : ℝ) * (1 / (r.factorial : ℝ)) *
        (1 / ((n - 2 * r).factorial : ℝ)) =
        (n.factorial : ℝ) / ((r.factorial : ℝ) * ((n - 2 * r).factorial : ℝ)) := by
      field_simp
    rw [← h, map_mul, map_mul, map_natCast]
    ring

private theorem hermite_succ_succ {A : Type*} [CommRing A] [Algebra ℚ A] [Algebra ℝ A]
    [IsScalarTower ℚ ℝ A] (x y : A) (k : ℕ) :
    kampeDeFerietHermite 2 (k + 2) x y = x * kampeDeFerietHermite 2 (k + 1) x y +
      (2 * y) * (k + 1 : A) * kampeDeFerietHermite 2 k x y := by
  have h := congrArg (coeff (k + 1)) (derivative_quadraticExp x y)
  simp only [coeff_derivative, add_mul, map_add, mul_assoc, coeff_C_mul, coeff_succ_X_mul] at h
  simp only [← factorial_mul_coeff_quadraticExp]
  calc
    _ = (↑(k + 1).factorial : A) * (coeff (k + 2) (quadraticExp x y) * (↑(k + 1) + 1)) := by
      rw [Nat.factorial_succ (k + 1), Nat.cast_mul, Nat.cast_succ (k + 1)]
      ring
    _ = _ := by
      rw [h, Nat.factorial_succ k, Nat.cast_mul, Nat.cast_succ]
      ring

-- Differentiating one more time gives the same two-step recurrence, since the factor in
-- the differential equation is linear and its derivative is constant.
private theorem iterate_derivative_quadraticExp_succ_succ (x y : ℝ) (k : ℕ) :
    d⁄dX^[k + 2] (quadraticExp x y) =
      (C x + C (2 * y) * X) * d⁄dX^[k + 1] (quadraticExp x y) +
        C (2 * y) * C (k + 1 : ℝ) * d⁄dX^[k] (quadraticExp x y) := by
  let Q : PowerSeries ℝ := C x + C (2 * y) * X
  have hQ : d⁄dX Q = C (2 * y) := by simp [Q]
  change _ = Q * _ + _
  induction k with
  | zero =>
    rw [Function.iterate_succ_apply' (n := 1), Function.iterate_one,
      derivative_quadraticExp, ← show Q = C x + C (2 * y) * X from rfl,
      Derivation.leibniz, hQ]
    simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_add,
      map_one, mul_one, smul_eq_mul]
    rw [derivative_quadraticExp]
    ring
  | succ k ih =>
    calc
      _ = d⁄dX (Q * d⁄dX^[k + 1] (quadraticExp x y) +
          C (2 * y) * C (k + 1 : ℝ) * d⁄dX^[k] (quadraticExp x y)) := by
        rw [← ih, Function.iterate_succ_apply']
      _ = _ := by
        simp only [map_add, Derivation.leibniz, hQ, derivative_C, smul_eq_mul, mul_zero,
          add_zero, ← Function.iterate_succ_apply', Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
          map_one, derivative_one]
        ring

private theorem iterate_derivative_quadraticExp (x y : ℝ) (k : ℕ) :
    d⁄dX^[k] (quadraticExp x y) =
      quadraticExp x y * kampeDeFerietHermite 2 k (C x + C (2 * y) * X) (C y) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [kampeDeFerietHermite_zero]
  | one =>
    rw [Function.iterate_one, derivative_quadraticExp]
    norm_num [kampeDeFerietHermite, mul_comm]
  | more k ih₀ ih₁ =>
    rw [iterate_derivative_quadraticExp_succ_succ, ih₀, ih₁, hermite_succ_succ]
    simp only [map_mul, map_ofNat, map_add, map_one, map_natCast]
    ring

private theorem coeff_hermiteShift (k n : ℕ) (x y : ℝ) :
    coeff n (quadraticExp x y * kampeDeFerietHermite 2 k (C x + C (2 * y) * X) (C y)) =
      kampeDeFerietHermite 2 (n + k) x y / (n.factorial : ℝ) := by
  rw [← iterate_derivative_quadraticExp, coeff_iterate_derivative, eq_div_iff (by positivity),
    ← factorial_mul_coeff_quadraticExp]
  have h := congrArg (fun a : ℕ ↦ (a : ℝ)) (Nat.factorial_mul_ascFactorial n k)
  push_cast at h
  rw [← h]
  ring

/-- **Hermite-shifted Catalan-type polynomials as convolutions.** Write $H_n(x, y) = H^2_n(x, y)$
for the Kampé de Fériet polynomials. For a natural number $m$ and real numbers $\lambda, z$,
write $(1 - m t + z t^m)^{-\lambda}$ and $(1 - m z t + t^m)^{-\lambda}$ for the negative real
powers of the trinomials $1 - m t + z t^m$ and $1 - m z t + t^m$ with exponent $\lambda$ as
power series in $t$ (for $m \ge 1$ these are their expansions in powers of $t$), and let
$P^\lambda_{r,m}(z)$ and $h^\lambda_{r,m}(z)$ be their coefficients of $t^r$. For all natural
numbers $k, m, n$ and real numbers $\lambda, x, y, z$, as formal power series in $t$ (with
$e^{xt + yt^2}$ the exponential series and $H_k(x + 2yt, y)$ evaluated in power series), the
coefficient of $t^n$ in $e^{xt + yt^2} H_k(x + 2yt, y) (1 - m t + z t^m)^{-\lambda}$ is
$\sum_{r=0}^{n} H_{n-r+k}(x, y) P^\lambda_{r,m}(z) / (n - r)!$, and the coefficient of $t^n$
in $e^{xt + yt^2} H_k(x + 2yt, y) (1 - m z t + t^m)^{-\lambda}$ is
$\sum_{r=0}^{n} H_{n-r+k}(x, y) h^\lambda_{r,m}(z) / (n - r)!$.

These coefficients are the paper's $H^{k;\lambda}_{n,m}(x, y, z)$ and
$h^{k;\lambda}_{n,m}(x, y, z)$ (Definition 3, Equations (8) and (9)).

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 2
(`integers-2026-A105-thm-2`). -/
public theorem coeff_hermiteShift_mul_trinomialNegPowSeries (k m n : ℕ)
    (lam x y z : ℝ) :
    let G : PowerSeries ℝ := ((exp ℝ).subst (C x * X + C y * X ^ 2 : PowerSeries ℝ) :
        PowerSeries ℝ) * kampeDeFerietHermite 2 k (C x + C (2 * y) * X) (C y)
    coeff n (G * trinomialNegPowSeries lam 1 m z m) =
        ∑ r ∈ Finset.range (n + 1), kampeDeFerietHermite 2 (n - r + k) x y /
          ((n - r).factorial : ℝ) * coeff r (trinomialNegPowSeries lam 1 m z m) ∧
      coeff n (G * trinomialNegPowSeries lam 1 (m * z) 1 m) =
        ∑ r ∈ Finset.range (n + 1), kampeDeFerietHermite 2 (n - r + k) x y /
          ((n - r).factorial : ℝ) * coeff r (trinomialNegPowSeries lam 1 (m * z) 1 m) := by
  intro G
  -- Use the second index of the coefficient antidiagonal for the trinomial factor.
  have convolution (F : PowerSeries ℝ) : coeff n (G * F) =
      ∑ r ∈ Finset.range (n + 1), kampeDeFerietHermite 2 (n - r + k) x y /
        ((n - r).factorial : ℝ) * coeff r F := by
    rw [mul_comm G F, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    change coeff r F * coeff (n - r) (quadraticExp x y *
      kampeDeFerietHermite 2 k (C x + C (2 * y) * X) (C y)) = _
    rw [coeff_hermiteShift, mul_comm]
  exact ⟨convolution _, convolution _⟩

end MetaMathlibExt
