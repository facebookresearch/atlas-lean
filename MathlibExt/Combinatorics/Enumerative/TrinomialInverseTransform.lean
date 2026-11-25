/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Ring

/-!
# The inverse trinomial transform

We prove the coefficient-extraction formula for the inverse 2-Pascal transform
by simplifying the two series of the Riordan array after substitution.
-/

open PowerSeries

namespace MetaMathlibExt

private theorem eq_of_sq_eq_of_constantCoeff {p q : PowerSeries ℚ}
    (h : p ^ 2 = q ^ 2) (h₀ : constantCoeff p = constantCoeff q) (hq : constantCoeff q ≠ 0) :
    p = q := by
  rcases eq_or_eq_neg_of_sq_eq_sq p q h with hpq | hpq
  · exact hpq
  · rw [hpq, map_neg, neg_eq_iff_add_eq_zero, ← two_mul, mul_eq_zero] at h₀
    exact (hq (h₀.resolve_left two_ne_zero)).elim

private theorem constantCoeff_subst_zero {u : PowerSeries ℚ}
    (hu : constantCoeff u = 0) (p : PowerSeries ℚ) :
    constantCoeff (p.subst u : PowerSeries ℚ) = constantCoeff p := by
  simpa only [constantCoeff_eq, Algebra.algebraMap_self, RingHom.id_apply] using
    constantCoeff_subst_of_constantCoeff_zero hu p

private theorem subst_inv_of_constantCoeff_ne_zero {u p : PowerSeries ℚ}
    (hu : constantCoeff u = 0) (hp : constantCoeff p ≠ 0) :
    p⁻¹.subst u = (p.subst u)⁻¹ := by
  have hu' := HasSubst.of_constantCoeff_zero' hu
  have hp' : constantCoeff (p.subst u : PowerSeries ℚ) ≠ 0 := by
    simpa only [constantCoeff_subst_zero hu] using hp
  apply (eq_inv_iff_mul_eq_one hp').2
  rw [← subst_mul hu', PowerSeries.inv_mul_cancel _ hp, ← coe_substAlgHom hu', map_one]

private theorem coeff_mul_mobius_subst (f : PowerSeries ℚ) (m : ℕ) :
    coeff m ((1 - X) ^ m * (1 - X)⁻¹ * f.subst (X * (1 - X)⁻¹)) = coeff m f := by
  let A : PowerSeries ℚ := 1 - X
  let v : PowerSeries ℚ := X * A⁻¹
  have hA : constantCoeff A = 1 := by simp [A]
  have hv : constantCoeff v = 0 := by simp [v]
  have hv' := HasSubst.of_constantCoeff_zero' hv
  change coeff m (A ^ m * A⁻¹ * f.subst v) = coeff m f
  induction m generalizing f with
  | zero =>
    simp [coeff_zero_eq_constantCoeff, hA, constantCoeff_subst_zero hv]
  | succ m ih =>
    let s := mk fun i => coeff (i + 1) f
    have hsplit : f.subst v = v * s.subst v + C (constantCoeff f) := by
      conv_lhs => rw [eq_X_mul_shift_add_const f]
      rw [subst_add hv', subst_mul hv', subst_X hv', subst_C, C_apply]
    have hcancel : A ^ (m + 1) * A⁻¹ = A ^ m := by
      rw [pow_succ, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp [hA]), mul_one]
    -- The constant part of f contributes a polynomial of degree at most m.
    have hpoly : coeff (m + 1) (A ^ m) = 0 := by
      rw [show A ^ m = (((1 - Polynomial.X : Polynomial ℚ) ^ m : Polynomial ℚ) : PowerSeries ℚ)
        by simp [A], Polynomial.coeff_coe]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hd : (1 - Polynomial.X : Polynomial ℚ).natDegree ≤ 1 :=
        (Polynomial.natDegree_sub_le _ _).trans (by simp)
      exact (Polynomial.natDegree_pow_le_of_le m hd).trans_lt (by simp)
    rw [hsplit, mul_add, map_add, hcancel, coeff_mul_C, hpoly, zero_mul, add_zero]
    have heq : A ^ m * (v * s.subst v) = X * (A ^ m * A⁻¹ * s.subst v) := by
      dsimp [v]
      ring
    rw [heq, coeff_succ_X_mul, ih, coeff_mk]

/-- **Recovering even coefficients from the 2-Pascal transform.** Write $[t^m]F$ for the
coefficient of $t^m$ in a power series $F$. Let $S$, $Q$, $R$ be power series over $\mathbb{Q}$
with $S^2 = 4 - 3t^2$, $S(0) = 2$, $2Q^2 = 2 - t^2 - tS$, $Q(0) = 1$, $R^2 = 1 - t + t^2$ and
$R(0) = 1$, and put

$$\alpha = \frac{-2(2Q + t^2 S - t)}{Q(3t^4 + 2tS - t^2 - 4)}, \qquad
\beta = \frac{t(t + S)}{2(1 - t^2)}.$$

For a power series $f$ over $\mathbb{Q}$ let $g(t) = \alpha(t)\,f(\beta(t))$. Then for every
$n \in \mathbb{N}$,

$$[t^{2n}]\,f = [t^{2n}]\,\frac{(2 - t)(1 - t)^{2n}}{2(1 - t + t^2)}\,g\!\left(\frac{t}{R}\right).$$

Here $S$, $Q$, $R$ are the square roots $\sqrt{4 - 3t^2}$, $\sqrt{(2 - t^2 - tS)/2}$ and
$\sqrt{1 - t + t^2}$, and $\alpha$, $\beta$ are the series of the paper's Theorem 6.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 49 (`jis-2025-25.3.5-cor-49`). -/
public theorem coeff_two_mul_eq_inverse_trinomial_transform (S Q R : PowerSeries ℚ)
    (hS : S ^ 2 = 4 - 3 * X ^ 2) (hS0 : constantCoeff S = 2)
    (hQ : 2 * Q ^ 2 = 2 - X ^ 2 - X * S) (hQ0 : constantCoeff Q = 1)
    (hR : R ^ 2 = 1 - X + X ^ 2) (hR0 : constantCoeff R = 1) (f : PowerSeries ℚ) (n : ℕ) :
    let α := -2 * (2 * Q + X ^ 2 * S - X) * (Q * (3 * X ^ 4 + 2 * X * S - X ^ 2 - 4))⁻¹
    let β := X * (X + S) * (2 * (1 - X ^ 2))⁻¹
    let g := α * f.subst β
    coeff (2 * n) f = coeff (2 * n) ((2 - X) * (1 - X) ^ (2 * n) * (2 * (1 - X + X ^ 2))⁻¹ *
      g.subst (X * R⁻¹)) := by
  intro α β g
  let u : PowerSeries ℚ := X * R⁻¹
  let P : PowerSeries ℚ := 1 - X + X ^ 2
  have hR0' : constantCoeff R ≠ 0 := by simp [hR0]
  have hRne : R ≠ 0 := fun h => hR0' (by simp [h])
  have hu : constantCoeff u = 0 := by simp [u]
  have hu' := HasSubst.of_constantCoeff_zero' hu
  have huR : u * R = X := by simp [u, mul_assoc, PowerSeries.inv_mul_cancel _ hR0']
  let s : PowerSeries ℚ := S.subst u
  let q : PowerSeries ℚ := Q.subst u
  have hs : s ^ 2 = 4 - 3 * u ^ 2 := by
    have h := congrArg (substAlgHom hu' : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ) hS
    simpa only [map_pow, map_sub, map_mul, map_ofNat, substAlgHom_X, coe_substAlgHom] using h
  have hq : 2 * q ^ 2 = 2 - u ^ 2 - u * s := by
    have h := congrArg (substAlgHom hu' : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ) hQ
    simpa only [map_pow, map_sub, map_mul, map_ofNat, substAlgHom_X, coe_substAlgHom] using h
  have hsR : s * R = 2 - X := by
    apply eq_of_sq_eq_of_constantCoeff
    · calc
        (s * R) ^ 2 = 4 * R ^ 2 - 3 * (u * R) ^ 2 := by rw [mul_pow, hs, mul_pow]; ring
        _ = (2 - X) ^ 2 := by rw [hR, huR]; ring
    · simp [s, hR0, constantCoeff_subst_zero hu, hS0, map_ofNat]
    · norm_num [map_ofNat]
  have hqR : q * R = 1 - X := by
    apply eq_of_sq_eq_of_constantCoeff
    · have htwo : (2 : PowerSeries ℚ) ≠ 0 := by
        intro h
        have h' := congrArg (constantCoeff (R := ℚ)) h
        norm_num [map_ofNat] at h'
      apply mul_left_cancel₀ htwo
      calc
        2 * (q * R) ^ 2 = (2 * q ^ 2) * R ^ 2 := by ring
        _ = 2 * R ^ 2 - (u * R) ^ 2 - (u * R) * (s * R) := by rw [hq]; ring
        _ = 2 * (1 - X) ^ 2 := by rw [hR, huR, hsR]; ring
    · simp [q, hR0, constantCoeff_subst_zero hu, hQ0]
    · simp
  have hβ₀ : constantCoeff β = 0 := by simp [β]
  have hβu : (PowerSeries.subst u β : PowerSeries ℚ) = X * (1 - X)⁻¹ := by
    have hden : constantCoeff (2 * (1 - X ^ 2) : PowerSeries ℚ) ≠ 0 := by norm_num [map_ofNat]
    have hden' : constantCoeff (2 * (1 - u ^ 2)) ≠ 0 := by norm_num [map_ofNat, hu]
    have hβform : (PowerSeries.subst u β : PowerSeries ℚ) =
        u * (u + s) * (2 * (1 - u ^ 2))⁻¹ := by
      dsimp only [β, s]
      rw [subst_mul hu', subst_inv_of_constantCoeff_ne_zero hu hden]
      simp only [← coe_substAlgHom hu', map_add, map_mul, map_sub, map_pow, map_one, map_ofNat,
        substAlgHom_X]
    rw [hβform, eq_comm, eq_mul_inv_iff_mul_eq hden']
    apply mul_right_cancel₀ (pow_ne_zero 2 hRne)
    have hfactor : 2 * (1 - u ^ 2) * R ^ 2 = 2 * (1 - X) := by
      calc
        2 * (1 - u ^ 2) * R ^ 2 = 2 * (R ^ 2 - (u * R) ^ 2) := by ring
        _ = _ := by rw [hR, huR]; ring
    calc
      X * (1 - X)⁻¹ * (2 * (1 - u ^ 2)) * R ^ 2 =
          2 * X * ((1 - X)⁻¹ * (1 - X)) := by rw [mul_assoc (X * (1 - X)⁻¹), hfactor]; ring
      _ = 2 * X := by rw [PowerSeries.inv_mul_cancel _ (by simp), mul_one]
      _ = u * (u + s) * R ^ 2 := by
        calc
          2 * X = (u * R) * (u * R + s * R) := by rw [huR, hsR]; ring
          _ = _ := by ring
  let N : PowerSeries ℚ := -2 * (2 * q + u ^ 2 * s - u)
  let D : PowerSeries ℚ := q * (3 * u ^ 4 + 2 * u * s - u ^ 2 - 4)
  have hαform : (α.subst u : PowerSeries ℚ) = N * D⁻¹ := by
    have hden : constantCoeff (Q * (3 * X ^ 4 + 2 * X * S - X ^ 2 - 4)) ≠ 0 := by
      norm_num [hQ0, map_ofNat]
    dsimp only [α, N, D, q, s]
    rw [subst_mul hu', subst_inv_of_constantCoeff_ne_zero hu hden]
    simp only [← coe_substAlgHom hu', map_add, map_mul, map_sub, map_pow, map_neg, map_ofNat,
      substAlgHom_X]
  have hαu : (2 - X) * (2 * P)⁻¹ * α.subst u = (1 - X)⁻¹ := by
    have hidentity : (2 - X) * (1 - X) * N = (2 * P) * D := by
      -- Clear the powers of R from the numerator and denominator separately.
      have hN : N * R ^ 3 = -2 * (2 * (1 - X) * P + X ^ 2 * (2 - X) - X * P) := by
        calc
          N * R ^ 3 = -2 * (2 * (q * R) * R ^ 2 + (u * R) ^ 2 * (s * R) - (u * R) * R ^ 2) := by
            dsimp [N]; ring
          _ = _ := by rw [hqR, huR, hsR, hR]
      have hD : D * R ^ 5 =
          (1 - X) * (3 * X ^ 4 + 2 * X * (2 - X) * P - X ^ 2 * P - 4 * P ^ 2) := by
        calc
          D * R ^ 5 = (q * R) * (3 * (u * R) ^ 4 + 2 * (u * R) * (s * R) * R ^ 2 -
              (u * R) ^ 2 * R ^ 2 - 4 * (R ^ 2) ^ 2) := by dsimp [D]; ring
          _ = _ := by rw [hqR, huR, hsR, hR]
      apply mul_right_cancel₀ (pow_ne_zero 5 hRne)
      calc
        (2 - X) * (1 - X) * N * R ^ 5 = (2 - X) * (1 - X) * (N * R ^ 3) * R ^ 2 := by ring
        _ = (2 * P) * (D * R ^ 5) := by rw [hN, hD, hR]; dsimp [P]; ring
        _ = (2 * P) * D * R ^ 5 := by ring
    have hP : constantCoeff (2 * P) ≠ 0 := by norm_num [P, map_ofNat]
    have hD : constantCoeff D ≠ 0 := by
      have hq₀ : constantCoeff q = 1 := by
        simp [q, constantCoeff_subst_zero hu, hQ0]
      norm_num [D, hq₀, hu, map_ofNat]
    rw [hαform, eq_inv_iff_mul_eq_one (by simp)]
    calc
      (2 - X) * (2 * P)⁻¹ * (N * D⁻¹) * (1 - X) =
          ((2 - X) * (1 - X) * N) * ((2 * P)⁻¹ * D⁻¹) := by ring
      _ = ((2 * P)⁻¹ * (2 * P)) * (D⁻¹ * D) := by rw [hidentity]; ring
      _ = 1 := by rw [PowerSeries.inv_mul_cancel _ hP, PowerSeries.inv_mul_cancel _ hD, mul_one]
  have hg : (g.subst u : PowerSeries ℚ) = α.subst u * f.subst (X * (1 - X)⁻¹) := by
    dsimp only [g]
    rw [subst_mul hu', subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hβ₀) hu', hβu]
  change coeff (2 * n) f = coeff (2 * n) ((2 - X) * (1 - X) ^ (2 * n) * (2 * P)⁻¹ * g.subst u)
  rw [hg, show (2 - X) * (1 - X) ^ (2 * n) * (2 * P)⁻¹ *
        (α.subst u * f.subst (X * (1 - X)⁻¹)) =
      (1 - X) ^ (2 * n) * ((2 - X) * (2 * P)⁻¹ * α.subst u) * f.subst (X * (1 - X)⁻¹) by ring,
    hαu, coeff_mul_mobius_subst]

end MetaMathlibExt
