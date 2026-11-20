/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.EllipsoidMethod
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Volumes of ellipsoids and the volume lemma of the ellipsoid method

The ellipsoid `E(a, A)` is the translate of the image of the Euclidean unit ball under the positive
square root `A^(1/2)` (continuous functional calculus), so its Lebesgue volume is
`√(det A) · vol E(0, I)`. With the determinant of the central-cut update this gives the exact volume
factor `(n / (n + 1)) (n² / (n² - 1))^((n - 1) / 2)` of one step, and the volume lemma
`vol E(a', A') < exp(-1 / (2 (n + 1))) · vol E(a, A)`.

Source: M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial
Optimization, Handout 19 (4 May 2009), Definition 7.1 and Lemma 7.1 with its proof.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.EllipsoidMethod

open Matrix MeasureTheory
open scoped MatrixOrder

variable {n : ℕ}

/-- **An ellipsoid is the image of the unit ball.** For positive definite `A`, `E(0, A) = A^(1/2)
E(0, I)`, where `A^(1/2)` is the positive square root of `A` given by the continuous functional
calculus (Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433, 2009, Definition 7.1,
where `A = BᵀB`). -/
theorem ellipsoid_zero_eq_image {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ellipsoid 0 A = (Matrix.toLin' (CFC.sqrt A)) '' ellipsoid 0 1 := by
  set S := CFC.sqrt A with hSdef
  have h0 : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ A := hA.posSemidef.nonneg
  have hSS : S * S = A := by rw [← sq]; exact CFC.sq_sqrt A h0
  have hSpsd : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hdetS : S.det ≠ 0 := by
    intro h
    have : A.det = 0 := by rw [← hSS, det_mul, h, zero_mul]
    exact hA.det_pos.ne' this
  have hSunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hdetS
  have hSinv_sym : (S⁻¹)ᵀ = S⁻¹ := by
    have := hSpsd.inv.1.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hAinv : A⁻¹ = S⁻¹ * S⁻¹ := by rw [← hSS, Matrix.mul_inv_rev]
  ext x
  simp only [ellipsoid, Set.mem_ofPred_eq, Set.mem_image, sub_zero, inv_one, one_mulVec]
  constructor
  · intro hx
    refine ⟨S⁻¹ *ᵥ x, ?_, ?_⟩
    · rw [hAinv, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hSinv_sym] at hx
      rw [dotProduct_comm] at hx
      exact hx
    · rw [Matrix.toLin'_apply, mulVec_mulVec, mul_nonsing_inv _ hSunit, one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    have hy' : S⁻¹ *ᵥ (S *ᵥ y) = y := by
      rw [mulVec_mulVec, nonsing_inv_mul _ hSunit, one_mulVec]
    rw [Matrix.toLin'_apply, hAinv, ← mulVec_mulVec, hy', dotProduct_mulVec, ← mulVec_transpose,
      hSinv_sym, hy']
    exact hy

/-- **Volume of an ellipsoid.** For positive definite `A`, the Lebesgue volume of `E(a, A)` is
`√(det A)` times the volume of the Euclidean unit ball `E(0, I)`: the ellipsoid is the translate by
`a` of the image of the ball under `A^(1/2)`, whose determinant is `√(det A)` (Goemans, *Lecture
notes on the ellipsoid algorithm*, MIT 18.433, 2009, proof of Lemma 7.1). -/
theorem volume_ellipsoid {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (a : Fin n → ℝ) :
    volume (ellipsoid a A) =
      ENNReal.ofReal (Real.sqrt A.det) * volume (ellipsoid 0 (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  have htrans : ellipsoid a A = (fun x => x + -a) ⁻¹' ellipsoid 0 A := by
    ext x; simp [ellipsoid, sub_eq_add_neg]
  rw [htrans, measure_preimage_add_right, ellipsoid_zero_eq_image hA,
    Measure.addHaar_image_linearMap, LinearMap.det_toLin', hA.posSemidef.det_sqrt]
  rw [RCLike.sqrt_real, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- **The central-cut matrix is positive definite.** For `n ≥ 2`, positive definite `A` and `c ≠ 0`,
the matrix `A'` of the central-cut step is positive definite, so `E(a', A')` is again an ellipsoid:
its inverse `(n² - 1) / n² · (A⁻¹ + 2 / (n - 1) · c cᵀ / (cᵀ A c))` is positive definite. -/
theorem nextMatrix_posDef (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {c : Fin n → ℝ} (hc : c ≠ 0) : (nextMatrix A c).PosDef := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hN2 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hpos : 0 < c ⬝ᵥ (A *ᵥ c) := by simpa using hA.dotProduct_mulVec_pos hc
  have hdet : 0 < (nextMatrix A c).det := by
    rw [det_nextMatrix hA hc]
    have : (0 : ℝ) < ((n : ℝ) - 1) / ((n : ℝ) + 1) := by positivity
    have := hA.det_pos
    positivity
  have hinv : (nextMatrix A c)⁻¹.PosDef := by
    rw [nextMatrix_inv hA hc hn]
    apply PosDef.smul _ (by positivity)
    apply hA.inv.add_posSemidef
    apply PosSemidef.smul _ (by positivity)
    simpa using posSemidef_vecMulVec_self_star c
  have := hinv.inv
  rwa [nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet.ne')] at this

/-- **Exact volume factor of a central-cut step.** For `n ≥ 2`, positive definite `A` and `c ≠ 0`,
`vol E(a', A') = (n / (n + 1)) (n² / (n² - 1))^((n - 1) / 2) · vol E(a, A)` (Goemans, *Lecture notes
on the ellipsoid algorithm*, MIT 18.433, 2009, proof of Lemma 7.1). -/
theorem volume_nextEllipsoid (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (a : Fin n → ℝ) {c : Fin n → ℝ} (hc : c ≠ 0) :
    volume (ellipsoid (nextCenter a A c) (nextMatrix A c)) =
      ENNReal.ofReal (volumeRatio n) * volume (ellipsoid a A) := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hN2 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hq : (0 : ℝ) ≤ ((n : ℝ) - 1) / ((n : ℝ) + 1) := by
    apply div_nonneg <;> linarith
  have hprod : (0 : ℝ) ≤ ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n * (((n : ℝ) - 1) / ((n : ℝ) + 1)) :=
    by positivity
  rw [volume_ellipsoid (nextMatrix_posDef hn hA hc), volume_ellipsoid hA, det_nextMatrix hA hc,
    Real.sqrt_mul hprod, sqrt_detRatio_eq_volumeRatio hn,
    ENNReal.ofReal_mul (volumeRatio_pos hn).le, mul_assoc]

/-- **The Euclidean unit ball lies in the unit cube.** `E(0, I) = {x : xᵀ x ≤ 1}` is contained in
the closed ball of radius `1` for the sup norm of `Fin n → ℝ`. -/
theorem unitEllipsoid_subset_closedBall :
    ellipsoid 0 (1 : Matrix (Fin n) (Fin n) ℝ) ⊆ Metric.closedBall 0 1 := by
  intro x hx
  simp only [ellipsoid, Set.mem_ofPred_eq, sub_zero, inv_one, one_mulVec] at hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have hi : x i * x i ≤ x ⬝ᵥ x :=
    Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
      (Finset.mem_univ i)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

/-- **The Euclidean unit ball contains a small cube.** The open sup-norm ball of radius `1 / (n +
1)` is contained in `E(0, I) = {x : xᵀ x ≤ 1}`. -/
theorem ball_subset_unitEllipsoid :
    Metric.ball (0 : Fin n → ℝ) (1 / ((n : ℝ) + 1)) ⊆
      ellipsoid 0 (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro x hx
  simp only [ellipsoid, Set.mem_ofPred_eq, sub_zero, inv_one, one_mulVec]
  rw [mem_ball_zero_iff] at hx
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbound : ∀ i, x i * x i ≤ (1 / ((n : ℝ) + 1)) ^ 2 := by
    intro i
    have h1 : |x i| ≤ ‖x‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x i
    have h2 : |x i| < 1 / ((n : ℝ) + 1) := lt_of_le_of_lt h1 hx
    rw [← abs_mul_abs_self, sq]
    exact mul_le_mul h2.le h2.le (abs_nonneg _) (by positivity)
  calc x ⬝ᵥ x = ∑ i, x i * x i := rfl
    _ ≤ ∑ _i : Fin n, (1 / ((n : ℝ) + 1)) ^ 2 := Finset.sum_le_sum fun i _ => hbound i
    _ = (n : ℝ) * (1 / ((n : ℝ) + 1)) ^ 2 := by simp
    _ ≤ 1 := by
      rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
      nlinarith

/-- **The Euclidean unit ball has positive volume.** -/
theorem volume_unitEllipsoid_pos :
    0 < volume (ellipsoid 0 (1 : Matrix (Fin n) (Fin n) ℝ)) :=
  lt_of_lt_of_le (Metric.measure_ball_pos volume _ (by positivity))
    (measure_mono ball_subset_unitEllipsoid)

/-- **The Euclidean unit ball has finite volume.** -/
theorem volume_unitEllipsoid_lt_top :
    volume (ellipsoid 0 (1 : Matrix (Fin n) (Fin n) ℝ)) < ⊤ :=
  lt_of_le_of_lt (measure_mono unitEllipsoid_subset_closedBall) measure_closedBall_lt_top

/-- **Volume lemma of the ellipsoid method.** For `n ≥ 2`, positive definite `A` and `c ≠ 0`, `vol
E(a', A') < exp(-1 / (2 (n + 1))) · vol E(a, A)` (Goemans, *Lecture notes on the ellipsoid
algorithm*, MIT 18.433, 2009, Lemma 7.1). -/
theorem volume_nextEllipsoid_lt (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (a : Fin n → ℝ) {c : Fin n → ℝ} (hc : c ≠ 0) :
    volume (ellipsoid (nextCenter a A c) (nextMatrix A c)) <
      ENNReal.ofReal (Real.exp (-1 / (2 * ((n : ℝ) + 1)))) * volume (ellipsoid a A) := by
  rw [volume_nextEllipsoid hn hA a hc]
  have hpos : volume (ellipsoid a A) ≠ 0 := by
    rw [volume_ellipsoid hA]
    exact mul_ne_zero (by simpa using hA.det_pos) volume_unitEllipsoid_pos.ne'
  have hfin : volume (ellipsoid a A) ≠ ⊤ := by
    rw [volume_ellipsoid hA]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top volume_unitEllipsoid_lt_top.ne
  exact ENNReal.mul_lt_mul_left hpos hfin
    ((ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mpr (volumeRatio_lt_exp hn))

end MathlibExt.Analysis.Convex.EllipsoidMethod
