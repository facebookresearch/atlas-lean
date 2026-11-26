/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.Order.Star.Real

/-!
# The ellipsoid method: the central-cut step and its volume reduction

For a positive definite `A` and a centre `a`, the ellipsoid `E(a, A)` is
`{x : (x - a)ᵀ A⁻¹ (x - a) ≤ 1}`. Given a nonzero `c`, the central-cut step replaces `E(a, A)` by
`E(a', A')` with

* `b = A c / √(cᵀ A c)`,
* `a' = a - b / (n + 1)`,
* `A' = n² / (n² - 1) · (A - 2 / (n + 1) · b bᵀ)`,

which contains the half-ellipsoid `E(a, A) ∩ {x : cᵀ x ≤ cᵀ a}`. Since volumes of ellipsoids scale
like `√(det A)`, the step shrinks the volume by the factor
`(n / (n + 1)) · (n² / (n² - 1))^((n - 1) / 2) < exp(-1 / (2 (n + 1)))`.

We prove the containment of the half-ellipsoid (through the Sherman-Morrison formula for `A'⁻¹`)
and the algebraic facts behind the volume lemma: the determinant of the updated matrix (by the
matrix determinant lemma, using `bᵀ A⁻¹ b = 1`), the identity between the square root of the
determinant ratio and the volume factor, and the strict bound by `exp(-1 / (2 (n + 1)))` (from
`1 + x < eˣ` for `x ≠ 0`). The volume formula `vol E(a, A) = √(det A) · vol E(0, I)` and the
volume lemma itself are proved in `MathlibExt.Analysis.Convex.EllipsoidVolume`
(`volume_ellipsoid`, `volume_nextEllipsoid_lt`), and the convergence of the method in
`MathlibExt.Analysis.Convex.EllipsoidConvergence`.

Source: M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial
Optimization, Handout 19 (4 May 2009), Definition 7.1, equations (3)-(5), Lemma 7.1 and its proof.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.EllipsoidMethod

open Matrix

/-- **Volume factor of a central-cut ellipsoid step.** In dimension `n`, one step of the
ellipsoid method multiplies the volume by
`(n / (n + 1)) · (n² / (n² - 1))^((n - 1) / 2)` (Goemans, *Lecture notes on the ellipsoid
algorithm*, MIT 18.433, 2009, proof of Lemma 7.1). -/
noncomputable def volumeRatio (n : ℕ) : ℝ :=
  ((n : ℝ) / ((n : ℝ) + 1)) * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ (((n : ℝ) - 1) / 2)

/-- **The volume factor is positive.** For `n ≥ 2`, `0 < volumeRatio n`. -/
theorem volumeRatio_pos {n : ℕ} (hn : 2 ≤ n) : 0 < volumeRatio n := by
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold volumeRatio
  have h1 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  positivity

private theorem ratio_lt_exp_aux (x : ℝ) (hx : 2 ≤ x) :
    x / (x + 1) * (x ^ 2 / (x ^ 2 - 1)) ^ ((x - 1) / 2) < Real.exp (-1 / (2 * (x + 1))) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hx2 : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have h1 : x / (x + 1) < Real.exp (-1 / (x + 1)) := by
    have := Real.add_one_lt_exp (x := -1 / (x + 1)) (by
      have : (0 : ℝ) < 1 / (x + 1) := by positivity
      intro h; rw [neg_div] at h; linarith)
    have e : -1 / (x + 1) + 1 = x / (x + 1) := by field_simp; ring
    rwa [e] at this
  have h2 : x ^ 2 / (x ^ 2 - 1) < Real.exp (1 / (x ^ 2 - 1)) := by
    have := Real.add_one_lt_exp (x := 1 / (x ^ 2 - 1)) (by positivity)
    have e : 1 / (x ^ 2 - 1) + 1 = x ^ 2 / (x ^ 2 - 1) := by field_simp; ring
    rwa [e] at this
  have hz : (0 : ℝ) < (x - 1) / 2 := by linarith
  have h3 : (x ^ 2 / (x ^ 2 - 1)) ^ ((x - 1) / 2) < Real.exp (1 / (2 * (x + 1))) := by
    have := Real.rpow_lt_rpow (by positivity) h2 hz
    rw [← Real.exp_mul] at this
    have e : 1 / (x ^ 2 - 1) * ((x - 1) / 2) = 1 / (2 * (x + 1)) := by
      have : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
      rw [this]
      have : (0 : ℝ) < x - 1 := by linarith
      field_simp
    rwa [e] at this
  have hprod : x / (x + 1) * (x ^ 2 / (x ^ 2 - 1)) ^ ((x - 1) / 2) <
      Real.exp (-1 / (x + 1)) * Real.exp (1 / (2 * (x + 1))) :=
    mul_lt_mul'' h1 h3 (by positivity) (by positivity)
  rw [← Real.exp_add] at hprod
  have e : -1 / (x + 1) + 1 / (2 * (x + 1)) = -1 / (2 * (x + 1)) := by
    field_simp; ring
  rw [e] at hprod
  exact hprod

/-- **Volume reduction of the ellipsoid method.** For `n ≥ 2`,
`(n / (n + 1)) · (n² / (n² - 1))^((n - 1) / 2) < exp(-1 / (2 (n + 1)))`
(Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433, 2009, Lemma 7.1). The proof
applies `1 + x < eˣ` (for `x ≠ 0`) to `x = -1 / (n + 1)` and to `x = 1 / (n² - 1)`. -/
theorem volumeRatio_lt_exp {n : ℕ} (hn : 2 ≤ n) :
    volumeRatio n < Real.exp (-1 / (2 * ((n : ℝ) + 1))) :=
  ratio_lt_exp_aux (n : ℝ) (by exact_mod_cast hn)

/-- **Volume after `k` central-cut steps.** For `n ≥ 2` and `k ≥ 1`,
`volumeRatio n ^ k < exp(-k / (2 (n + 1)))`; so after `k` steps the volume is below
`vol(E₀) · exp(-k / (2 (n + 1)))` (Goemans, *Lecture notes on the ellipsoid algorithm*,
MIT 18.433, 2009, the remark after Claim 7.2). -/
theorem volumeRatio_pow_lt_exp {n k : ℕ} (hn : 2 ≤ n) (hk : k ≠ 0) :
    volumeRatio n ^ k < Real.exp (-(k : ℝ) / (2 * ((n : ℝ) + 1))) := by
  have h := pow_lt_pow_left₀ (volumeRatio_lt_exp hn) (volumeRatio_pos hn).le hk
  rw [← Real.exp_nat_mul] at h
  have e : (k : ℝ) * (-1 / (2 * ((n : ℝ) + 1))) = -(k : ℝ) / (2 * ((n : ℝ) + 1)) := by ring
  rwa [e] at h

variable {n : ℕ}

/-- **Ellipsoid with centre `a` and matrix `A`.** `E(a, A) = {x : (x - a)ᵀ A⁻¹ (x - a) ≤ 1}`,
meant for a positive definite `A` (Goemans, *Lecture notes on the ellipsoid algorithm*,
MIT 18.433, 2009, Definition 7.1). -/
noncomputable def ellipsoid (a : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | (x - a) ⬝ᵥ (A⁻¹ *ᵥ (x - a)) ≤ 1}

/-- **Direction of a central-cut step.** `b = A c / √(cᵀ A c)` (Goemans, *Lecture notes on the
ellipsoid algorithm*, MIT 18.433, 2009, the vector `b` after equation (3)). -/
noncomputable def cutDirection (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) : Fin n → ℝ :=
  (Real.sqrt (c ⬝ᵥ (A *ᵥ c)))⁻¹ • (A *ᵥ c)

/-- **Centre after a central-cut step.** `a' = a - b / (n + 1)` with `b = A c / √(cᵀ A c)`
(Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433, 2009, equation (5)). -/
noncomputable def nextCenter (a : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    Fin n → ℝ :=
  a - ((n : ℝ) + 1)⁻¹ • cutDirection A c

/-- **Matrix after a central-cut step.** `A' = n² / (n² - 1) · (A - 2 / (n + 1) · b bᵀ)` with
`b = A c / √(cᵀ A c)` (Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433, 2009,
equation (5)). -/
noncomputable def nextMatrix (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
    (A - (2 / ((n : ℝ) + 1)) • vecMulVec (cutDirection A c) (cutDirection A c))

/-- **The cut direction has unit `A⁻¹`-norm.** For positive definite `A` and `c ≠ 0`,
`bᵀ A⁻¹ b = 1` where `b = A c / √(cᵀ A c)`. -/
theorem cutDirection_inv_norm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {c : Fin n → ℝ}
    (hc : c ≠ 0) : cutDirection A c ⬝ᵥ (A⁻¹ *ᵥ cutDirection A c) = 1 := by
  have hpos : 0 < c ⬝ᵥ (A *ᵥ c) := by simpa using hA.dotProduct_mulVec_pos hc
  have hunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAc : A⁻¹ *ᵥ (A *ᵥ c) = c := by
    rw [mulVec_mulVec, nonsing_inv_mul A hunit, one_mulVec]
  unfold cutDirection
  rw [mulVec_smul, hAc, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have e : (A *ᵥ c) ⬝ᵥ c = c ⬝ᵥ (A *ᵥ c) := dotProduct_comm _ _
  rw [e]
  have hs := Real.sq_sqrt hpos.le
  have hs0 : Real.sqrt (c ⬝ᵥ (A *ᵥ c)) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  field_simp
  linarith [hs]

/-- **Determinant after a central-cut step.** For positive definite `A` and `c ≠ 0`,
`det A' = (n² / (n² - 1))ⁿ · (n - 1) / (n + 1) · det A`, by the matrix determinant lemma
`det (A - β b bᵀ) = det A · (1 - β bᵀ A⁻¹ b)` with `bᵀ A⁻¹ b = 1` and `β = 2 / (n + 1)`
(Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433, 2009, equation (5) and the proof
of Lemma 7.1). -/
theorem det_nextMatrix {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {c : Fin n → ℝ}
    (hc : c ≠ 0) :
    (nextMatrix A c).det =
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n * (((n : ℝ) - 1) / ((n : ℝ) + 1)) * A.det := by
  have hunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hb := cutDirection_inv_norm hA hc
  set b := cutDirection A c
  set β : ℝ := 2 / ((n : ℝ) + 1)
  have hrank : A - β • vecMulVec b b =
      A + replicateCol Unit (-β • b) * replicateRow Unit b := by
    rw [← vecMulVec_eq Unit]
    ext i j
    simp [vecMulVec, sub_eq_add_neg, mul_assoc]
  have hentry : (1 + replicateRow Unit b * A⁻¹ * replicateCol Unit (-β • b)).det = 1 - β := by
    rw [det_unique]
    have : (replicateRow Unit b * A⁻¹ * replicateCol Unit (-β • b)) default default =
        b ⬝ᵥ (A⁻¹ *ᵥ (-β • b)) := by
      simp only [neg_smul, PUnit.default_eq_unit, Matrix.mul_apply, replicateRow_apply,
        replicateCol_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, mul_neg, mul_left_comm,
        Finset.sum_mul, mul_assoc, Finset.mul_sum, Finset.sum_neg_distrib, dotProduct, mulVec,
        neg_mul, neg_inj]
      rw [Finset.sum_comm]
    rw [Matrix.add_apply, this, mulVec_smul, dotProduct_smul, hb]
    simp [sub_eq_add_neg]
  unfold nextMatrix
  rw [det_smul, Fintype.card_fin, hrank, det_add_replicateCol_mul_replicateRow hunit, hentry]
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have e : 1 - β = ((n : ℝ) - 1) / ((n : ℝ) + 1) := by
    simp only [β]
    field_simp
    ring
  rw [e]
  ring

/-- **Volume factor from the determinant ratio.** For `n ≥ 2`,
`√((n² / (n² - 1))ⁿ · (n - 1) / (n + 1)) = (n / (n + 1)) · (n² / (n² - 1))^((n - 1) / 2)`,
so the square root of `det A' / det A` given by `det_nextMatrix` is `volumeRatio n` (Goemans,
*Lecture notes on the ellipsoid algorithm*, MIT 18.433, 2009, proof of Lemma 7.1). -/
theorem sqrt_detRatio_eq_volumeRatio {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n * (((n : ℝ) - 1) / ((n : ℝ) + 1))) =
      volumeRatio n := by
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx2 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hr : (0 : ℝ) < (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) := by positivity
  have hsq : volumeRatio n ^ 2 =
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n * (((n : ℝ) - 1) / ((n : ℝ) + 1)) := by
    unfold volumeRatio
    rw [mul_pow, ← Real.rpow_natCast (_ ^ (((n : ℝ) - 1) / 2)) 2, ← Real.rpow_mul hr.le]
    have e1 : ((n : ℝ) - 1) / 2 * ((2 : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [e1, Real.rpow_natCast]
    have e2 : ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n =
        ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ (n - 1) * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [e2]
    have hfac : (n : ℝ) ^ 2 - 1 = ((n : ℝ) - 1) * ((n : ℝ) + 1) := by ring
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    rw [hfac]
    field_simp
  rw [← hsq, Real.sqrt_sq (volumeRatio_pos hn).le]

private theorem inv_symm_dot {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (u v : Fin n → ℝ) :
    u ⬝ᵥ (A⁻¹ *ᵥ v) = v ⬝ᵥ (A⁻¹ *ᵥ u) := by
  have hsym : Aᵀ = A := by
    have := hA.1.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_nonsing_inv, hsym, dotProduct_comm]

/-- **Inverse of the matrix after a central-cut step.** For `n ≥ 2`, positive definite `A` and
`c ≠ 0`, `A'⁻¹ = (n² - 1) / n² · (A⁻¹ + 2 / (n - 1) · c cᵀ / (cᵀ A c))`, by the Sherman-Morrison
formula with `b = A c / √(cᵀ A c)`. -/
theorem nextMatrix_inv {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {c : Fin n → ℝ}
    (hc : c ≠ 0) (hn : 2 ≤ n) :
    (nextMatrix A c)⁻¹ = ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1))⁻¹ •
      (A⁻¹ + ((2 / ((n : ℝ) - 1)) / (c ⬝ᵥ (A *ᵥ c))) • vecMulVec c c) := by
  have hpos : 0 < c ⬝ᵥ (A *ᵥ c) := by simpa using hA.dotProduct_mulVec_pos hc
  have hunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  set s := Real.sqrt (c ⬝ᵥ (A *ᵥ c)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hss : s ^ 2 = c ⬝ᵥ (A *ᵥ c) := Real.sq_sqrt hpos.le
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : cutDirection A c = s⁻¹ • (A *ᵥ c) := rfl
  have hAinvb : A⁻¹ *ᵥ cutDirection A c = s⁻¹ • c := by
    rw [hb, mulVec_smul, mulVec_mulVec, nonsing_inv_mul A hunit, one_mulVec]
  have hbc : cutDirection A c ⬝ᵥ c = s := by
    rw [hb, smul_dotProduct, smul_eq_mul, dotProduct_comm, ← hss]
    field_simp
  have hAc : A *ᵥ c = s • cutDirection A c := by
    rw [hb, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  set b := cutDirection A c
  set β : ℝ := 2 / ((n : ℝ) + 1)
  set κ : ℝ := (2 / ((n : ℝ) - 1)) / (c ⬝ᵥ (A *ᵥ c))
  set r : ℝ := (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)
  have hr : r ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have key : ∀ v : Fin n → ℝ,
      (A - β • vecMulVec b b) *ᵥ (A⁻¹ *ᵥ v + κ • (vecMulVec c c *ᵥ v)) = v := by
    intro v
    have hbv : b ⬝ᵥ (A⁻¹ *ᵥ v) = s⁻¹ * (c ⬝ᵥ v) := by
      rw [inv_symm_dot hA, hAinvb, dotProduct_smul, smul_eq_mul, dotProduct_comm]
    have e1 : A *ᵥ (A⁻¹ *ᵥ v + κ • (vecMulVec c c *ᵥ v)) = v + (κ * (c ⬝ᵥ v) * s) • b := by
      rw [mulVec_add, mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec, vecMulVec_mulVec,
        op_smul_eq_smul, mulVec_smul, mulVec_smul, hAc]
      module
    have e2 : vecMulVec b b *ᵥ (A⁻¹ *ᵥ v + κ • (vecMulVec c c *ᵥ v)) =
        (s⁻¹ * (c ⬝ᵥ v) + κ * (c ⬝ᵥ v) * s) • b := by
      rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_add, hbv, vecMulVec_mulVec,
        op_smul_eq_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hbc]
      congr 1
      ring
    have hscalar : κ * (c ⬝ᵥ v) * s - β * (s⁻¹ * (c ⬝ᵥ v) + κ * (c ⬝ᵥ v) * s) = 0 := by
      have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      simp only [κ, β, ← hss]
      field_simp
      ring
    rw [sub_mulVec, smul_mulVec, e1, e2,
      show v + (κ * (c ⬝ᵥ v) * s) • b - β • (s⁻¹ * (c ⬝ᵥ v) + κ * (c ⬝ᵥ v) * s) • b =
        v + (κ * (c ⬝ᵥ v) * s - β * (s⁻¹ * (c ⬝ᵥ v) + κ * (c ⬝ᵥ v) * s)) • b by module,
      hscalar, zero_smul, add_zero]
  apply inv_eq_right_inv
  apply ext_of_mulVec_single
  intro i
  rw [show nextMatrix A c = r • (A - β • vecMulVec b b) from rfl, one_mulVec, ← mulVec_mulVec]
  simp only [smul_mulVec, mulVec_smul, add_mulVec]
  rw [key, smul_smul, inv_mul_cancel₀ hr, one_smul]

/-- **The central-cut ellipsoid contains the half-ellipsoid.** For `n ≥ 2`, positive definite `A`
and `c ≠ 0`, the ellipsoid `E(a', A')` produced by the central-cut step contains
`E(a, A) ∩ {x : cᵀ x ≤ cᵀ a}` (Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433,
2009, equations (4)-(5)). With `y = x - a`, `q = yᵀ A⁻¹ y ≤ 1` and `t = cᵀ y / √(cᵀ A c) ∈ [-1, 0]`,
the quadratic form of `E(a', A')` at `x` equals `(q + 2 t (t + 1) / (n - 1) + 1 / (n² - 1)) / r`
with `r = n² / (n² - 1)`, which is at most `1`. -/
theorem halfEllipsoid_subset_nextEllipsoid (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (a : Fin n → ℝ) {c : Fin n → ℝ} (hc : c ≠ 0) :
    ellipsoid a A ∩ {x | c ⬝ᵥ x ≤ c ⬝ᵥ a} ⊆ ellipsoid (nextCenter a A c) (nextMatrix A c) := by
  rintro x ⟨hx, hcx⟩
  simp only [ellipsoid, Set.mem_ofPred_eq] at hx hcx ⊢
  rw [nextMatrix_inv hA hc hn]
  have hpos : 0 < c ⬝ᵥ (A *ᵥ c) := by simpa using hA.dotProduct_mulVec_pos hc
  have hunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  set s := Real.sqrt (c ⬝ᵥ (A *ᵥ c)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hss : s ^ 2 = c ⬝ᵥ (A *ᵥ c) := Real.sq_sqrt hpos.le
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hbb := cutDirection_inv_norm hA hc
  have hb : cutDirection A c = s⁻¹ • (A *ᵥ c) := rfl
  have hAinvb : A⁻¹ *ᵥ cutDirection A c = s⁻¹ • c := by
    rw [hb, mulVec_smul, mulVec_mulVec, nonsing_inv_mul A hunit, one_mulVec]
  have hcb : c ⬝ᵥ cutDirection A c = s := by
    rw [hb, dotProduct_smul, smul_eq_mul, ← hss]
    field_simp
  have hxa : x - nextCenter a A c = (x - a) + ((n : ℝ) + 1)⁻¹ • cutDirection A c := by
    unfold nextCenter
    abel
  rw [hxa]
  set b := cutDirection A c
  set y := x - a
  set k : ℝ := ((n : ℝ) + 1)⁻¹
  set γ : ℝ := 2 / ((n : ℝ) - 1)
  set r : ℝ := (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)
  set q := y ⬝ᵥ (A⁻¹ *ᵥ y)
  set t := s⁻¹ * (c ⬝ᵥ y)
  have hyb : y ⬝ᵥ (A⁻¹ *ᵥ b) = t := by
    rw [hAinvb, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  have hby : b ⬝ᵥ (A⁻¹ *ᵥ y) = t := by rw [inv_symm_dot hA, hyb]
  have hcy : c ⬝ᵥ y = s * t := by
    simp only [t]; field_simp
  have hval : (y + k • b) ⬝ᵥ ((r⁻¹ • (A⁻¹ + (γ / (c ⬝ᵥ (A *ᵥ c))) • vecMulVec c c)) *ᵥ
      (y + k • b)) = r⁻¹ * (q + 2 * k * t + k ^ 2 + γ * (t + k) ^ 2) := by
    simp only [smul_mulVec, add_mulVec, vecMulVec_mulVec, op_smul_eq_smul, mulVec_add,
      mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      hyb, hby, hbb, hcy, hcb]
    rw [dotProduct_comm b c, hcb, dotProduct_comm y c, hcy, ← hss]
    field_simp
    ring
  rw [hval]
  -- Cauchy-Schwarz in the A⁻¹ inner product
  have hCS : t ^ 2 ≤ q := by
    have h0 := (hA.inv).posSemidef.dotProduct_mulVec_nonneg (y - t • b)
    simp only [star_trivial, mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hyb, hby, hbb] at h0
    nlinarith
  have ht0 : t ≤ 0 := by
    have : c ⬝ᵥ y ≤ 0 := by simp only [y, dotProduct_sub]; linarith
    simp only [t]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hs0.le) this
  have ht1 : -1 ≤ t := by nlinarith
  have hN1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hN2 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hrpos : 0 < r := by positivity
  have expand : q + 2 * k * t + k ^ 2 + γ * (t + k) ^ 2 =
      q + γ * (t * (t + 1)) + 1 / ((n : ℝ) ^ 2 - 1) := by
    simp only [k, γ]
    field_simp
    ring
  have hr1 : r = 1 + 1 / ((n : ℝ) ^ 2 - 1) := by
    simp only [r]; field_simp; ring
  have hγ : 0 ≤ γ := by positivity
  have htt : t * (t + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht0 (by linarith)
  rw [inv_mul_le_iff₀ hrpos, expand, mul_one, hr1]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hγ htt]

end MathlibExt.Analysis.Convex.EllipsoidMethod
