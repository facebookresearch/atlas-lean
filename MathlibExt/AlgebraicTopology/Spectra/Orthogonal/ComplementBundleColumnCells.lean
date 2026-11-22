/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ComplementBundleGeometry

/-!
# Complete last-column complement-bundle cells

The complete inherited functions and topology are retained.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Filter
open TopologicalSpace Topology
open Matrix
open scoped InnerProductSpace
open CategoryTheory.Spectra

namespace CategoryTheory.Spectra.OrthogonalComplementBundle

/-- The inherited closed Euclidean disk used for the last-column attachment. -/
abbrev ClosedDisk (k : ℕ) := {x : Euclidean k // ‖x‖ ≤ 1}

/-- The actual unit sphere of possible last columns. -/
abbrev ColumnSphere (k : ℕ) := {x : Euclidean (k + 1) // ‖x‖ = 1}

/-- The first coordinates embed with a zero final coordinate. -/
def includeVector {k : ℕ} : Euclidean k →ₗ[ℝ] Euclidean (k + 1) where
  toFun x := WithLp.toLp 2 (Fin.lastCases 0 x.ofLp)
  map_add' x y := by
    apply WithLp.ofLp_injective
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  map_smul' t x := by
    apply WithLp.ofLp_injective
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp

/-- Dropping the final coordinate is the original finite coordinate projection. -/
def dropVector {k : ℕ} : Euclidean (k + 1) →ₗ[ℝ] Euclidean k where
  toFun x := WithLp.toLp 2 (fun j => x.ofLp j.castSucc)
  map_add' x y := by
    apply WithLp.ofLp_injective
    rfl
  map_smul' t x := by
    apply WithLp.ofLp_injective
    rfl

/-- The fixed last coordinate is the actual Euclidean basis vector. -/
def spherePole (k : ℕ) : Euclidean (k + 1) :=
  EuclideanSpace.basisFun (Fin (k + 1)) ℝ (Fin.last k)

@[simp]
theorem includeVector_castSucc {k : ℕ} (x : Euclidean k) (j : Fin k) :
    (includeVector x).ofLp j.castSucc = x.ofLp j := by
  simp [includeVector]

@[simp]
theorem includeVector_last {k : ℕ} (x : Euclidean k) :
    (includeVector x).ofLp (Fin.last k) = 0 := by
  simp [includeVector]

@[simp]
theorem dropVector_apply {k : ℕ} (x : Euclidean (k + 1)) (j : Fin k) :
    (dropVector x).ofLp j = x.ofLp j.castSucc := rfl

@[simp]
theorem spherePole_castSucc (k : ℕ) (j : Fin k) :
    (spherePole k).ofLp j.castSucc = 0 := by
  simp [spherePole, EuclideanSpace.basisFun_apply]

@[simp]
theorem spherePole_last (k : ℕ) :
    (spherePole k).ofLp (Fin.last k) = 1 := by
  simp [spherePole, EuclideanSpace.basisFun_apply]

/-- The coordinate inclusion preserves the full Euclidean norm. -/
theorem includeVector_norm {k : ℕ} (x : Euclidean k) :
    ‖includeVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_castSucc]
  simp

/-- The fixed last-coordinate vector has unit norm. -/
theorem spherePole_norm (k : ℕ) : ‖spherePole k‖ = 1 :=
  (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).orthonormal.norm_eq_one _

/-- The coordinate inclusion and projection reconstruct every first coordinate. -/
@[simp]
theorem dropVector_includeVector {k : ℕ} (x : Euclidean k) :
    dropVector (includeVector x) = x := by
  apply WithLp.ofLp_injective
  funext j
  simp

/-- The actual last coordinate is the inner product with the fixed pole. -/
theorem spherePole_inner {k : ℕ} (x : Euclidean (k + 1)) :
    ⟪spherePole k, x⟫_ℝ = x.ofLp (Fin.last k) :=
  EuclideanSpace.basisFun_inner (𝕜 := ℝ) (ι := Fin (k + 1)) x (Fin.last k)

/-- The first-coordinate subspace is perpendicular to the actual last pole. -/
theorem includeVector_inner_pole {k : ℕ} (x : Euclidean k) :
    ⟪includeVector x, spherePole k⟫_ℝ = 0 := by
  rw [real_inner_comm, spherePole_inner, includeVector_last]

/-- The first coordinates and the final coordinate reconstruct the entire vector. -/
theorem include_drop_add_pole {k : ℕ} (x : Euclidean (k + 1)) :
    includeVector (dropVector x) + x.ofLp (Fin.last k) • spherePole k = x := by
  apply WithLp.ofLp_injective
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- The first/final coordinate decomposition has its exact squared-norm identity. -/
theorem dropVector_norm_sq {k : ℕ} (x : Euclidean (k + 1)) :
    ‖dropVector x‖ ^ 2 + x.ofLp (Fin.last k) ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_castSucc]
  rfl

/-- Squared norms add in the actual first-coordinate/final-pole decomposition. -/
theorem includeVector_add_pole_norm_sq {k : ℕ} (x : Euclidean k) (t : ℝ) :
    ‖includeVector x + t • spherePole k‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 := by
  have h := dropVector_norm_sq (includeVector x + t • spherePole k)
  have hd : dropVector (includeVector x + t • spherePole k) = x := by
    apply WithLp.ofLp_injective
    funext j
    simp
  rw [hd] at h
  simpa [WithLp.ofLp_add, WithLp.ofLp_smul] using h.symm

/-- The inherited closed Euclidean disk is compact. -/
instance closedDisk_compactSpace (k : ℕ) : CompactSpace (ClosedDisk k) := by
  have heq : {x : Euclidean k | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  have h : IsCompact {x : Euclidean k | ‖x‖ ≤ 1} := by
    rw [heq]
    exact isCompact_closedBall 0 1
  exact isCompact_iff_compactSpace.mp h

/-- The nonnegative last coordinate of the closed upper hemisphere. -/
def diskHeight {k : ℕ} (x : ClosedDisk k) : ℝ := Real.sqrt (1 - ‖x.val‖ ^ 2)

theorem diskHeight_nonneg {k : ℕ} (x : ClosedDisk k) : 0 ≤ diskHeight x :=
  Real.sqrt_nonneg _

/-- The genuine disk height satisfies the exact hemisphere equation. -/
theorem diskHeight_sq {k : ℕ} (x : ClosedDisk k) :
    diskHeight x ^ 2 = 1 - ‖x.val‖ ^ 2 := by
  apply Real.sq_sqrt
  have hn := norm_nonneg x.val
  have hx := x.property
  nlinarith

/-- Height is continuous on the entire closed disk, including the boundary. -/
theorem diskHeight_continuous (k : ℕ) :
    Continuous (fun x : ClosedDisk k => diskHeight x) :=
  Real.continuous_sqrt.comp
    (continuous_const.sub ((continuous_norm.comp continuous_subtype_val).pow 2))

/-- The full upper-hemisphere vector, in coefficient-first/final-pole coordinates. -/
def diskHemisphere {k : ℕ} (x : ClosedDisk k) : Euclidean (k + 1) :=
  includeVector x.val + diskHeight x • spherePole k

/-- The hemisphere vector has unit norm on the entire closed disk. -/
theorem diskHemisphere_norm {k : ℕ} (x : ClosedDisk k) :
    ‖diskHemisphere x‖ = 1 := by
  have h := includeVector_add_pole_norm_sq x.val (diskHeight x)
  rw [diskHeight_sq] at h
  change ‖diskHemisphere x‖ ^ 2 = _ at h
  nlinarith [norm_nonneg (diskHemisphere x)]

/-- No actual hemisphere vector is zero, even on the attachment boundary. -/
theorem diskHemisphere_ne_zero {k : ℕ} (x : ClosedDisk k) : diskHemisphere x ≠ 0 := by
  intro h
  have hn := diskHemisphere_norm x
  rw [h, norm_zero] at hn
  norm_num at hn

/-- The actual upper-hemisphere function is continuous on the full closed disk. -/
theorem diskHemisphere_continuous (k : ℕ) :
    Continuous (fun x : ClosedDisk k => diskHemisphere x) :=
  (includeVector.continuous_of_finiteDimensional.comp continuous_subtype_val).add
    ((diskHeight_continuous k).smul continuous_const)

/-- A genuine original orthogonal lift over the full characteristic disk. -/
def diskLiftFrame {k : ℕ} (x : ClosedDisk k) :
    CategoryTheory.Spectra.OrthogonalMatrixHom (k + 1) (k + 1) :=
  CategoryTheory.Spectra.OrthogonalMatrixHom.comp
    (reflectionFrame (spherePole k)) (reflectionFrame (diskHemisphere x))

/-- The full matrix of the disk lift retains the original late-first composition. -/
theorem diskLiftFrame_val {k : ℕ} (x : ClosedDisk k) :
    (diskLiftFrame x).val =
      reflectionMatrix (diskHemisphere x) * reflectionMatrix (spherePole k) := rfl

/-- Both reflections act on the actual entire Euclidean vector. -/
theorem diskLiftFrame_apply {k : ℕ} (x : ClosedDisk k) (v : Euclidean (k + 1)) :
    matrixLinear (diskLiftFrame x).val v =
      reflectedVector (diskHemisphere x) (reflectedVector (spherePole k) v) :=
  matrixLinear_mul _ _ _

/-- The disk lift is continuous on every boundary point as well as the interior. -/
theorem diskLiftFrame_continuous (k : ℕ) :
    Continuous (fun x : ClosedDisk k => (diskLiftFrame x).val) := by
  have hr : Continuous (fun x : ClosedDisk k => reflectionMatrix (diskHemisphere x)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (reflectionMatrix_continuousAt (diskHemisphere_ne_zero x)).comp
      (diskHemisphere_continuous k).continuousAt
  exact hr.matrix_mul continuous_const

/-- The actual spherical characteristic function is the last column of its orthogonal lift. -/
def diskColumn {k : ℕ} (x : ClosedDisk k) : Euclidean (k + 1) :=
  matrixLinear (diskLiftFrame x).val (spherePole k)

/-- Every characteristic last column has genuine unit norm. -/
theorem diskColumn_norm {k : ℕ} (x : ClosedDisk k) : ‖diskColumn x‖ = 1 := by
  rw [diskColumn, matrixLinear_norm _ (diskLiftFrame x).property.1, spherePole_norm]

/-- The characteristic last column has its full explicit vector formula. -/
theorem diskColumn_formula {k : ℕ} (x : ClosedDisk k) :
    diskColumn x = (2 * diskHeight x) • diskHemisphere x - spherePole k := by
  rw [diskColumn, diskLiftFrame_apply, reflectedVector_self, reflectedVector_apply,
    diskHemisphere_norm]
  have hi : ⟪diskHemisphere x, spherePole k⟫_ℝ = diskHeight x := by
    rw [diskHemisphere, inner_add_left, includeVector_inner_pole, real_inner_smul_left,
      real_inner_self_eq_norm_sq, spherePole_norm]
    ring
  rw [inner_neg_right, hi]
  norm_num
  abel

/-- The complete characteristic column function is continuous by its actual vector formula. -/
theorem diskColumn_continuous (k : ℕ) :
    Continuous (fun x : ClosedDisk k => diskColumn x) := by
  have hf : Continuous (fun x : ClosedDisk k =>
      (2 * diskHeight x) • diskHemisphere x - spherePole k) :=
    ((continuous_const.mul (diskHeight_continuous k)).smul
      (diskHemisphere_continuous k)).sub continuous_const
  have heq : (fun x : ClosedDisk k => diskColumn x) =
      (fun x : ClosedDisk k => (2 * diskHeight x) • diskHemisphere x - spherePole k) :=
    funext diskColumn_formula
  rw [heq]
  exact hf

/-- The first coordinates of the spherical characteristic function. -/
theorem diskColumn_drop {k : ℕ} (x : ClosedDisk k) :
    dropVector (diskColumn x) = (2 * diskHeight x) • x.val := by
  rw [diskColumn_formula]
  apply WithLp.ofLp_injective
  funext j
  simp [diskHemisphere]

/-- The final coordinate of the spherical characteristic function. -/
theorem diskColumn_last {k : ℕ} (x : ClosedDisk k) :
    (diskColumn x).ofLp (Fin.last k) = 1 - 2 * ‖x.val‖ ^ 2 := by
  rw [diskColumn_formula]
  simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, WithLp.ofLp_add,
    diskHemisphere, includeVector_last, spherePole_last, zero_add, Pi.smul_apply,
    Pi.sub_apply, Pi.add_apply, smul_eq_mul, mul_one]
  nlinarith [diskHeight_sq x]

/-- The whole disk boundary maps to the distinguished negative pole. -/
theorem diskColumn_boundary {k : ℕ} (x : ClosedDisk k) (hx : ‖x.val‖ = 1) :
    diskColumn x = -spherePole k := by
  have hh : diskHeight x = 0 := by
    rw [diskHeight, hx]
    norm_num
  rw [diskColumn_formula, hh]
  simp

/-- A positive disk height is equivalent to being in the actual open disk. -/
theorem diskHeight_pos_iff {k : ℕ} (x : ClosedDisk k) :
    0 < diskHeight x ↔ ‖x.val‖ < 1 := by
  rw [diskHeight, Real.sqrt_pos]
  have hn := norm_nonneg x.val
  constructor <;> intro h <;> nlinarith [x.property]

/-- Exactly the disk boundary maps to the negative pole. -/
theorem diskColumn_eq_neg_pole_iff {k : ℕ} (x : ClosedDisk k) :
    diskColumn x = -spherePole k ↔ ‖x.val‖ = 1 := by
  constructor
  · intro h
    have hl := congrArg (fun v : Euclidean (k + 1) => v.ofLp (Fin.last k)) h
    rw [diskColumn_last] at hl
    simp only [WithLp.ofLp_neg, Pi.neg_apply, spherePole_last] at hl
    nlinarith [norm_nonneg x.val]
  · exact diskColumn_boundary x

/-- The characteristic disk is injective away from the attachment boundary. -/
theorem diskColumn_injective_of_interior {k : ℕ} (x y : ClosedDisk k)
    (hx : ‖x.val‖ < 1) (h : diskColumn x = diskColumn y) : x = y := by
  have hl := congrArg (fun v : Euclidean (k + 1) => v.ofLp (Fin.last k)) h
  rw [diskColumn_last, diskColumn_last] at hl
  have hs : diskHeight x ^ 2 = diskHeight y ^ 2 := by
    rw [diskHeight_sq, diskHeight_sq]
    nlinarith
  have hh : diskHeight x = diskHeight y :=
    (sq_eq_sq₀ (diskHeight_nonneg x) (diskHeight_nonneg y)).mp hs
  have hv := congrArg (fun v : Euclidean (k + 1) => dropVector v) h
  rw [diskColumn_drop, diskColumn_drop, ← hh] at hv
  apply Subtype.ext
  exact smul_right_injective (Euclidean k)
    (by nlinarith [(diskHeight_pos_iff x).mpr hx]) hv

/-- The complete spherical characteristic kernel consists of equal points or boundary points. -/
theorem diskColumn_eq_iff {k : ℕ} (x y : ClosedDisk k) :
    diskColumn x = diskColumn y ↔ x = y ∨ (‖x.val‖ = 1 ∧ ‖y.val‖ = 1) := by
  constructor
  · intro h
    by_cases hx : ‖x.val‖ = 1
    · right
      refine ⟨hx, ?_⟩
      apply (diskColumn_eq_neg_pole_iff y).mp
      rw [← h, diskColumn_boundary x hx]
    · left
      exact diskColumn_injective_of_interior x y
        (lt_of_le_of_ne x.property hx) h
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · rw [diskColumn_boundary x hx, diskColumn_boundary y hy]

/-- Every last coordinate of an actual unit column lies in the real unit interval. -/
theorem columnSphere_last_bounds {k : ℕ} (v : ColumnSphere k) :
    -1 ≤ v.val.ofLp (Fin.last k) ∧ v.val.ofLp (Fin.last k) ≤ 1 := by
  have h := dropVector_norm_sq v.val
  rw [v.property] at h
  have hs : v.val.ofLp (Fin.last k) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ‖dropVector v.val‖]
  exact abs_le.mp ((sq_le_one_iff_abs_le_one _).mp hs)

/-- Away from the negative pole, the actual last coordinate is strictly larger than minus one. -/
theorem columnSphere_last_gt_neg_one {k : ℕ} (v : ColumnSphere k)
    (hv : v.val ≠ -spherePole k) : -1 < v.val.ofLp (Fin.last k) := by
  by_contra h
  have ht : v.val.ofLp (Fin.last k) = -1 :=
    le_antisymm (le_of_not_gt h) (columnSphere_last_bounds v).1
  have hn := dropVector_norm_sq v.val
  rw [v.property, ht] at hn
  have hnorm : ‖dropVector v.val‖ = 0 := by
    nlinarith [norm_nonneg (dropVector v.val)]
  have hz : dropVector v.val = 0 := norm_eq_zero.mp hnorm
  have hr := include_drop_add_pole v.val
  rw [hz, map_zero, zero_add, ht] at hr
  exact hv (by simpa using hr.symm)

/-- The positive denominator of the explicit inverse characteristic coordinates. -/
def columnDenominator {k : ℕ} (v : ColumnSphere k) : ℝ :=
  Real.sqrt (2 * (1 + v.val.ofLp (Fin.last k)))

/-- The explicit inverse denominator has its exact square on the actual sphere. -/
theorem columnDenominator_sq {k : ℕ} (v : ColumnSphere k) :
    columnDenominator v ^ 2 = 2 * (1 + v.val.ofLp (Fin.last k)) := by
  apply Real.sq_sqrt
  nlinarith [(columnSphere_last_bounds v).1]

/-- The inverse denominator is positive precisely on the required off-pole domain. -/
theorem columnDenominator_pos {k : ℕ} (v : ColumnSphere k)
    (hv : v.val ≠ -spherePole k) : 0 < columnDenominator v := by
  apply Real.sqrt_pos.mpr
  nlinarith [columnSphere_last_gt_neg_one v hv]

/-- The full inverse characteristic vector in the original first coordinates. -/
def columnInverseVector {k : ℕ} (v : ColumnSphere k) : Euclidean k :=
  (columnDenominator v)⁻¹ • dropVector v.val

/-- The inverse vector has its exact actual Euclidean norm, rather than a carrier bijection. -/
theorem columnInverseVector_norm_sq {k : ℕ} (v : ColumnSphere k)
    (hv : v.val ≠ -spherePole k) :
    ‖columnInverseVector v‖ ^ 2 = (1 - v.val.ofLp (Fin.last k)) / 2 := by
  have hd : columnDenominator v ≠ 0 := ne_of_gt (columnDenominator_pos v hv)
  have hn := dropVector_norm_sq v.val
  rw [v.property] at hn
  calc
    ‖columnInverseVector v‖ ^ 2 =
        ‖dropVector v.val‖ ^ 2 / columnDenominator v ^ 2 := by
      rw [columnInverseVector, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (columnDenominator_pos v hv)), mul_pow, inv_pow]
      ring
    _ = (1 - v.val.ofLp (Fin.last k)) / 2 := by
      apply (div_eq_iff (pow_ne_zero 2 hd)).mpr
      rw [columnDenominator_sq]
      nlinarith

/-- Every off-pole unit column has an inverse in the actual open Euclidean disk. -/
theorem columnInverseVector_norm_lt_one {k : ℕ} (v : ColumnSphere k)
    (hv : v.val ≠ -spherePole k) : ‖columnInverseVector v‖ < 1 := by
  have hn := columnInverseVector_norm_sq v hv
  nlinarith [norm_nonneg (columnInverseVector v), columnSphere_last_gt_neg_one v hv]

/-- The actual disk point corresponding to a unit column away from the negative pole. -/
def columnInverseDisk {k : ℕ} (v : ColumnSphere k) (hv : v.val ≠ -spherePole k) :
    ClosedDisk k := ⟨columnInverseVector v, (columnInverseVector_norm_lt_one v hv).le⟩

/-- The inverse disk point recovers the positive height used by the forward lift. -/
theorem columnInverseDisk_height {k : ℕ} (v : ColumnSphere k)
    (hv : v.val ≠ -spherePole k) :
    2 * diskHeight (columnInverseDisk v hv) = columnDenominator v := by
  have hp : 0 ≤ columnDenominator v := (columnDenominator_pos v hv).le
  apply (sq_eq_sq₀ (mul_nonneg (by norm_num) (diskHeight_nonneg _))
    hp).mp
  have hh := diskHeight_sq (columnInverseDisk v hv)
  have hn := columnInverseVector_norm_sq v hv
  have hd := columnDenominator_sq v
  change diskHeight (columnInverseDisk v hv) ^ 2 = 1 - ‖columnInverseVector v‖ ^ 2 at hh
  nlinarith

/-- The forward characteristic map reconstructs every actual off-pole unit column. -/
theorem diskColumn_columnInverseDisk {k : ℕ} (v : ColumnSphere k)
    (hv : v.val ≠ -spherePole k) : diskColumn (columnInverseDisk v hv) = v.val := by
  have hd : dropVector (diskColumn (columnInverseDisk v hv)) = dropVector v.val := by
    rw [diskColumn_drop]
    change (2 * diskHeight (columnInverseDisk v hv)) •
      ((columnDenominator v)⁻¹ • dropVector v.val) = _
    rw [columnInverseDisk_height, smul_smul,
      mul_inv_cancel₀ (ne_of_gt (columnDenominator_pos v hv)), one_smul]
  have hl : (diskColumn (columnInverseDisk v hv)).ofLp (Fin.last k) =
      v.val.ofLp (Fin.last k) := by
    rw [diskColumn_last]
    change 1 - 2 * ‖columnInverseVector v‖ ^ 2 = _
    rw [columnInverseVector_norm_sq v hv]
    ring
  calc
    diskColumn (columnInverseDisk v hv) =
        includeVector (dropVector (diskColumn (columnInverseDisk v hv))) +
          (diskColumn (columnInverseDisk v hv)).ofLp (Fin.last k) • spherePole k :=
      (include_drop_add_pole _).symm
    _ = includeVector (dropVector v.val) + v.val.ofLp (Fin.last k) • spherePole k := by
      rw [hd, hl]
    _ = v.val := include_drop_add_pole _

/-- All unit columns other than the negative pole are covered by the genuine open disk. -/
theorem diskColumn_surjective_off_pole {k : ℕ} (v : ColumnSphere k)
    (hv : v.val ≠ -spherePole k) :
    ∃ x : ClosedDisk k, ‖x.val‖ < 1 ∧ diskColumn x = v.val :=
  ⟨columnInverseDisk v hv, columnInverseVector_norm_lt_one v hv,
    diskColumn_columnInverseDisk v hv⟩

/-- The actual open-disk source of the characteristic map. -/
abbrev DiskInterior (k : ℕ) := {x : ClosedDisk k // ‖x.val‖ < 1}

/-- The actual off-pole open part of the sphere of last columns. -/
abbrev ColumnInterior (k : ℕ) := {v : ColumnSphere k // v.val ≠ -spherePole k}

/-- The denominator varies continuously on the original unit sphere. -/
theorem columnDenominator_continuous (k : ℕ) :
    Continuous (fun v : ColumnSphere k => columnDenominator v) := by
  have hc : Continuous (fun v : ColumnSphere k => v.val.ofLp (Fin.last k)) :=
    (continuous_apply (Fin.last k)).comp
      ((EuclideanSpace.equiv (Fin (k + 1)) ℝ).continuous.comp continuous_subtype_val)
  exact Real.continuous_sqrt.comp (continuous_const.mul (continuous_const.add hc))

/-- The explicit inverse characteristic vector is continuous on its whole off-pole domain. -/
theorem columnInverseVector_continuous (k : ℕ) :
    Continuous (fun v : ColumnInterior k => columnInverseVector v.val) := by
  have hd : Continuous (fun v : ColumnInterior k => (columnDenominator v.val)⁻¹) :=
    ((columnDenominator_continuous k).comp continuous_subtype_val).inv₀
      (fun v => ne_of_gt (columnDenominator_pos v.val v.property))
  have hp : Continuous (fun v : ColumnInterior k => dropVector v.val.val) :=
    dropVector.continuous_of_finiteDimensional.comp
      (continuous_subtype_val.comp continuous_subtype_val)
  exact hd.smul hp

/-- The actual spherical characteristic disk has both continuous inverse functions
on its interior. -/
def diskColumnInteriorHomeomorph (k : ℕ) : DiskInterior k ≃ₜ ColumnInterior k where
  toFun x := ⟨⟨diskColumn x.val, diskColumn_norm x.val⟩, by
    intro h
    exact (ne_of_lt x.property) ((diskColumn_eq_neg_pole_iff x.val).mp h)⟩
  invFun v := ⟨columnInverseDisk v.val v.property,
    columnInverseVector_norm_lt_one v.val v.property⟩
  left_inv x := by
    apply Subtype.ext
    have hv : diskColumn x.val ≠ -spherePole k := by
      intro h
      exact (ne_of_lt x.property) ((diskColumn_eq_neg_pole_iff x.val).mp h)
    have hc : diskColumn (columnInverseDisk ⟨diskColumn x.val, diskColumn_norm x.val⟩ hv) =
        diskColumn x.val := diskColumn_columnInverseDisk _ hv
    exact (diskColumn_injective_of_interior x.val _ x.property
      hc.symm).symm
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    exact diskColumn_columnInverseDisk v.val v.property
  continuous_toFun :=
    (((diskColumn_continuous k).comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((columnInverseVector_continuous k).subtype_mk _).subtype_mk _

/-- The sphere is covered by the negative-pole fiber and the actual characteristic disk. -/
def poleDiskColumnMap (k : ℕ) : Unit ⊕ ClosedDisk k → ColumnSphere k :=
  Sum.elim (fun _ => ⟨-spherePole k, by simp [spherePole_norm]⟩)
    (fun x => ⟨diskColumn x, diskColumn_norm x⟩)

/-- The full pole-and-disk characteristic function is continuous in the inherited topology. -/
theorem poleDiskColumnMap_continuous (k : ℕ) : Continuous (poleDiskColumnMap k) :=
  continuous_const.sumElim ((diskColumn_continuous k).subtype_mk _)

/-- Every actual unit column is covered, also in the zero-dimensional disk case. -/
theorem poleDiskColumnMap_surjective (k : ℕ) : Function.Surjective (poleDiskColumnMap k) := by
  intro v
  by_cases hv : v.val = -spherePole k
  · refine ⟨Sum.inl (), ?_⟩
    exact Subtype.ext hv.symm
  · refine ⟨Sum.inr (columnInverseDisk v hv), ?_⟩
    exact Subtype.ext (diskColumn_columnInverseDisk v hv)

/-- The pole-and-disk characteristic map gives the actual sphere quotient topology. -/
theorem poleDiskColumnMap_quotient (k : ℕ) : IsQuotientMap (poleDiskColumnMap k) :=
  IsQuotientMap.of_surjective_continuous
    (poleDiskColumnMap_surjective k) (poleDiskColumnMap_continuous k)

/-- The actual coordinate inclusion preserves both Euclidean inner-product arguments. -/
theorem includeVector_inner {k : ℕ} (x y : Euclidean k) :
    ⟪includeVector x, includeVector y⟫_ℝ = ⟪x, y⟫_ℝ := by
  simp only [← euclidean_dot_inner, dotProduct, Fin.sum_univ_castSucc,
    includeVector_castSucc, includeVector_last, zero_mul, add_zero]

/-- Appending a pole column leaves the original ordered embedding columns first. -/
def insertColumn {n k : ℕ} (A : EmbeddingMatrix n k) (j : Fin (n + 1)) :
    Euclidean (k + 1) :=
  Fin.lastCases (spherePole k) (fun i => includeVector (embeddingColumn A i)) j

/-- The appended columns satisfy their actual one-sided orthonormal equations. -/
theorem insertColumn_orthonormal {n k : ℕ} (A : EmbeddingMatrix n k) :
    Orthonormal ℝ (insertColumn A) := by
  rw [orthonormal_iff_ite]
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [insertColumn, spherePole_norm]
    · simp [insertColumn, spherePole_inner, Ne.symm (Fin.castSucc_ne_last j)]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [insertColumn, includeVector_inner_pole]
    · simpa [insertColumn, includeVector_inner] using embeddingColumn_inner A i j

/-- The actual one-sided embedding obtained by appending the fixed pole column. -/
def insertEmbedding {n k : ℕ} (A : EmbeddingMatrix n k) :
    EmbeddingMatrix (n + 1) (k + 1) :=
  ⟨fun i j => (insertColumn A j).ofLp i, by
    ext i j
    change (insertColumn A i).ofLp ⬝ᵥ (insertColumn A j).ofLp =
      if i = j then 1 else 0
    rw [euclidean_dot_inner]
    exact (orthonormal_iff_ite.mp (insertColumn_orthonormal A)) i j⟩

/-- The inserted matrix has exactly the specified original finite columns. -/
theorem insertEmbedding_column {n k : ℕ} (A : EmbeddingMatrix n k)
    (j : Fin (n + 1)) : embeddingColumn (insertEmbedding A) j = insertColumn A j := by
  apply WithLp.ofLp_injective
  rfl

/-- The unchanged embedding entries occur in the original first coordinate blocks. -/
theorem insertEmbedding_castSucc {n k : ℕ} (A : EmbeddingMatrix n k)
    (i : Fin k) (j : Fin n) :
    (insertEmbedding A).val i.castSucc j.castSucc = A.val i j := by
  simp [insertEmbedding, insertColumn, embeddingColumn]

/-- Every actual complement vector is perpendicular to every original embedding column. -/
theorem embeddingColumn_inner_bundleVector {n k : ℕ} (p : ComplementBundle n k)
    (j : Fin n) : ⟪embeddingColumn (bundleBase p) j, bundleVector p⟫_ℝ = 0 := by
  rw [← euclidean_dot_inner]
  exact congrFun p.property.2 j

/-- Appending the fixed pole inserts the entire original complement-bundle point. -/
def insertBundle {n k : ℕ} (p : ComplementBundle n k) :
    ComplementBundle (n + 1) (k + 1) :=
  ⟨((insertEmbedding (bundleBase p)).val, includeVector (bundleVector p)),
    (insertEmbedding (bundleBase p)).property, by
      ext j
      change (insertColumn (bundleBase p) j).ofLp ⬝ᵥ
        (includeVector (bundleVector p)).ofLp = 0
      rw [euclidean_dot_inner]
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [insertColumn, spherePole_inner]
      · simpa [insertColumn, includeVector_inner] using
          embeddingColumn_inner_bundleVector p j⟩

/-- Insertion retains the specified original embedding matrix. -/
theorem insertBundle_base {n k : ℕ} (p : ComplementBundle n k) :
    bundleBase (insertBundle p) = insertEmbedding (bundleBase p) := rfl

/-- Insertion retains the full original vector with a zero last coordinate. -/
theorem insertBundle_vector {n k : ℕ} (p : ComplementBundle n k) :
    bundleVector (insertBundle p) = includeVector (bundleVector p) := rfl

/-- The appended final column is exactly the fixed positive pole. -/
theorem insertBundle_lastColumn {n k : ℕ} (p : ComplementBundle n k) :
    embeddingColumn (bundleBase (insertBundle p)) (Fin.last n) = spherePole k := by
  rw [insertBundle_base, insertEmbedding_column]
  simp [insertColumn]

/-- Every first embedding column retains its original order under insertion. -/
theorem insertBundle_castSuccColumn {n k : ℕ} (p : ComplementBundle n k) (j : Fin n) :
    embeddingColumn (bundleBase (insertBundle p)) j.castSucc =
      includeVector (embeddingColumn (bundleBase p) j) := by
  rw [insertBundle_base, insertEmbedding_column]
  simp [insertColumn]

/-- Inserting a pole preserves the actual Euclidean complement norm. -/
theorem insertBundle_norm {n k : ℕ} (p : ComplementBundle n k) :
    ‖bundleVector (insertBundle p)‖ = ‖bundleVector p‖ := by
  rw [insertBundle_vector, includeVector_norm]

/-- Pole insertion is injective on the full original matrix/vector carrier. -/
theorem insertBundle_injective (n k : ℕ) :
    Function.Injective (insertBundle : ComplementBundle n k → _) := by
  intro p q hpq
  apply complementBundle_ext
  · ext i j
    change (bundleBase p).val i j = (bundleBase q).val i j
    have h := congrArg (fun r : ComplementBundle (n + 1) (k + 1) =>
      (bundleBase r).val i.castSucc j.castSucc) hpq
    simpa only [insertBundle_base, insertEmbedding_castSucc] using h
  · change bundleVector p = bundleVector q
    have h := congrArg (fun r : ComplementBundle (n + 1) (k + 1) =>
      dropVector (bundleVector r)) hpq
    simpa only [insertBundle_vector, dropVector_includeVector] using h

/-- Every inserted finite embedding column depends continuously on the actual original base. -/
theorem insertColumn_continuous (n k : ℕ) (j : Fin (n + 1)) :
    Continuous (fun A : EmbeddingMatrix n k => insertColumn A j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [insertColumn, Fin.lastCases_last] using
      (continuous_const : Continuous (fun _ : EmbeddingMatrix n k => spherePole k))
  · simpa only [insertColumn, Fin.lastCases_castSucc, Function.comp_def] using
      (includeVector.continuous_of_finiteDimensional.comp (embeddingColumn_continuous i))

/-- The appended one-sided matrix varies continuously in its inherited finite topology. -/
theorem insertEmbedding_continuous (n k : ℕ) :
    Continuous (insertEmbedding : EmbeddingMatrix n k → _) := by
  have h : Continuous (fun A : EmbeddingMatrix n k =>
      fun i : Fin (k + 1) => fun j : Fin (n + 1) => (insertColumn A j).ofLp i) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply i).comp
      ((EuclideanSpace.equiv (Fin (k + 1)) ℝ).continuous.comp
        (insertColumn_continuous n k j))
  exact h.subtype_mk _

/-- The full complement-bundle insertion is continuous in the original inherited topology. -/
theorem insertBundle_continuous (n k : ℕ) :
    Continuous (insertBundle : ComplementBundle n k → _) :=
  (((continuous_subtype_val.comp (insertEmbedding_continuous n k)).comp
      continuous_bundleBase).prodMk
    (includeVector.continuous_of_finiteDimensional.comp continuous_bundleVector)).subtype_mk _

/-- Original target matrices act on every embedding column by their actual linear function. -/
theorem targetMap_embeddingColumn {n k l : ℕ}
    (t : CategoryTheory.Spectra.OrthogonalMatrixHom k l) (p : ComplementBundle n k)
    (j : Fin n) :
    embeddingColumn (bundleBase (targetMap t p)) j =
      matrixLinear t.val (embeddingColumn (bundleBase p) j) := by
  rw [embeddingColumn_eq_matrixLinear_basis, embeddingColumn_eq_matrixLinear_basis]
  change matrixLinear (t.val * p.val.1) _ = matrixLinear t.val (matrixLinear p.val.1 _)
  exact matrixLinear_mul _ _ _

/-- Original target matrices act on the complete complement vector by their
actual linear function. -/
theorem targetMap_bundleVector {n k l : ℕ}
    (t : CategoryTheory.Spectra.OrthogonalMatrixHom k l) (p : ComplementBundle n k) :
    bundleVector (targetMap t p) = matrixLinear t.val (bundleVector p) := rfl

/-- The complete smaller bundle inserted over the distinguished negative pole. -/
def poleBundle {n k : ℕ} (p : ComplementBundle n k) :
    ComplementBundle (n + 1) (k + 1) :=
  targetMap (reflectionFrame (spherePole k)) (insertBundle p)

/-- The negative-pole insertion has its exact actual final embedding column. -/
theorem poleBundle_lastColumn {n k : ℕ} (p : ComplementBundle n k) :
    embeddingColumn (bundleBase (poleBundle p)) (Fin.last n) = -spherePole k := by
  rw [poleBundle, targetMap_embeddingColumn, insertBundle_lastColumn]
  exact reflectedVector_self _

/-- The first columns of the negative-pole insertion retain their original ordered coordinates. -/
theorem poleBundle_castSuccColumn {n k : ℕ} (p : ComplementBundle n k) (j : Fin n) :
    embeddingColumn (bundleBase (poleBundle p)) j.castSucc =
      includeVector (embeddingColumn (bundleBase p) j) := by
  rw [poleBundle, targetMap_embeddingColumn, insertBundle_castSuccColumn]
  exact reflectedVector_perpendicular _ _ (by rw [spherePole_inner, includeVector_last])

/-- The negative-pole insertion keeps the full finite vector in the first coordinates. -/
theorem poleBundle_vector {n k : ℕ} (p : ComplementBundle n k) :
    bundleVector (poleBundle p) = includeVector (bundleVector p) := by
  rw [poleBundle, targetMap_bundleVector, insertBundle_vector]
  exact reflectedVector_perpendicular _ _ (by rw [spherePole_inner, includeVector_last])

/-- The negative-pole insertion preserves the actual complement norm. -/
theorem poleBundle_norm {n k : ℕ} (p : ComplementBundle n k) :
    ‖bundleVector (poleBundle p)‖ = ‖bundleVector p‖ := by
  rw [poleBundle_vector, includeVector_norm]

/-- The negative-pole insertion is continuous on the full smaller complement bundle. -/
theorem poleBundle_continuous (n k : ℕ) :
    Continuous (poleBundle : ComplementBundle n k → _) :=
  (targetMap_continuous (reflectionFrame (spherePole k))).comp (insertBundle_continuous n k)

/-- The actual disk family of full matrix/vector characteristic points. -/
def diskBundleAttachment (n k : ℕ) :
    ClosedDisk k × ComplementBundle n k → ComplementBundle (n + 1) (k + 1) :=
  fun p => targetMap (diskLiftFrame p.1) (insertBundle p.2)

/-- The final column of the full bundle attachment is its original spherical characteristic. -/
theorem diskBundleAttachment_lastColumn (n k : ℕ) (x : ClosedDisk k)
    (p : ComplementBundle n k) :
    embeddingColumn (bundleBase (diskBundleAttachment n k (x, p))) (Fin.last n) =
      diskColumn x := by
  rw [diskBundleAttachment, targetMap_embeddingColumn, insertBundle_lastColumn]
  rfl

/-- Every earlier column has the original orthogonal lift applied to its original coordinates. -/
theorem diskBundleAttachment_castSuccColumn (n k : ℕ) (x : ClosedDisk k)
    (p : ComplementBundle n k) (j : Fin n) :
    embeddingColumn (bundleBase (diskBundleAttachment n k (x, p))) j.castSucc =
      matrixLinear (diskLiftFrame x).val (includeVector (embeddingColumn (bundleBase p) j)) := by
  rw [diskBundleAttachment, targetMap_embeddingColumn, insertBundle_castSuccColumn]

/-- The actual vector characteristic is the full orthogonal lift of the original
complement vector. -/
theorem diskBundleAttachment_vector (n k : ℕ) (x : ClosedDisk k)
    (p : ComplementBundle n k) :
    bundleVector (diskBundleAttachment n k (x, p)) =
      matrixLinear (diskLiftFrame x).val (includeVector (bundleVector p)) := by
  rw [diskBundleAttachment, targetMap_bundleVector, insertBundle_vector]

/-- The full disk characteristic preserves every actual finite complement norm. -/
theorem diskBundleAttachment_norm (n k : ℕ) (x : ClosedDisk k)
    (p : ComplementBundle n k) :
    ‖bundleVector (diskBundleAttachment n k (x, p))‖ = ‖bundleVector p‖ := by
  rw [diskBundleAttachment, targetMap_norm, insertBundle_norm]

/-- The disk family varies continuously jointly in its disk coordinate and full bundle point. -/
theorem diskBundleAttachment_continuous (n k : ℕ) :
    Continuous (diskBundleAttachment n k) := by
  have hl : Continuous (fun x : ClosedDisk k => diskLiftFrame x) :=
    continuous_induced_rng.mpr (diskLiftFrame_continuous k)
  have hd : Continuous (fun p : ClosedDisk k × ComplementBundle n k =>
      (diskLiftFrame p.1, insertBundle p.2)) :=
    (hl.comp continuous_fst).prodMk
      ((insertBundle_continuous n k).comp continuous_snd)
  exact (targetMap_joint_continuous (n + 1) (k + 1) (k + 1)).comp hd

/-- Every actual column has exactly the corresponding original finite matrix entries. -/
theorem embeddingColumn_entry {n k : ℕ} (A : EmbeddingMatrix n k)
    (i : Fin k) (j : Fin n) : (embeddingColumn A j).ofLp i = A.val i j := rfl

/-- All original ordered columns and the actual vector determine a full bundle point. -/
theorem complementBundle_ext_columns {n k : ℕ} {p q : ComplementBundle n k}
    (hA : ∀ j, embeddingColumn (bundleBase p) j = embeddingColumn (bundleBase q) j)
    (hv : bundleVector p = bundleVector q) : p = q := by
  apply complementBundle_ext
  · ext i j
    have h := congrArg (fun x : Euclidean k => x.ofLp i) (hA j)
    simpa only [embeddingColumn_entry, bundleBase_val] using h
  · simpa only [bundleVector_val] using hv

/-- The actual closed subspace where the appended final column is the positive pole. -/
abbrev PositivePoleFiber (n k : ℕ) :=
  {p : ComplementBundle (n + 1) (k + 1) //
    embeddingColumn (bundleBase p) (Fin.last n) = spherePole k}

/-- Every earlier column has zero final coordinate on the actual positive-pole fiber. -/
theorem positivePoleFiber_lastRow {n k : ℕ} (p : PositivePoleFiber n k) (j : Fin n) :
    (bundleBase p.val).val (Fin.last k) j.castSucc = 0 := by
  have h := embeddingColumn_inner (bundleBase p.val) j.castSucc (Fin.last n)
  rw [p.property, real_inner_comm, spherePole_inner] at h
  simpa only [embeddingColumn_entry, ite_eq_right (Fin.castSucc_ne_last j)] using h

/-- The full complement vector has zero final coordinate on the positive-pole fiber. -/
theorem positivePoleFiber_lastVector {n k : ℕ} (p : PositivePoleFiber n k) :
    (bundleVector p.val).ofLp (Fin.last k) = 0 := by
  have h := embeddingColumn_inner_bundleVector p.val (Fin.last n)
  rw [p.property, spherePole_inner] at h
  exact h

/-- The earlier rows and columns recover the original smaller one-sided embedding. -/
def removePoleEmbedding {n k : ℕ} (p : PositivePoleFiber n k) : EmbeddingMatrix n k :=
  ⟨fun i j => (bundleBase p.val).val i.castSucc j.castSucc, by
    ext i j
    have h := congrFun (congrFun (bundleBase p.val).property i.castSucc) j.castSucc
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    rw [Fin.sum_univ_castSucc, positivePoleFiber_lastRow p i,
      zero_mul, add_zero] at h
    change (∑ l : Fin k, (bundleBase p.val).val l.castSucc i.castSucc *
      (bundleBase p.val).val l.castSucc j.castSucc) = if i = j then 1 else 0
    simpa only [Fin.castSucc_inj] using h⟩

/-- Dropping the pole row and column recovers the entire smaller complement-bundle point. -/
def removePoleBundle {n k : ℕ} (p : PositivePoleFiber n k) : ComplementBundle n k :=
  ⟨((removePoleEmbedding p).val, dropVector (bundleVector p.val)),
    (removePoleEmbedding p).property, by
      ext j
      have h := congrFun p.val.property.2 j.castSucc
      change (∑ i : Fin (k + 1), (bundleBase p.val).val i j.castSucc *
        (bundleVector p.val).ofLp i) = 0 at h
      rw [Fin.sum_univ_castSucc, positivePoleFiber_lastRow p j,
        zero_mul, add_zero] at h
      exact h⟩

/-- The recovered vector is exactly the actual first-coordinate projection. -/
theorem removePoleBundle_vector {n k : ℕ} (p : PositivePoleFiber n k) :
    bundleVector (removePoleBundle p) = dropVector (bundleVector p.val) := rfl

/-- Recovering the smaller bundle preserves the actual Euclidean complement norm. -/
theorem removePoleBundle_norm {n k : ℕ} (p : PositivePoleFiber n k) :
    ‖bundleVector (removePoleBundle p)‖ = ‖bundleVector p.val‖ := by
  rw [removePoleBundle_vector]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := dropVector_norm_sq (bundleVector p.val)
  rw [positivePoleFiber_lastVector p, zero_pow (by decide), add_zero] at h
  exact h

/-- The first-coordinate inclusion reconstructs the complete positive-pole vector. -/
theorem positivePoleFiber_include_drop_vector {n k : ℕ} (p : PositivePoleFiber n k) :
    includeVector (dropVector (bundleVector p.val)) = bundleVector p.val := by
  have h := include_drop_add_pole (bundleVector p.val)
  rw [positivePoleFiber_lastVector p, zero_smul, add_zero] at h
  exact h

/-- Removing an inserted pole recovers every original smaller bundle point. -/
theorem removePoleBundle_insertBundle {n k : ℕ} (p : ComplementBundle n k) :
    removePoleBundle ⟨insertBundle p, insertBundle_lastColumn p⟩ = p := by
  apply complementBundle_ext
  · ext i j
    change (insertEmbedding (bundleBase p)).val i.castSucc j.castSucc = p.val.1 i j
    exact insertEmbedding_castSucc _ _ _
  · change dropVector (bundleVector (insertBundle p)) = bundleVector p
    rw [insertBundle_vector, dropVector_includeVector]

/-- Inserting the recovered first coordinates reconstructs the entire positive-pole bundle point. -/
theorem insertBundle_removePoleBundle {n k : ℕ} (p : PositivePoleFiber n k) :
    insertBundle (removePoleBundle p) = p.val := by
  apply complementBundle_ext_columns
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [insertBundle_lastColumn, p.property]
    · rw [insertBundle_castSuccColumn]
      apply WithLp.ofLp_injective
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [includeVector_last, embeddingColumn_entry, positivePoleFiber_lastRow]
      · rw [includeVector_castSucc, embeddingColumn_entry, embeddingColumn_entry]
        rfl
  · rw [insertBundle_vector, removePoleBundle_vector,
      positivePoleFiber_include_drop_vector]

/-- The complete smaller-bundle recovery function is continuous on the positive-pole subspace. -/
theorem removePoleBundle_continuous (n k : ℕ) :
    Continuous (removePoleBundle : PositivePoleFiber n k → _) := by
  have hm : Continuous (fun p : PositivePoleFiber n k => p.val.val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hA : Continuous (fun p : PositivePoleFiber n k =>
      fun i : Fin k => fun j : Fin n => p.val.val.1 i.castSucc j.castSucc) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply j.castSucc).comp ((continuous_apply i.castSucc).comp hm)
  have hv : Continuous (fun p : PositivePoleFiber n k => dropVector (bundleVector p.val)) :=
    dropVector.continuous_of_finiteDimensional.comp
      (continuous_bundleVector.comp continuous_subtype_val)
  exact (hA.prodMk hv).subtype_mk _

/-- The actual positive-pole subspace is homeomorphic to the full original smaller bundle. -/
def positivePoleFiberHomeomorph (n k : ℕ) : ComplementBundle n k ≃ₜ PositivePoleFiber n k where
  toFun p := ⟨insertBundle p, insertBundle_lastColumn p⟩
  invFun := removePoleBundle
  left_inv := removePoleBundle_insertBundle
  right_inv p := Subtype.ext (insertBundle_removePoleBundle p)
  continuous_toFun := (insertBundle_continuous n k).subtype_mk _
  continuous_invFun := removePoleBundle_continuous n k

/-- The original positive-pole fiber is a closed subspace of the actual larger bundle. -/
theorem positivePoleFiber_isClosed (n k : ℕ) :
    IsClosed {p : ComplementBundle (n + 1) (k + 1) |
      embeddingColumn (bundleBase p) (Fin.last n) = spherePole k} :=
  isClosed_eq ((embeddingColumn_continuous (Fin.last n)).comp continuous_bundleBase)
    continuous_const

/-- The full pole insertion is a genuine closed embedding with its original inherited topology. -/
theorem insertBundle_closedEmbedding (n k : ℕ) :
    IsClosedEmbedding (insertBundle : ComplementBundle n k → _) :=
  (positivePoleFiber_isClosed n k).isClosedEmbedding_subtypeVal.comp
    (positivePoleFiberHomeomorph n k).isClosedEmbedding

/-- The original smaller bundle is inserted properly into the full larger bundle. -/
theorem insertBundle_proper (n k : ℕ) : IsProperMap (insertBundle : ComplementBundle n k → _) :=
  (insertBundle_closedEmbedding n k).isProperMap

/-- The negative-pole insertion is a proper map of the actual complement-bundle carriers. -/
theorem poleBundle_proper (n k : ℕ) : IsProperMap (poleBundle : ComplementBundle n k → _) :=
  (targetHomeomorph (reflectionFrame (spherePole k))).isProperMap.comp
    (insertBundle_proper n k)

/-- The full disk attachment is proper because its actual fiber norm is preserved uniformly. -/
theorem diskBundleAttachment_proper (n k : ℕ) : IsProperMap (diskBundleAttachment n k) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨diskBundleAttachment_continuous n k, ?_⟩
  intro K hK
  obtain ⟨R, hR⟩ := (hK.image (continuous_norm.comp continuous_bundleVector)).bddAbove
  apply (isCompact_univ.prod (bundleNormSublevel_isCompact n k R)).of_isClosed_subset
    (hK.isClosed.preimage (diskBundleAttachment_continuous n k))
  intro p hp
  refine ⟨Set.mem_univ _, ?_⟩
  change ‖bundleVector p.2‖ ≤ R
  rw [← diskBundleAttachment_norm n k p.1 p.2]
  exact hR ⟨diskBundleAttachment n k p, hp, rfl⟩

/-- Reflection respects the actual first-coordinate inclusion on every finite vector. -/
theorem reflectedVector_includeVector {k : ℕ} (w x : Euclidean k) :
    reflectedVector (includeVector w) (includeVector x) = includeVector (reflectedVector w x) := by
  rw [reflectedVector_apply, reflectedVector_apply, includeVector_inner, includeVector_norm,
    map_sub, map_smul]

/-- On the actual disk boundary the upper-hemisphere vector has zero pole coordinate. -/
theorem diskHemisphere_boundary {k : ℕ} (x : ClosedDisk k) (hx : ‖x.val‖ = 1) :
    diskHemisphere x = includeVector x.val := by
  simp [diskHemisphere, diskHeight, hx]

/-- The actual disk lift restricts on its boundary to the original smaller reflection. -/
theorem diskLiftFrame_boundary_includeVector {k : ℕ} (x : ClosedDisk k)
    (hx : ‖x.val‖ = 1) (v : Euclidean k) :
    matrixLinear (diskLiftFrame x).val (includeVector v) =
      includeVector (reflectedVector x.val v) := by
  rw [diskLiftFrame_apply,
    reflectedVector_perpendicular (spherePole k) (includeVector v)
      (by rw [spherePole_inner, includeVector_last]),
    diskHemisphere_boundary x hx, reflectedVector_includeVector]

/-- The disk boundary is the actual unit sphere in the smaller Euclidean space. -/
abbrev DiskBoundary (k : ℕ) := {x : Euclidean k // ‖x‖ = 1}

/-- The actual disk boundary is compact in its inherited Euclidean topology. -/
instance diskBoundary_compactSpace (k : ℕ) : CompactSpace (DiskBoundary k) := by
  have heq : {x : Euclidean k | ‖x‖ = 1} = Metric.sphere 0 1 := by
    ext x
    simp
  have h : IsCompact {x : Euclidean k | ‖x‖ = 1} := by
    rw [heq]
    exact isCompact_sphere 0 1
  exact isCompact_iff_compactSpace.mp h

/-- The boundary attaching function acts on the original full smaller bundle. -/
def boundaryClutch (n k : ℕ) : DiskBoundary k × ComplementBundle n k → ComplementBundle n k :=
  fun p => targetMap (reflectionFrame p.1.val) p.2

/-- The genuine boundary attaching function preserves every actual finite fiber norm. -/
theorem boundaryClutch_norm (n k : ℕ) (x : DiskBoundary k) (p : ComplementBundle n k) :
    ‖bundleVector (boundaryClutch n k (x, p))‖ = ‖bundleVector p‖ := by
  rw [boundaryClutch, targetMap_norm]

/-- The full boundary reflection family is continuous on its original sphere parameter. -/
theorem boundaryClutch_continuous (n k : ℕ) : Continuous (boundaryClutch n k) := by
  have hr : Continuous (fun x : DiskBoundary k => reflectionMatrix x.val) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hx : x.val ≠ 0 := by
      intro h
      have hn := x.property
      rw [h, norm_zero] at hn
      norm_num at hn
    exact (reflectionMatrix_continuousAt hx).comp continuous_subtype_val.continuousAt
  have hf : Continuous (fun x : DiskBoundary k => reflectionFrame x.val) :=
    continuous_induced_rng.mpr hr
  have hp : Continuous (fun p : DiskBoundary k × ComplementBundle n k =>
      (reflectionFrame p.1.val, p.2)) :=
    (hf.comp continuous_fst).prodMk continuous_snd
  exact (targetMap_joint_continuous n k k).comp hp

/-- The boundary attaching function is proper by compactness and its exact actual norm formula. -/
theorem boundaryClutch_proper (n k : ℕ) : IsProperMap (boundaryClutch n k) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨boundaryClutch_continuous n k, ?_⟩
  intro K hK
  obtain ⟨R, hR⟩ := (hK.image (continuous_norm.comp continuous_bundleVector)).bddAbove
  apply (isCompact_univ.prod (bundleNormSublevel_isCompact n k R)).of_isClosed_subset
    (hK.isClosed.preimage (boundaryClutch_continuous n k))
  intro p hp
  refine ⟨Set.mem_univ _, ?_⟩
  change ‖bundleVector p.2‖ ≤ R
  rw [← boundaryClutch_norm n k p.1 p.2]
  exact hR ⟨boundaryClutch n k p, hp, rfl⟩

/-- Every original reflection acts involutively on the entire actual complement-bundle carrier. -/
theorem reflectionBundle_involutive {n k : ℕ} (w : Euclidean k) (p : ComplementBundle n k) :
    targetMap (reflectionFrame w) (targetMap (reflectionFrame w) p) = p := by
  apply complementBundle_ext_columns
  · intro j
    rw [targetMap_embeddingColumn, targetMap_embeddingColumn]
    change reflectedVector w (reflectedVector w (embeddingColumn (bundleBase p) j)) = _
    exact reflectedVector_involutive _ _
  · rw [targetMap_bundleVector, targetMap_bundleVector]
    change reflectedVector w (reflectedVector w (bundleVector p)) = _
    exact reflectedVector_involutive _ _

/-- The original boundary attaching function is its own full finite inverse. -/
theorem boundaryClutch_involutive (n k : ℕ) (x : DiskBoundary k) (p : ComplementBundle n k) :
    boundaryClutch n k (x, boundaryClutch n k (x, p)) = p :=
  reflectionBundle_involutive _ _

/-- The full disk attachment and the negative-pole inclusion satisfy the actual
boundary relation. -/
theorem diskBundleAttachment_boundary (n k : ℕ) (x : ClosedDisk k) (hx : ‖x.val‖ = 1)
    (p : ComplementBundle n k) :
    diskBundleAttachment n k (x, p) =
      poleBundle (targetMap (reflectionFrame x.val) p) := by
  apply complementBundle_ext_columns
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [diskBundleAttachment_lastColumn, diskColumn_boundary x hx, poleBundle_lastColumn]
    · rw [diskBundleAttachment_castSuccColumn, poleBundle_castSuccColumn,
        diskLiftFrame_boundary_includeVector x hx, targetMap_embeddingColumn]
      rfl
  · rw [diskBundleAttachment_vector, poleBundle_vector,
      diskLiftFrame_boundary_includeVector x hx, targetMap_bundleVector]
    rfl

/-- The boundary square uses the original sphere-to-disk inclusion and the full clutching map. -/
theorem diskBundleAttachment_boundary_square (n k : ℕ) (x : DiskBoundary k)
    (p : ComplementBundle n k) :
    diskBundleAttachment n k (coefficientSphereToDisk k x, p) =
      poleBundle (boundaryClutch n k (x, p)) := by
  change diskBundleAttachment n k (coefficientSphereToDisk k x, p) =
    poleBundle (targetMap (reflectionFrame x.val) p)
  exact diskBundleAttachment_boundary n k (coefficientSphereToDisk k x) x.property p

/-- The negative-pole inclusion is injective on both original matrix and vector coordinates. -/
theorem poleBundle_injective (n k : ℕ) :
    Function.Injective (poleBundle : ComplementBundle n k → _) := by
  intro p q h
  apply insertBundle_injective n k
  exact (targetHomeomorph (reflectionFrame (spherePole k))).injective h

/-- On the actual open disk the full disk characteristic is injective in both arguments. -/
theorem diskBundleAttachment_interior_injective (n k : ℕ) (x y : ClosedDisk k)
    (hx : ‖x.val‖ < 1) (p q : ComplementBundle n k)
    (h : diskBundleAttachment n k (x, p) = diskBundleAttachment n k (y, q)) :
    x = y ∧ p = q := by
  have hc := congrArg (fun r : ComplementBundle (n + 1) (k + 1) =>
    embeddingColumn (bundleBase r) (Fin.last n)) h
  rw [diskBundleAttachment_lastColumn, diskBundleAttachment_lastColumn] at hc
  have hxy := diskColumn_injective_of_interior x y hx hc
  subst y
  refine ⟨rfl, ?_⟩
  apply insertBundle_injective n k
  exact (targetHomeomorph (diskLiftFrame x)).injective h

/-- A disk characteristic can meet the original negative-pole fiber only on its actual boundary. -/
theorem diskBundleAttachment_eq_poleBundle_boundary (n k : ℕ) (x : ClosedDisk k)
    (p q : ComplementBundle n k)
    (h : diskBundleAttachment n k (x, p) = poleBundle q) : ‖x.val‖ = 1 := by
  have hc := congrArg (fun r : ComplementBundle (n + 1) (k + 1) =>
    embeddingColumn (bundleBase r) (Fin.last n)) h
  rw [diskBundleAttachment_lastColumn, poleBundle_lastColumn] at hc
  exact (diskColumn_eq_neg_pole_iff x).mp hc

/-- The complete disk/pole kernel is exactly the original reflected boundary attaching relation. -/
theorem diskBundleAttachment_eq_poleBundle_iff (n k : ℕ) (x : ClosedDisk k)
    (p q : ComplementBundle n k) :
    diskBundleAttachment n k (x, p) = poleBundle q ↔
      ‖x.val‖ = 1 ∧ targetMap (reflectionFrame x.val) p = q := by
  constructor
  · intro h
    have hx := diskBundleAttachment_eq_poleBundle_boundary n k x p q h
    refine ⟨hx, ?_⟩
    apply poleBundle_injective n k
    rw [← diskBundleAttachment_boundary n k x hx p]
    exact h
  · rintro ⟨hx, hp⟩
    rw [diskBundleAttachment_boundary n k x hx p, hp]

/-- The full finite disk kernel preserves both interior coordinates and every
boundary reflection. -/
theorem diskBundleAttachment_eq_iff (n k : ℕ) (x y : ClosedDisk k)
    (p q : ComplementBundle n k) :
    diskBundleAttachment n k (x, p) = diskBundleAttachment n k (y, q) ↔
      (x = y ∧ p = q) ∨
        (‖x.val‖ = 1 ∧ ‖y.val‖ = 1 ∧
          targetMap (reflectionFrame x.val) p = targetMap (reflectionFrame y.val) q) := by
  constructor
  · intro h
    by_cases hx : ‖x.val‖ = 1
    · have hy : ‖y.val‖ = 1 := diskBundleAttachment_eq_poleBundle_boundary n k y q
        (targetMap (reflectionFrame x.val) p)
        (h.symm.trans (diskBundleAttachment_boundary n k x hx p))
      right
      refine ⟨hx, hy, ?_⟩
      apply poleBundle_injective n k
      rw [← diskBundleAttachment_boundary n k x hx p,
        ← diskBundleAttachment_boundary n k y hy q]
      exact h
    · left
      exact diskBundleAttachment_interior_injective n k x y
        (lt_of_le_of_ne x.property hx) p q h
  · rintro (⟨rfl, rfl⟩ | ⟨hx, hy, h⟩)
    · rfl
    · rw [diskBundleAttachment_boundary n k x hx p,
        diskBundleAttachment_boundary n k y hy q, h]

/-- Every actual larger-bundle point over the negative pole comes from the
original smaller bundle. -/
theorem exists_poleBundle_preimage (n k : ℕ) (p : ComplementBundle (n + 1) (k + 1))
    (hp : embeddingColumn (bundleBase p) (Fin.last n) = -spherePole k) :
    ∃ q : ComplementBundle n k, poleBundle q = p := by
  have hm : embeddingColumn
      (bundleBase (targetMap (reflectionFrame (spherePole k)) p)) (Fin.last n) =
        spherePole k := by
    rw [targetMap_embeddingColumn, hp]
    change reflectedVector (spherePole k) (-spherePole k) = spherePole k
    rw [map_neg, reflectedVector_self, neg_neg]
  let r : PositivePoleFiber n k := ⟨targetMap (reflectionFrame (spherePole k)) p, hm⟩
  refine ⟨removePoleBundle r, ?_⟩
  rw [poleBundle, insertBundle_removePoleBundle]
  exact reflectionBundle_involutive (spherePole k) p

/-- Every actual off-pole larger-bundle point comes from its unique open-disk coordinate. -/
theorem exists_diskBundleAttachment_preimage (n k : ℕ)
    (p : ComplementBundle (n + 1) (k + 1))
    (hp : embeddingColumn (bundleBase p) (Fin.last n) ≠ -spherePole k) :
    ∃ x : ClosedDisk k, ∃ q : ComplementBundle n k,
      ‖x.val‖ < 1 ∧ diskBundleAttachment n k (x, q) = p := by
  let u : ColumnSphere k :=
    ⟨embeddingColumn (bundleBase p) (Fin.last n), embeddingColumn_norm _ _⟩
  have hu : u.val ≠ -spherePole k := hp
  let x : ClosedDisk k := columnInverseDisk u hu
  have hc : diskColumn x = embeddingColumn (bundleBase p) (Fin.last n) :=
    diskColumn_columnInverseDisk u hu
  have hm : embeddingColumn (bundleBase (targetMap
      (CategoryTheory.Spectra.OrthogonalMatrixHom.transpose (diskLiftFrame x)) p))
        (Fin.last n) = spherePole k := by
    rw [targetMap_embeddingColumn, ← hc]
    change matrixLinear (diskLiftFrame x).val.transpose
      (matrixLinear (diskLiftFrame x).val (spherePole k)) = spherePole k
    rw [← matrixLinear_mul, (diskLiftFrame x).property.1, matrixLinear_one]
  let r : PositivePoleFiber n k :=
    ⟨targetMap (CategoryTheory.Spectra.OrthogonalMatrixHom.transpose (diskLiftFrame x)) p, hm⟩
  refine ⟨x, removePoleBundle r, columnInverseVector_norm_lt_one u hu, ?_⟩
  rw [diskBundleAttachment, insertBundle_removePoleBundle]
  exact targetMap_transpose_right (diskLiftFrame x) p

/-- The actual negative-pole fiber and characteristic disk cover the complete larger bundle. -/
def poleDiskBundleMap (n k : ℕ) :
    ComplementBundle n k ⊕ (ClosedDisk k × ComplementBundle n k) →
      ComplementBundle (n + 1) (k + 1) :=
  Sum.elim poleBundle (diskBundleAttachment n k)

/-- The full matrix/vector pole-and-disk cover is continuous in its original finite topology. -/
theorem poleDiskBundleMap_continuous (n k : ℕ) : Continuous (poleDiskBundleMap n k) :=
  (poleBundle_continuous n k).sumElim (diskBundleAttachment_continuous n k)

/-- The full actual larger complement bundle is covered in every source and target dimension. -/
theorem poleDiskBundleMap_surjective (n k : ℕ) : Function.Surjective (poleDiskBundleMap n k) := by
  intro p
  by_cases hp : embeddingColumn (bundleBase p) (Fin.last n) = -spherePole k
  · obtain ⟨q, hq⟩ := exists_poleBundle_preimage n k p hp
    exact ⟨Sum.inl q, hq⟩
  · obtain ⟨x, q, _, hq⟩ := exists_diskBundleAttachment_preimage n k p hp
    exact ⟨Sum.inr (x, q), hq⟩

/-- With zero embedding columns, the actual complement-bundle total space is Euclidean space. -/
def zeroColumnBundleHomeomorph (k : ℕ) : ComplementBundle 0 k ≃ₜ Euclidean k where
  toFun := bundleVector
  invFun x := ⟨(0, x), by
    constructor
    · ext i
      exact Fin.elim0 i
    · ext i
      exact Fin.elim0 i⟩
  left_inv p := by
    apply complementBundle_ext
    · ext i j
      exact Fin.elim0 j
    · rfl
  right_inv x := rfl
  continuous_toFun := continuous_bundleVector
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _

end CategoryTheory.Spectra.OrthogonalComplementBundle

namespace CategoryTheory.Spectra.OrthogonalCoendThom

open CategoryTheory.Spectra.OrthogonalComplementBundle

/-- The lifted actual closed disk of last-column characteristic coordinates. -/
abbrev LiftedDisk (k : ℕ) := ULift.{v, 0} (ClosedDisk k)

/-- The lifted actual sphere of boundary characteristic coordinates. -/
abbrev LiftedBoundary (k : ℕ) := ULift.{v, 0} (DiskBoundary k)

instance liftedDisk_locallyCompactSpace (k : ℕ) :
    LocallyCompactSpace (LiftedDisk.{v} k) := inferInstance

instance liftedBoundary_locallyCompactSpace (k : ℕ) :
    LocallyCompactSpace (LiftedBoundary.{v} k) := inferInstance

/-- The actual zero-column complement bundle identifies with the original lifted representation. -/
def liftedZeroColumnBundleHomeomorph (k : ℕ) :
    LiftedBundle.{v} 0 k ≃ₜ LiftedEuclidean.{v} k :=
  (Homeomorph.ulift (X := ComplementBundle 0 k)).trans
    ((zeroColumnBundleHomeomorph k).trans (Homeomorph.ulift (X := Euclidean k)).symm)

/-- The actual first-coordinate representation is the hyperplane perpendicular
to the negative pole. -/
def poleHyperplaneHomeomorph (k : ℕ) :
    Euclidean k ≃ₜ (ℝ ∙ (-spherePole k))ᗮ where
  toFun x := ⟨includeVector x, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
      inner_neg_left, spherePole_inner, includeVector_last, neg_zero]⟩
  invFun x := dropVector x.val
  left_inv := dropVector_includeVector
  right_inv x := by
    apply Subtype.ext
    have hx := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
    rw [inner_neg_left, spherePole_inner] at hx
    have hp : x.val.ofLp (Fin.last k) = 0 := by linarith
    have h := include_drop_add_pole x.val
    rw [hp, zero_smul, add_zero] at h
    exact h
  continuous_toFun := includeVector.continuous_of_finiteDimensional.subtype_mk _
  continuous_invFun := dropVector.continuous_of_finiteDimensional.comp continuous_subtype_val

/-- The actual Euclidean compactification is the column sphere with its
distinguished negative pole. -/
def euclideanOnePointColumnSphereHomeomorph (k : ℕ) :
    OnePoint (Euclidean k) ≃ₜ ColumnSphere k := by
  have heq : Metric.sphere (0 : Euclidean (k + 1)) 1 =
      {x : Euclidean (k + 1) | ‖x‖ = 1} := by
    ext x
    simp
  exact (Homeomorph.onePointCongr (poleHyperplaneHomeomorph k)).trans
    ((onePointHyperplaneHomeoUnitSphere (by simp [spherePole_norm] : ‖-spherePole k‖ = 1)).trans
      (Homeomorph.setCongr heq))

/-- The actual Euclidean sphere identification takes infinity to the exact attachment pole. -/
theorem euclideanOnePointColumnSphereHomeomorph_infty (k : ℕ) :
    (euclideanOnePointColumnSphereHomeomorph k OnePoint.infty).val = -spherePole k := by
  change ((onePointHyperplaneHomeoUnitSphere
    (by simp [spherePole_norm] : ‖-spherePole k‖ = 1)) OnePoint.infty).val = _
  simp only [onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty]

end CategoryTheory.Spectra.OrthogonalCoendThom
