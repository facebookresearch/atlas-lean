/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.DrinfeldUpperHalfPlane
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open DrinfeldUpperHalfPlane
open scoped MatrixGroups

/-- Source-shaped consumer with the original binders. -/
example (K₀ : Type*) [Field K₀] (K : Type*) [Field K] [Algebra K₀ K]
    (z : K) : z ∈ upperHalfPlane K₀ K ↔ ∀ x : K₀, algebraMap K₀ K x ≠ z :=
  mem_upperHalfPlane_iff K₀ z

/-- A point `x + y i` with `y ≠ 0` lies in the Drinfeld upper half plane of `ℂ` over `ℚ`. -/
private theorem mem_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : w ∈ upperHalfPlane ℚ ℂ := by
  rw [mem_upperHalfPlane_iff]
  intro x hx
  apply hw
  rw [← hx]
  simp

/-- Unfolding: the point `i` lies in the Drinfeld upper half plane over `ℚ`. -/
example : Complex.I ∈ upperHalfPlane ℚ ℂ := by
  rw [mem_upperHalfPlane_iff]
  intro x hx
  have h := congrArg Complex.im hx
  simp at h

private theorem I_mem : Complex.I ∈ upperHalfPlane ℚ ℂ :=
  mem_of_im_ne_zero (by simp)

/-- Rational points, such as `0`, are not in the upper half plane. -/
private theorem zero_not_mem : (0 : ℂ) ∉ upperHalfPlane ℚ ℂ := fun h =>
  (mem_upperHalfPlane_iff ℚ (0 : ℂ)).mp h 0 (map_zero _)

/-- The Möbius formula of the identity matrix is the identity. -/
example (z : ℂ) : moebius ℚ ℂ (1 : GL (Fin 2) ℚ) z = z := by
  simp [moebius]

/-- The identity of `PGL(2, ℚ)` fixes `i`. -/
example : pmoebius ℚ (1 : PGL(2, ℚ)) Complex.I = Complex.I := by
  rw [pmoebius_one]

/-- The translation `z ↦ z + 1`. -/
private def T : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])

/-- The inversion `z ↦ 1 / z`. -/
private def S : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

/-- The translation sends `i` to `i + 1`. -/
private theorem pmoebius_T_I :
    pmoebius ℚ (Matrix.ProjGenLinGroup.mk T) Complex.I = Complex.I + 1 := by
  rw [pmoebius_mk ℚ T Complex.I (by simp [T])]
  simp [moebius, T]

/-- The inversion sends `w` to `1 / w` for every nonzero `w`. -/
private theorem pmoebius_S {w : ℂ} (hw : w ≠ 0) :
    pmoebius ℚ (Matrix.ProjGenLinGroup.mk S) w = 1 / w := by
  rw [pmoebius_mk ℚ S w (by simpa [S] using hw)]
  simp [moebius, S]

/-- The inversion sends `i` to `-i`, a point of the upper half plane again. -/
example : pmoebius ℚ (Matrix.ProjGenLinGroup.mk S) Complex.I = -Complex.I ∧
    pmoebius ℚ (Matrix.ProjGenLinGroup.mk S) Complex.I ∈ upperHalfPlane ℚ ℂ ∧
    -Complex.I ∈ upperHalfPlane ℚ ℂ := by
  refine ⟨?_, pmoebius_mem_upperHalfPlane ℚ I_mem _, mem_of_im_ne_zero (by simp)⟩
  rw [pmoebius_S Complex.I_ne_zero, one_div, Complex.inv_I]

/-- The translation keeps `i` in the upper half plane, and its image is `i + 1`. -/
example : pmoebius ℚ (Matrix.ProjGenLinGroup.mk T) Complex.I ∈ upperHalfPlane ℚ ℂ ∧
    Complex.I + 1 ∈ upperHalfPlane ℚ ℂ :=
  ⟨pmoebius_mem_upperHalfPlane ℚ I_mem _, mem_of_im_ne_zero (by simp)⟩

private theorem I_add_one_ne_zero : Complex.I + 1 ≠ 0 := fun h => by
  simpa using congrArg Complex.im h

/-- Composition: inverting after translating sends `i` to `(1 - i) / 2`, computed through
`pmoebius_mul` and, independently, through the product matrix `!![0, 1; 1, 1]`. -/
example : pmoebius ℚ (Matrix.ProjGenLinGroup.mk S * Matrix.ProjGenLinGroup.mk T) Complex.I =
      (1 - Complex.I) / 2 ∧
    pmoebius ℚ (Matrix.ProjGenLinGroup.mk (S * T)) Complex.I = (1 - Complex.I) / 2 := by
  have hval : 1 / (Complex.I + 1) = (1 - Complex.I) / 2 := by
    rw [div_eq_div_iff I_add_one_ne_zero two_ne_zero]
    ring_nf
    rw [Complex.I_sq]
    ring
  refine ⟨?_, ?_⟩
  · rw [pmoebius_mul ℚ I_mem, pmoebius_T_I, pmoebius_S I_add_one_ne_zero, hval]
  · rw [pmoebius_mk ℚ (S * T) Complex.I (by simpa [S, T, add_comm] using I_add_one_ne_zero),
      ← hval]
    simp [moebius, S, T, add_comm]

/-- The other order: translating after inverting sends `i` to `1 - i`, so the order of composition
matters. -/
example : pmoebius ℚ (Matrix.ProjGenLinGroup.mk T * Matrix.ProjGenLinGroup.mk S) Complex.I =
    1 - Complex.I := by
  rw [pmoebius_mul ℚ I_mem, pmoebius_S Complex.I_ne_zero,
    pmoebius_mk ℚ T _ (by simp [T]), one_div, Complex.inv_I]
  simp [moebius, T, sub_eq_neg_add]

/-- Scalar descent: the representative `2 T` of the class of `T` in `PGL(2, ℚ)` gives the same
transformation, `i ↦ i + 1`. -/
example : Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (2 : ℚ) two_ne_zero) * T) =
      Matrix.ProjGenLinGroup.mk T ∧
    pmoebius ℚ (Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (2 : ℚ) two_ne_zero) * T))
      Complex.I = Complex.I + 1 := by
  refine ⟨by rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul], ?_⟩
  rw [pmoebius_mk ℚ _ Complex.I (by simp [T, Matrix.GeneralLinearGroup.scalar])]
  simp only [moebius, T, Matrix.GeneralLinearGroup.scalar]
  field_simp
  simp
  ring

/-- Denominator handling: the inversion sends the rational point `0` to `∞`, which `pmoebius`
reads as `0`; `0` is not a point of the upper half plane, so it cannot be a theta parameter. -/
example : Matrix.ProjGenLinGroup.mk S • ((0 : ℂ) : OnePoint ℂ) = OnePoint.infty ∧
    pmoebius ℚ (Matrix.ProjGenLinGroup.mk S) (0 : ℂ) = 0 ∧
    ¬ ∃ a : upperHalfPlane ℚ ℂ, (a : ℂ) = 0 := by
  have hinf : Matrix.ProjGenLinGroup.mk S • ((0 : ℂ) : OnePoint ℂ) = OnePoint.infty := by
    rw [mk_smul_eq, gl_smul_def, OnePoint.smul_some_eq_ite]
    simp [S]
  refine ⟨hinf, by rw [pmoebius, hinf, toAffine_infty], ?_⟩
  rintro ⟨a, ha⟩
  exact zero_not_mem (ha ▸ a.2)

/-- A theta factor at the inversion uses the actual images `S i = -i` and `S (2 i) = -i / 2`. -/
example (z₀ z : ℂ) :
    thetaFactor (MonoidHom.id PGL(2, ℚ)) ⟨Complex.I, I_mem⟩
        ⟨2 * Complex.I, mem_of_im_ne_zero (by simp)⟩ z₀ z (Matrix.ProjGenLinGroup.mk S) =
      crossRatio z z₀ (-Complex.I) (-(Complex.I / 2)) := by
  have h2 : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  simp only [thetaFactor, MonoidHom.id_apply]
  rw [pmoebius_S Complex.I_ne_zero, pmoebius_S h2, one_div, one_div, Complex.inv_I, mul_inv,
    Complex.inv_I]
  ring_nf

/-- The same factor as a number, at `z₀ = i` and `z = 0`: `[0, i; -i, -i / 2] = 3 / 2`. The value
does not go through `crossRatio`, so a reversed cross-ratio convention (giving `2 / 3`) fails. -/
example : thetaFactor (MonoidHom.id PGL(2, ℚ)) ⟨Complex.I, I_mem⟩
      ⟨2 * Complex.I, mem_of_im_ne_zero (by simp)⟩ Complex.I 0 (Matrix.ProjGenLinGroup.mk S) =
    3 / 2 := by
  have h2 : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  simp only [thetaFactor, MonoidHom.id_apply, crossRatio]
  rw [pmoebius_S Complex.I_ne_zero, pmoebius_S h2, one_div, one_div, Complex.inv_I, mul_inv,
    Complex.inv_I]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- Over the trivial group the theta function is the single cross-ratio `[z, z₀; a, b]`. -/
example (a b : upperHalfPlane ℚ ℂ) (z₀ z : ℂ) :
    theta (1 : Unit →* PGL(2, ℚ)) a b z₀ z = crossRatio z z₀ a b := by
  rw [theta_eq_of_hasProd (hasProd_fintype _), Fintype.prod_unique]
  simp [thetaFactor]

/-- The same as a number: over the trivial group `θ(i, 2 i; 0)`, normalized at `3 i`, is
`[0, 3 i; i, 2 i] = 1 / 4`; a reversed cross-ratio convention gives `4`. -/
example : theta (1 : Unit →* PGL(2, ℚ)) ⟨Complex.I, I_mem⟩
      ⟨2 * Complex.I, mem_of_im_ne_zero (by simp)⟩ (3 * Complex.I) 0 = 1 / 4 := by
  rw [theta_eq_of_hasProd (hasProd_fintype _), Fintype.prod_unique]
  simp only [thetaFactor, MonoidHom.one_apply, pmoebius_one, crossRatio]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- With `T2Space K`, `theta` is available over every topological field extension of `ℚ`. -/
example {K : Type*} [Field K] [Algebra ℚ K] [DecidableEq K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] (a b : upperHalfPlane ℚ K) (z₀ z : K) :
    theta (MonoidHom.id PGL(2, ℚ)) a b z₀ z = theta (MonoidHom.id PGL(2, ℚ)) a b z₀ z :=
  rfl

/-- Without `T2Space K`, `theta` does not elaborate: a product can then have several limits. -/
example {K : Type*} [Field K] [Algebra ℚ K] [DecidableEq K] [TopologicalSpace K]
    [IsTopologicalRing K] (_a _b : upperHalfPlane ℚ K) (_z₀ _z : K) : True := by
  fail_if_success have := theta (MonoidHom.id PGL(2, ℚ)) _a _b _z₀ _z
  trivial

/-- Over the trivial group the period `θ(a, a; z₀)` is `[z₀, z₀; a, a] = 1`. -/
example (a z₀ : upperHalfPlane ℚ ℂ) (h : (z₀ : ℂ) ≠ a) :
    period (1 : Unit →* PGL(2, ℚ)) a z₀ () () = 1 := by
  have h' : (z₀ : ℂ) - a ≠ 0 := sub_ne_zero.mpr h
  rw [period, theta_eq_of_hasProd (hasProd_fintype _), Fintype.prod_unique]
  simp only [thetaFactor, MonoidHom.one_apply, pmoebius_one, crossRatio]
  exact div_self (mul_ne_zero h' h')

/-- Regression for the normalization point: at `z₀ = a` the factor `[a, a; a, a]` has denominator
`0`, so over the trivial group `period` is the totalized value `0`, while it is `1` for `z₀ ≠ a`
(previous example). -/
example (a : upperHalfPlane ℚ ℂ) : period (1 : Unit →* PGL(2, ℚ)) a a () () = 0 := by
  rw [period, theta_eq_of_hasProd (hasProd_fintype _), Fintype.prod_unique]
  simp [thetaFactor, crossRatio]

/-- Automorphy on the upper half plane is the source's pointwise condition. -/
example (ρ : PGL(2, ℚ) →* PGL(2, ℚ)) (f : ℂ → ℂ) (c : PGL(2, ℚ) →* ℂˣ) :
    IsAutomorphicWithMultiplier ρ (upperHalfPlane ℚ ℂ) f c ↔
      ∀ γ, ∀ z ∈ upperHalfPlane ℚ ℂ, f (pmoebius ℚ (ρ γ) z) = (c γ : ℂ) * f z :=
  isAutomorphicWithMultiplier_iff_of_subset subset_rfl

/-- The involution `z ↦ (z + 1) / (z - 1)`, which swaps `1` and `∞`. -/
private def W : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 1, -1] (by norm_num [Matrix.det_fin_two])

private theorem mk_W_sq : Matrix.ProjGenLinGroup.mk W ^ 2 = 1 := by
  have hW : W ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (2 : ℚ) two_ne_zero) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [W, sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar]
  rw [← map_pow, hW, Matrix.ProjGenLinGroup.mk_scalar]

private theorem mk_W_smul_one :
    Matrix.ProjGenLinGroup.mk W • ((1 : ℂ) : OnePoint ℂ) = OnePoint.infty := by
  rw [mk_smul_eq, gl_smul_def, OnePoint.smul_some_eq_ite]
  simp [W]

/-- Poles impose no condition: for the group generated by `W`, the identity function is invariant
on `{1}`, since every element sends `1` either to itself or to `∞`. The affine reading through
`pmoebius` would instead compare `f 0` with `f 1`, as `W` sends `1` to `∞` and `pmoebius` reads
it as `0`. -/
example : IsInvariant (zpowersHom PGL(2, ℚ) (Matrix.ProjGenLinGroup.mk W)) {(1 : ℂ)} id ∧
    pmoebius ℚ (Matrix.ProjGenLinGroup.mk W) (1 : ℂ) = 0 := by
  refine ⟨?_, by rw [pmoebius, mk_W_smul_one, toAffine_infty]⟩
  intro n z hz w hw
  rw [Set.mem_singleton_iff] at hz
  subst hz
  rw [zpowersHom_apply] at hw
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n.toAdd
  · rw [hk, zpow_mul, zpow_ofNat, mk_W_sq, one_zpow, one_smul] at hw
    obtain rfl : w = 1 := (OnePoint.coe_injective hw).symm
    simp
  · rw [hk, zpow_add, zpow_mul, zpow_ofNat, mk_W_sq, one_zpow, one_mul, zpow_one,
      mk_W_smul_one] at hw
    exact absurd hw (OnePoint.infty_ne_coe w)
