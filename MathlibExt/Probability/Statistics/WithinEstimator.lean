/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.CochranIndependence
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The within estimator equals the dummy-variable regression coefficient

Panel data: observations `ι` are grouped by `grp : ι → G` (an individual, a firm, a region).
The fixed-effects (*within*) estimator regresses the group-demeaned response `ÿ = y - ȳ_grp` on
the group-demeaned regressors `Ẍ = X - X̄_grp`. The least-squares dummy-variable (LSDV)
regression instead regresses `y` on one dummy per group together with `X`. By the
Frisch–Waugh–Lovell argument, partialling the dummies out of `X` and `y` is exactly group
demeaning, so the two regressions give the same slope block.

The statements use normal equations, as `Matrix.frischWaughLovell` does: no rank or positivity
hypothesis is needed for the identities, and the within Gram matrix `Ẍᵀ Ẍ` is assumed
nonsingular only for the solved form. Groups may be unbalanced, singletons (their demeaned rows
vanish) or empty (their dummy column is zero). The partialling-out step is proved here directly
for the dummy block, without a general block Frisch–Waugh–Lovell theorem.

## Main definitions

* `groupDummy grp`: the `ι × G` dummy matrix (one dummy per group, no separate intercept).
* `withinVec grp y`, `withinMat grp X`: the within (group-demeaning) transformation, built on
  `ProbabilityTheory.groupMean`.

## Main results

* `lsdv_slope_within_normal_eq`: an LSDV solution `(α, β)` has `β` solving the within normal
  equations `(Ẍᵀ Ẍ) β = Ẍᵀ ÿ`.
* `lsdv_normal_eq_of_within_normal_eq`: conversely, a within solution `β` with intercepts
  `α g = ȳ_g - X̄_g β` solves the LSDV normal equations.
* `lsdv_slope_eq_within_estimator`: if `Ẍᵀ Ẍ` is nonsingular, the LSDV slope is the within
  estimator `(Ẍᵀ Ẍ)⁻¹ Ẍᵀ ÿ`.

## References

* J. M. Wooldridge, *Econometric Analysis of Cross Section and Panel Data*, 2nd ed., MIT Press
  (2010), §10.5 (fixed-effects estimation, the dummy variable regression).
* R. Frisch, F. V. Waugh, *Partial time regressions as compared with individual trends*,
  Econometrica 1 (1933), 387–401; M. C. Lovell, *Seasonal adjustment of economic time series and
  multiple regression analysis*, J. Amer. Statist. Assoc. 58 (1963), 993–1010.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Probability.Statistics.WithinEstimator

open ProbabilityTheory

/-- The group-dummy design matrix: entry `(i, g)` is `1` if observation `i` belongs to group `g`
and `0` otherwise (one dummy per group, no separate intercept). -/
def groupDummy {ι G : Type*} [DecidableEq G] (grp : ι → G) : Matrix ι G ℝ :=
  Matrix.of fun i g => if grp i = g then 1 else 0

/-- The within (group-demeaning) transformation of a response vector:
`ÿ i = y i - ȳ_{grp i}`. -/
noncomputable def withinVec {ι G : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G)
    (y : ι → ℝ) : ι → ℝ :=
  fun i => y i - groupMean grp y (grp i)

/-- The within transformation applied to each column of a regressor matrix:
`Ẍ i j = X i j - X̄_{grp i, j}`. -/
noncomputable def withinMat {ι G π : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G)
    (X : Matrix ι π ℝ) : Matrix ι π ℝ :=
  Matrix.of fun i j => X i j - groupMean grp (fun k => X k j) (grp i)

lemma sum_demeaned_eq_zero {ι G : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G)
    (x : ι → ℝ) (g : G) :
    ∑ i ∈ Finset.univ.filter (fun i => grp i = g), (x i - groupMean grp x g) = 0 := by
  have hsum : (∑ i with grp i = g, x i) = ∑ i ∈ Finset.univ.filter (fun i => grp i = g), x i := rfl
  have hcard : (#{i | grp i = g} : ℕ) = #(Finset.univ.filter (fun i => grp i = g)) := rfl
  unfold groupMean
  rw [hsum, hcard]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  by_cases hn : #(Finset.univ.filter (fun i => grp i = g)) = 0
  · have hs : Finset.univ.filter (fun i => grp i = g) = ∅ := Finset.card_eq_zero.mp hn
    rw [hs]
    simp
  · have hnR : ((#(Finset.univ.filter (fun i => grp i = g)) : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hn
    have hcancel : ((#(Finset.univ.filter (fun i => grp i = g)) : ℕ) : ℝ) *
        ((∑ i ∈ Finset.univ.filter (fun i => grp i = g), x i) /
          ((#(Finset.univ.filter (fun i => grp i = g)) : ℕ) : ℝ)) =
        ∑ i ∈ Finset.univ.filter (fun i => grp i = g), x i := by
      field_simp
    rw [hcancel]
    exact sub_self _

lemma dummy_mulVec_apply {ι G : Type*} [Fintype G] [DecidableEq G] (grp : ι → G)
    (v : G → ℝ) (i : ι) :
    ((groupDummy grp) *ᵥ v) i = v (grp i) := by
  unfold groupDummy
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  have h1 : ∀ g : G, (if grp i = g then (1 : ℝ) else 0) * v g =
      (if grp i = g then v g else 0) := fun g => by split_ifs <;> simp_all
  simp only [h1]
  rw [Finset.sum_ite_eq]
  simp

lemma transpose_dummy_mulVec_apply {ι G : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G)
    (w : ι → ℝ) (g : G) :
    (((groupDummy grp)ᵀ *ᵥ w) g) = ∑ i ∈ Finset.univ.filter (fun i => grp i = g), w i := by
  unfold groupDummy
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
  have h1 : ∀ i : ι, (if grp i = g then (1 : ℝ) else 0) * w i =
      (if grp i = g then w i else 0) := fun i => by split_ifs <;> simp_all
  simp only [h1]
  rw [Finset.sum_filter]

lemma transpose_dummy_withinVec_eq_zero {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (y : ι → ℝ) :
    (groupDummy grp)ᵀ *ᵥ withinVec grp y = 0 := by
  funext g
  simp only [Pi.zero_apply]
  rw [transpose_dummy_mulVec_apply]
  have h : ∀ i ∈ Finset.univ.filter (fun i => grp i = g),
      withinVec grp y i = y i - groupMean grp y g := by
    intro i hi
    have hgi : grp i = g := (Finset.mem_filter.mp hi).2
    unfold withinVec
    rw [hgi]
  have heq : (∑ i ∈ Finset.univ.filter (fun i => grp i = g), withinVec grp y i) =
      ∑ i ∈ Finset.univ.filter (fun i => grp i = g), (y i - groupMean grp y g) :=
    Finset.sum_congr rfl h
  rw [heq]
  exact sum_demeaned_eq_zero grp y g

lemma transpose_dummy_withinMat_eq_zero {ι G π : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (X : Matrix ι π ℝ) :
    (groupDummy grp)ᵀ * withinMat grp X = 0 := by
  ext g j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply]
  unfold groupDummy withinMat
  simp only [Matrix.of_apply]
  have h1 : ∀ i : ι, (if grp i = g then (1 : ℝ) else 0) *
      (X i j - groupMean grp (fun k => X k j) (grp i)) =
      (if grp i = g then (X i j - groupMean grp (fun k => X k j) (grp i)) else 0) := by
    intro i
    split_ifs <;> simp_all
  simp only [h1]
  rw [← Finset.sum_filter]
  have h2 : ∀ i ∈ Finset.univ.filter (fun i => grp i = g),
      (X i j - groupMean grp (fun k => X k j) (grp i)) =
      (X i j - groupMean grp (fun k => X k j) g) := by
    intro i hi
    have hgi : grp i = g := (Finset.mem_filter.mp hi).2
    rw [hgi]
  have heq : (∑ i ∈ Finset.univ.filter (fun i => grp i = g),
        (X i j - groupMean grp (fun k => X k j) (grp i))) =
      ∑ i ∈ Finset.univ.filter (fun i => grp i = g),
        (X i j - groupMean grp (fun k => X k j) g) :=
    Finset.sum_congr rfl h2
  rw [heq]
  exact sum_demeaned_eq_zero grp (fun k => X k j) g

lemma withinMat_add_dummy {ι G π : Type*} [Fintype ι] [Fintype G] [DecidableEq G]
    (grp : ι → G) (X : Matrix ι π ℝ) :
    X = withinMat grp X + groupDummy grp *
      Matrix.of (fun g j => groupMean grp (fun k => X k j) g) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply]
  unfold groupDummy withinMat
  simp only [Matrix.of_apply]
  have h1 : ∀ g : G, (if grp i = g then (1 : ℝ) else 0) *
      groupMean grp (fun k => X k j) g =
      (if grp i = g then groupMean grp (fun k => X k j) g else 0) := by
    intro g
    split_ifs <;> simp_all
  simp only [h1]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  ring

lemma withinVec_add_dummy {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq G]
    (grp : ι → G) (y : ι → ℝ) :
    y = withinVec grp y + groupDummy grp *ᵥ (fun g => groupMean grp y g) := by
  funext i
  simp only [Pi.add_apply]
  rw [dummy_mulVec_apply]
  unfold withinVec
  ring

-- Helper: Ẍᵀ * D = 0
lemma withinMat_transpose_mul_dummy_eq_zero {ι G π : Type*} [Fintype ι]
    [DecidableEq G] (grp : ι → G) (X : Matrix ι π ℝ) :
    (withinMat grp X)ᵀ * groupDummy grp = 0 := by
  have hDW := transpose_dummy_withinMat_eq_zero grp X
  have h := congrArg Matrix.transpose hDW
  rw [Matrix.transpose_mul, Matrix.transpose_transpose] at h
  rwa [Matrix.transpose_zero] at h

/-- **Dummy-variable regression ⇒ within normal equations**: if `(α, β)` solves the least-squares
normal equations of the regression of `y` on group dummies and regressors `X` (LSDV), then the
slope block `β` solves the normal equations of the within regression of `ÿ` on `Ẍ`. -/
theorem lsdv_slope_within_normal_eq {ι G π : Type*} [Fintype ι] [Fintype G] [DecidableEq G]
    [Fintype π] (grp : ι → G) {X : Matrix ι π ℝ} {y : ι → ℝ} {α : G → ℝ} {β : π → ℝ}
    (hD : (groupDummy grp)ᵀ *ᵥ (y - groupDummy grp *ᵥ α - X *ᵥ β) = 0)
    (hX : Xᵀ *ᵥ (y - groupDummy grp *ᵥ α - X *ᵥ β) = 0) :
    ((withinMat grp X)ᵀ * withinMat grp X) *ᵥ β = (withinMat grp X)ᵀ *ᵥ withinVec grp y := by
  have hXeq := withinMat_add_dummy grp X
  have hXTeq : Xᵀ = (withinMat grp X)ᵀ +
      (Matrix.of (fun g j => groupMean grp (fun k => X k j) g))ᵀ * (groupDummy grp)ᵀ := by
    conv_lhs => rw [hXeq]
    rw [Matrix.transpose_add, Matrix.transpose_mul]
  have hWTe : (withinMat grp X)ᵀ *ᵥ (y - groupDummy grp *ᵥ α - X *ᵥ β) = 0 := by
    have h := hX
    rw [hXTeq, Matrix.add_mulVec, ← Matrix.mulVec_mulVec] at h
    rw [hD, Matrix.mulVec_zero, add_zero] at h
    exact h
  have hy := withinVec_add_dummy grp y
  have hXβ : X *ᵥ β = (withinMat grp X) *ᵥ β + (groupDummy grp) *ᵥ
      ((Matrix.of (fun g j => groupMean grp (fun k => X k j) g)) *ᵥ β) := by
    conv_lhs => rw [hXeq]
    rw [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  have he : (y - groupDummy grp *ᵥ α - X *ᵥ β) =
      ((withinVec grp y - (withinMat grp X) *ᵥ β) +
        (groupDummy grp) *ᵥ ((fun g => groupMean grp y g) - α -
          (Matrix.of (fun g j => groupMean grp (fun k => X k j) g)) *ᵥ β)) := by
    conv_lhs => rw [hy, hXβ]
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
    abel
  have hWD := withinMat_transpose_mul_dummy_eq_zero grp X
  have hcalc : (withinMat grp X)ᵀ *ᵥ (y - groupDummy grp *ᵥ α - X *ᵥ β) =
      (((withinMat grp X)ᵀ *ᵥ withinVec grp y - ((withinMat grp X)ᵀ * withinMat grp X) *ᵥ β) +
        ((withinMat grp X)ᵀ * groupDummy grp) *ᵥ
          ((fun g => groupMean grp y g) - α -
            (Matrix.of (fun g j => groupMean grp (fun k => X k j) g)) *ᵥ β)) := by
    rw [he, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hWD, Matrix.zero_mulVec, add_zero] at hcalc
  rw [hWTe] at hcalc
  have hsub : (withinMat grp X)ᵀ *ᵥ withinVec grp y -
      ((withinMat grp X)ᵀ * withinMat grp X) *ᵥ β = 0 := hcalc.symm
  have heq := sub_eq_zero.mp hsub
  exact heq.symm

/-- **Within normal equations ⇒ dummy-variable regression**: if `β` solves the within normal
equations, then `β` together with the group intercepts `α g = ȳ_g - X̄_g β` solves the LSDV
normal equations. -/
theorem lsdv_normal_eq_of_within_normal_eq {ι G π : Type*} [Fintype ι] [Fintype G]
    [DecidableEq G] [Fintype π] (grp : ι → G) {X : Matrix ι π ℝ} {y : ι → ℝ} {β : π → ℝ}
    (hW : ((withinMat grp X)ᵀ * withinMat grp X) *ᵥ β = (withinMat grp X)ᵀ *ᵥ withinVec grp y) :
    (groupDummy grp)ᵀ *ᵥ (y - groupDummy grp *ᵥ
        (fun g => groupMean grp y g - ∑ j, groupMean grp (fun k => X k j) g * β j) - X *ᵥ β) = 0 ∧
      Xᵀ *ᵥ (y - groupDummy grp *ᵥ
        (fun g => groupMean grp y g - ∑ j, groupMean grp (fun k => X k j) g * β j) -
          X *ᵥ β) = 0 := by
  have hXeq := withinMat_add_dummy grp X
  have hXTeq : Xᵀ = (withinMat grp X)ᵀ +
      (Matrix.of (fun g j => groupMean grp (fun k => X k j) g))ᵀ * (groupDummy grp)ᵀ := by
    conv_lhs => rw [hXeq]
    rw [Matrix.transpose_add, Matrix.transpose_mul]
  have hy := withinVec_add_dummy grp y
  have hXβ : X *ᵥ β = (withinMat grp X) *ᵥ β + (groupDummy grp) *ᵥ
      ((Matrix.of (fun g j => groupMean grp (fun k => X k j) g)) *ᵥ β) := by
    conv_lhs => rw [hXeq]
    rw [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  have hα : (fun g => groupMean grp y g - ∑ j, groupMean grp (fun k => X k j) g * β j) =
      (fun g => groupMean grp y g) -
        (Matrix.of (fun g j => groupMean grp (fun k => X k j) g)) *ᵥ β := by
    funext g
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  have he : (y - groupDummy grp *ᵥ
        (fun g => groupMean grp y g - ∑ j, groupMean grp (fun k => X k j) g * β j) - X *ᵥ β) =
      (withinVec grp y - (withinMat grp X) *ᵥ β) := by
    rw [hα]
    conv_lhs => rw [hXβ]
    nth_rewrite 1 [hy]
    rw [Matrix.mulVec_sub]
    abel
  have hDw := transpose_dummy_withinVec_eq_zero grp y
  have hDW := transpose_dummy_withinMat_eq_zero grp X
  have hD2 : (groupDummy grp)ᵀ *ᵥ (withinVec grp y - (withinMat grp X) *ᵥ β) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hDw, hDW]
    rw [Matrix.zero_mulVec, sub_zero]
  constructor
  · rw [he]
    exact hD2
  · rw [he]
    rw [hXTeq, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    rw [hD2, Matrix.mulVec_zero, add_zero]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    exact sub_eq_zero.mpr hW.symm

/-- **Within estimator = dummy-variable coefficient**: if `(α, β)` solves the LSDV normal
equations and the within Gram matrix `Ẍᵀ Ẍ` is nonsingular, then `β = (Ẍᵀ Ẍ)⁻¹ Ẍᵀ ÿ`. -/
theorem lsdv_slope_eq_within_estimator {ι G π : Type*} [Fintype ι] [Fintype G] [DecidableEq G]
    [Fintype π] [DecidableEq π] (grp : ι → G) {X : Matrix ι π ℝ} {y : ι → ℝ} {α : G → ℝ}
    {β : π → ℝ}
    (hD : (groupDummy grp)ᵀ *ᵥ (y - groupDummy grp *ᵥ α - X *ᵥ β) = 0)
    (hX : Xᵀ *ᵥ (y - groupDummy grp *ᵥ α - X *ᵥ β) = 0)
    (hG : IsUnit ((withinMat grp X)ᵀ * withinMat grp X).det) :
    β = ((withinMat grp X)ᵀ * withinMat grp X)⁻¹ *ᵥ
      ((withinMat grp X)ᵀ *ᵥ withinVec grp y) := by
  have hW := lsdv_slope_within_normal_eq grp hD hX
  have hInv : ((withinMat grp X)ᵀ * withinMat grp X)⁻¹ *
      ((withinMat grp X)ᵀ * withinMat grp X) = 1 :=
    Matrix.nonsing_inv_mul _ hG
  calc β = (((withinMat grp X)ᵀ * withinMat grp X)⁻¹ *
        ((withinMat grp X)ᵀ * withinMat grp X)) *ᵥ β := by
        rw [hInv, Matrix.one_mulVec]
    _ = ((withinMat grp X)ᵀ * withinMat grp X)⁻¹ *ᵥ
          (((withinMat grp X)ᵀ * withinMat grp X) *ᵥ β) := by
        rw [← Matrix.mulVec_mulVec]
    _ = ((withinMat grp X)ᵀ * withinMat grp X)⁻¹ *ᵥ
          ((withinMat grp X)ᵀ *ᵥ withinVec grp y) := by
        rw [hW]

end MathlibExt.Probability.Statistics.WithinEstimator
