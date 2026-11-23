/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.Killing.VectorSpace

/-!
# Tests for Killing vector fields on the Euclidean plane
-/

open Bundle CovariantDerivative
open scoped Manifold ContDiff

noncomputable section

namespace KillingPlaneTests

/-- First standard basis vector. -/
abbrev e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

/-- Second standard basis vector. -/
abbrev e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

/-- Right-angle rotation. -/
def J : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.proj 0).smulRight e₁ - (EuclideanSpace.proj 1).smulRight e₀

/-- Shear map. -/
def Shear : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.proj 1).smulRight e₀

/-- Coordinates of `e₀`. -/
theorem e₀_coords : e₀.ofLp 0 = 1 ∧ e₀.ofLp 1 = 0 :=
  ⟨PiLp.single_eq_same 2 0 1, PiLp.single_eq_of_ne 2 (by decide) 1⟩

/-- Coordinates of `e₁`. -/
theorem e₁_coords : e₁.ofLp 0 = 0 ∧ e₁.ofLp 1 = 1 :=
  ⟨PiLp.single_eq_of_ne 2 (by decide) 1, PiLp.single_eq_same 2 1 1⟩

/-- Inner products with the basis. -/
theorem basis_inner_left (v : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ e₀ v = v.ofLp 0 ∧ inner ℝ e₁ v = v.ofLp 1 := by
  constructor
  · show inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) v = _
    rw [EuclideanSpace.inner_single_left]; simp
  · show inner ℝ (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) v = _
    rw [EuclideanSpace.inner_single_left]; simp

/-- The basis is orthonormal. -/
theorem basis_gram : inner ℝ e₀ e₀ = 1 ∧ inner ℝ e₁ e₁ = 1 ∧
    inner ℝ e₀ e₁ = 0 ∧ inner ℝ e₁ e₀ = 0 := by
  have h0 := (basis_inner_left e₀).1; rw [e₀_coords.1] at h0
  have h1 := (basis_inner_left e₁).1; rw [e₁_coords.1] at h1
  have h2 := (basis_inner_left e₀).2; rw [e₀_coords.2] at h2
  have h3 := (basis_inner_left e₁).2; rw [e₁_coords.2] at h3
  refine ⟨h0, h3, h1, ?_⟩; rw [real_inner_comm]; exact h1

/-- Both basis vectors are nonzero. -/
theorem basis_ne_zero : e₀ ≠ 0 ∧ e₁ ≠ (0 : EuclideanSpace ℝ (Fin 2)) := by
  constructor
  · intro h; have h00 := e₀_coords.1; rw [h] at h00
    rw [PiLp.zero_apply] at h00; exact one_ne_zero h00.symm
  · intro h; have h11 := e₁_coords.2; rw [h] at h11
    rw [PiLp.zero_apply] at h11; exact one_ne_zero h11.symm

/-- Formula for `J`. -/
theorem J_apply (u : EuclideanSpace ℝ (Fin 2)) :
    J u = (u.ofLp 0) • e₁ - (u.ofLp 1) • e₀ := by
  unfold J
  rw [sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj,
    EuclideanSpace.coe_proj]

/-- Pin `J e₀ = e₁`. -/
example : J e₀ = e₁ := by
  rw [J_apply, e₀_coords.1, e₀_coords.2]; simp

/-- Pin `J e₁ = -e₀`. -/
example : J e₁ = -e₀ := by
  rw [J_apply, e₁_coords.1, e₁_coords.2]; simp

/-- Pin: `J` is skew-adjoint. -/
theorem J_skew (u w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (J u) w + inner ℝ u (J w) = 0 := by
  have he0L := fun v : EuclideanSpace ℝ (Fin 2) => (basis_inner_left v).1
  have he1L := fun v : EuclideanSpace ℝ (Fin 2) => (basis_inner_left v).2
  have he0R : ∀ v : EuclideanSpace ℝ (Fin 2), inner ℝ v e₀ = v.ofLp 0 := by
    intro v; rw [real_inner_comm]; exact he0L v
  have he1R : ∀ v : EuclideanSpace ℝ (Fin 2), inner ℝ v e₁ = v.ofLp 1 := by
    intro v; rw [real_inner_comm]; exact he1L v
  rw [J_apply u, J_apply w]
  simp [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    he0L, he1L, he0R, he1R]; ring

/-- Pin `Shear e₁ = e₀`. -/
theorem Shear_e1 : Shear e₁ = e₀ := by
  unfold Shear
  simp only [ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj,
    e₁_coords.2, one_smul]

/-- Pin `Shear e₀ = 0`. -/
theorem Shear_e0 : Shear e₀ = 0 := by
  unfold Shear
  simp only [ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj,
    e₀_coords.2, zero_smul]

/-- Translation by `e₀` is Killing. -/
theorem trans_killing : Manifold.IsKillingVectorField (𝓡 2)
    (fun y : EuclideanSpace ℝ (Fin 2) => show TangentSpace (𝓡 2) y from e₀) :=
  Manifold.isKillingVectorField_const e₀

/-- Translation takes a nonzero value. -/
example : (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from e₀) e₀ ≠ 0 := basis_ne_zero.1

/-- Translation is nonzero in `killingVectorFields`. -/
example : (⟨_, trans_killing⟩ :
    Manifold.killingVectorFields (𝓡 2) (EuclideanSpace ℝ (Fin 2))) ≠ 0 := by
  intro h0
  have h1 : (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from e₀) = 0 := congrArg Subtype.val h0
  have h2 := congrFun h1 e₀; simp only [Pi.zero_apply] at h2
  exact basis_ne_zero.1 h2

/-- Rotation field is Killing. -/
theorem rot_killing : Manifold.IsKillingVectorField (𝓡 2)
    (fun y : EuclideanSpace ℝ (Fin 2) => show TangentSpace (𝓡 2) y from J y) :=
  (Manifold.isKillingVectorField_continuousLinearMap_iff J).mpr J_skew

/-- Rotation is not constant. -/
example : (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from J y) 0 ≠
    (fun y : EuclideanSpace ℝ (Fin 2) =>
      show TangentSpace (𝓡 2) y from J y) e₀ := by
  have hJe : J e₀ = e₁ := by
    rw [J_apply, e₀_coords.1, e₀_coords.2]; simp
  have h0 : J (0 : EuclideanSpace ℝ (Fin 2)) = 0 := map_zero J
  have hne : J (0 : EuclideanSpace ℝ (Fin 2)) ≠ J e₀ := by
    rw [h0, hJe]; exact Ne.symm basis_ne_zero.2
  exact hne

/-- Rotation is nonzero in `killingVectorFields`. -/
example : (⟨_, rot_killing⟩ :
    Manifold.killingVectorFields (𝓡 2) (EuclideanSpace ℝ (Fin 2))) ≠ 0 := by
  intro h0
  have h1 : (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from J y) = 0 := congrArg Subtype.val h0
  have h2 := congrFun h1 e₀
  have hJe : J e₀ = e₁ := by
    rw [J_apply, e₀_coords.1, e₀_coords.2]; simp
  have hEq : J e₀ = (0 : EuclideanSpace ℝ (Fin 2)) := h2
  rw [hJe] at hEq; exact basis_ne_zero.2 hEq

/-- Covariant derivative of rotation at `e₀` is `e₁`. -/
example : CovariantDerivative.leviCivitaConnection (𝓡 2)
    (EuclideanSpace ℝ (Fin 2))
    (fun y : EuclideanSpace ℝ (Fin 2) => show TangentSpace (𝓡 2) y from J y)
    e₀ e₀ = e₁ := by
  have hCont : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from J y) := J.contDiff
  have hSmooth : CMDiff ∞ (T% (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from J y)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hCont
  have hX : MDiffAt (T% (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from J y)) e₀ :=
    hSmooth.mdifferentiableAt (by simp)
  have hConn := CovariantDerivative.leviCivitaConnection_vectorSpace_apply hX e₀
  have hDer : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from J y) e₀ = J := ContinuousLinearMap.fderiv J
  have hJe : J e₀ = e₁ := by
    rw [J_apply, e₀_coords.1, e₀_coords.2]; simp
  rw [hConn, hDer] at *; show J e₀ = e₁; exact hJe

/-- Dilation is smooth. -/
example : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from y) := contDiff_id

/-- Dilation is nonzero at `e₀`. -/
example : (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from y) e₀ ≠ 0 := basis_ne_zero.1

/-- Killing expression of dilation equals `2`. -/
example : inner ℝ (CovariantDerivative.leviCivitaConnection (𝓡 2)
      (EuclideanSpace ℝ (Fin 2))
      (fun y : EuclideanSpace ℝ (Fin 2) => show TangentSpace (𝓡 2) y from y)
      e₀ e₀) e₀ + inner ℝ e₀ (CovariantDerivative.leviCivitaConnection (𝓡 2)
      (EuclideanSpace ℝ (Fin 2))
      (fun y : EuclideanSpace ℝ (Fin 2) => show TangentSpace (𝓡 2) y from y)
      e₀ e₀) = 2 := by
  have hSmooth : CMDiff ∞ (T% (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from y)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_id
  have hX : MDiffAt (T% (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from y)) e₀ :=
    hSmooth.mdifferentiableAt (by simp)
  have hConn := CovariantDerivative.leviCivitaConnection_vectorSpace_apply hX e₀
  have hDer : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from y) e₀ =
    ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) :=
    ContinuousLinearMap.fderiv (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))
  have hPlain : inner ℝ ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) e₀)
      e₀ + inner ℝ e₀ ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) e₀)
      = (2 : ℝ) := by
    simp only [ContinuousLinearMap.id_apply, basis_gram.1]; norm_num
  rw [hConn, hDer]; exact hPlain

/-- Dilation is not Killing. -/
example : ¬ Manifold.IsKillingVectorField (𝓡 2)
    (fun y : EuclideanSpace ℝ (Fin 2) => show TangentSpace (𝓡 2) y from y) := by
  intro hK
  have hS := (Manifold.isKillingVectorField_vectorSpace_iff).mp hK
  have hEq := hS.2 e₀ e₀ e₀
  have hDer : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from y) e₀ =
    ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) :=
    ContinuousLinearMap.fderiv (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))
  rw [hDer] at hEq
  have hP : inner ℝ ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) e₀)
      e₀ + inner ℝ e₀ ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) e₀)
      = (0 : ℝ) := hEq
  simp only [ContinuousLinearMap.id_apply, basis_gram.1] at hP
  norm_num at hP

/-- Dilation is not in `killingVectorFields`. -/
example : (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from y) ∉
    Manifold.killingVectorFields (𝓡 2) (EuclideanSpace ℝ (Fin 2)) := by
  intro hMem
  have hK : Manifold.IsKillingVectorField (𝓡 2) (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from y) :=
    (Manifold.mem_killingVectorFields (𝓡 2) (EuclideanSpace ℝ (Fin 2))).mp hMem
  have hS := (Manifold.isKillingVectorField_vectorSpace_iff).mp hK
  have hEq := hS.2 e₀ e₀ e₀
  have hDer : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from y) e₀ =
    ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) :=
    ContinuousLinearMap.fderiv (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))
  rw [hDer] at hEq
  have hP : inner ℝ ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) e₀)
      e₀ + inner ℝ e₀ ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) e₀)
      = (0 : ℝ) := hEq
  simp only [ContinuousLinearMap.id_apply, basis_gram.1] at hP
  norm_num at hP

/-- Shear is smooth. -/
example : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from Shear y) := Shear.contDiff

/-- Shear is nonzero at `e₁`. -/
example : (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from Shear y) e₁ ≠ 0 := by
  have hEq : (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from Shear y) e₁ = e₀ := Shear_e1
  rw [hEq]; exact basis_ne_zero.1

/-- Killing expression of shear equals `1`. -/
example : inner ℝ (CovariantDerivative.leviCivitaConnection (𝓡 2)
      (EuclideanSpace ℝ (Fin 2))
      (fun y : EuclideanSpace ℝ (Fin 2) => show TangentSpace (𝓡 2) y from Shear y)
      e₀ e₁) e₀ + inner ℝ e₁ (CovariantDerivative.leviCivitaConnection (𝓡 2)
      (EuclideanSpace ℝ (Fin 2))
      (fun y : EuclideanSpace ℝ (Fin 2) => show TangentSpace (𝓡 2) y from Shear y)
      e₀ e₀) = 1 := by
  have hSmooth : CMDiff ∞ (T% (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from Shear y)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr Shear.contDiff
  have hX : MDiffAt (T% (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from Shear y)) e₀ :=
    hSmooth.mdifferentiableAt (by simp)
  have hC1 := CovariantDerivative.leviCivitaConnection_vectorSpace_apply hX e₁
  have hC0 := CovariantDerivative.leviCivitaConnection_vectorSpace_apply hX e₀
  have hDer : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from Shear y) e₀ = Shear :=
    ContinuousLinearMap.fderiv Shear
  have hPlain : inner ℝ e₀ e₀ + inner ℝ e₁ (0 : EuclideanSpace ℝ (Fin 2))
      = (1 : ℝ) := by
    simp only [basis_gram.1, inner_zero_right, add_zero]
  rw [hC1, hC0, hDer, Shear_e1, Shear_e0]; exact hPlain

/-- Shear is not Killing. -/
example : ¬ Manifold.IsKillingVectorField (𝓡 2)
    (fun y : EuclideanSpace ℝ (Fin 2) =>
      show TangentSpace (𝓡 2) y from Shear y) := by
  intro hK
  have hS := (Manifold.isKillingVectorField_vectorSpace_iff).mp hK
  have hEq := hS.2 e₀ e₁ e₀
  have hDer : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
    show TangentSpace (𝓡 2) y from Shear y) e₀ = Shear :=
    ContinuousLinearMap.fderiv Shear
  rw [hDer, Shear_e1, Shear_e0] at hEq
  have hP : inner ℝ e₀ e₀ + inner ℝ e₁ (0 : EuclideanSpace ℝ (Fin 2))
      = (0 : ℝ) := hEq
  simp only [basis_gram.1, inner_zero_right, add_zero] at hP
  exact one_ne_zero hP

/-- Killing fields agreeing everywhere are equal. -/
example (a b : Manifold.killingVectorFields (𝓡 2) (EuclideanSpace ℝ (Fin 2)))
    (h : ∀ x : EuclideanSpace ℝ (Fin 2),
      (a : Π x : EuclideanSpace ℝ (Fin 2), TangentSpace (𝓡 2) x) x =
      (b : Π x : EuclideanSpace ℝ (Fin 2), TangentSpace (𝓡 2) x) x) :
    a = b :=
  Manifold.killingVectorFields.ext (𝓡 2) (EuclideanSpace ℝ (Fin 2)) h

/-- Sum of translation and rotation has value `e₀` at `0`. -/
example : (⟨_, Manifold.IsKillingVectorField.add (𝓡 2)
      trans_killing rot_killing⟩ :
    Manifold.killingVectorFields (𝓡 2) (EuclideanSpace ℝ (Fin 2))).val 0 = e₀ := by
  show e₀ + J (0 : EuclideanSpace ℝ (Fin 2)) = e₀; simp

/-- General pointwise lemma for a Killing field. -/
example {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    {X : (x : M) → TangentSpace I x}
    (hX : Manifold.IsKillingVectorField I X) (x : M) (u : TangentSpace I x) :
    inner ℝ (CovariantDerivative.leviCivitaConnection I M X x u) u = 0 :=
  Manifold.IsKillingVectorField.inner_leviCivitaConnection_self I hX x u

/-- General `L_X g = 0` characterization. -/
example {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    {X : (x : M) → TangentSpace I x}
    (hX : Manifold.IsKillingVectorField I X) (x : M)
    (Y Z : (x : M) → TangentSpace I x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    ((d% fun y => inner ℝ (Y y) (Z y)) x) (X x) -
      inner ℝ (VectorField.mlieBracket I X Y x) (Z x) -
      inner ℝ (Y x) (VectorField.mlieBracket I X Z x) = 0 :=
  (Manifold.isKillingVectorField_iff_mvfderiv_inner I).mp hX |>.2 x Y Z hY hZ

end KillingPlaneTests
