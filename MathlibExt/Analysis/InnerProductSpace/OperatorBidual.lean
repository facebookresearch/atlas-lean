/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# The canonical retraction from the bidual of the operator space

For a complex Hilbert space `H`, this file constructs the canonical contraction

`(H →L[ℂ] H)** →L[ℂ] (H →L[ℂ] H)`

by testing a bidual element on the weak-operator coefficient functionals
`T ↦ ⟪h, T g⟫_ℂ`.  The construction is valid for the zero Hilbert space and
introduces no topology or global instance.
-/

@[expose] public section

open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private noncomputable def operatorCoefficientBilin :
    H →L⋆[ℂ] H →L[ℂ] StrongDual ℂ (H →L[ℂ] H) :=
  ContinuousLinearMap.bilinearComp
    (ContinuousLinearMap.compL ℂ (H →L[ℂ] H) H ℂ)
    (innerSL ℂ) (ContinuousLinearMap.apply ℂ H)

/-- Let `H` be a complex normed inner-product space. The operator space is `H →L[ℂ] H`, and its
continuous dual and double dual have their operator norms.

The weak-operator coefficient functional `T ↦ ⟪h, T g⟫_ℂ`. -/
@[no_expose]
noncomputable def operatorCoefficient (g h : H) : StrongDual ℂ (H →L[ℂ] H) :=
  operatorCoefficientBilin h g

@[simp]
theorem operatorCoefficient_apply (g h : H) (T : H →L[ℂ] H) :
    operatorCoefficient g h T = ⟪h, T g⟫_ℂ :=
  by simp [operatorCoefficient, operatorCoefficientBilin]

@[simp]
theorem operatorCoefficient_add_left (g₁ g₂ h : H) :
    operatorCoefficient (g₁ + g₂) h =
      operatorCoefficient g₁ h + operatorCoefficient g₂ h := by
  simp [operatorCoefficient]

@[simp]
theorem operatorCoefficient_smul_left (c : ℂ) (g h : H) :
    operatorCoefficient (c • g) h = c • operatorCoefficient g h := by
  simp [operatorCoefficient]

@[simp]
theorem operatorCoefficient_add_right (g h₁ h₂ : H) :
    operatorCoefficient g (h₁ + h₂) =
      operatorCoefficient g h₁ + operatorCoefficient g h₂ := by
  simp [operatorCoefficient]

@[simp]
theorem operatorCoefficient_smul_right (c : ℂ) (g h : H) :
    operatorCoefficient g (c • h) = star c • operatorCoefficient g h := by
  simp [operatorCoefficient]

/-- Let `H` be a complex normed inner-product space. The operator space is `H →L[ℂ] H`, and its
continuous dual and double dual have their operator norms.

The norm of a coefficient functional is bounded by the product of the norms of its two vectors. -/
theorem norm_operatorCoefficient_le (g h : H) :
    ‖operatorCoefficient g h‖ ≤ ‖g‖ * ‖h‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg g) (norm_nonneg h))
  intro T
  calc
    ‖operatorCoefficient g h T‖ = ‖⟪h, T g⟫_ℂ‖ := by
      rw [operatorCoefficient_apply]
    _ ≤ ‖h‖ * ‖T g‖ := norm_inner_le_norm _ _
    _ ≤ ‖h‖ * (‖T‖ * ‖g‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm g) (norm_nonneg h)
    _ = (‖g‖ * ‖h‖) * ‖T‖ := by ring

private noncomputable def operatorBidualForm
    (Φ : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) :
    H →L⋆[ℂ] H →L[ℂ] ℂ :=
  ((ContinuousLinearMap.compL ℂ H (StrongDual ℂ (H →L[ℂ] H)) ℂ) Φ).comp
    operatorCoefficientBilin

@[simp]
private theorem operatorBidualForm_apply
    (Φ : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) (h g : H) :
    operatorBidualForm Φ h g = Φ (operatorCoefficient g h) := by
  simp [operatorBidualForm, operatorCoefficient, operatorCoefficientBilin]

variable [CompleteSpace H]

local instance operatorDoubleDualNorm :
    Norm (StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) :=
  ContinuousLinearMap.hasOpNorm (E := StrongDual ℂ (H →L[ℂ] H)) (F := ℂ)
    (σ₁₂ := RingHom.id ℂ)

local instance operatorDoubleDualSeminormedAddCommGroup :
    SeminormedAddCommGroup (StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
    (E := StrongDual ℂ (H →L[ℂ] H)) (F := ℂ) (σ₁₂ := RingHom.id ℂ)

local instance operatorDoubleDualNormedSpace :
    NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) :=
  ContinuousLinearMap.toNormedSpace
    (E := StrongDual ℂ (H →L[ℂ] H)) (F := ℂ) (σ₁₂ := RingHom.id ℂ)

/-- Let `H` be a complex normed inner-product space. The operator space is `H →L[ℂ] H`, and its
continuous dual and double dual have their operator norms.

The canonical operator norm on the double strong dual of `B(H)`, exposed without installing a
global instance on the nested dual carrier. -/
noncomputable def operatorDoubleDualOpNorm
    (Φ : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) : ℝ :=
  ContinuousLinearMap.opNorm (E := StrongDual ℂ (H →L[ℂ] H)) (F := ℂ)
    (σ₁₂ := RingHom.id ℂ) Φ

omit [CompleteSpace H] in
private theorem operatorDoubleDualOpNorm_eq_norm
    (Φ : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) :
    operatorDoubleDualOpNorm Φ = ‖Φ‖ :=
  rfl

omit [CompleteSpace H] in
theorem operatorDoubleDualOpNorm_nonneg
    (Φ : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) :
    0 ≤ operatorDoubleDualOpNorm Φ :=
  ContinuousLinearMap.opNorm_nonneg
    (E := StrongDual ℂ (H →L[ℂ] H)) (F := ℂ) (σ₁₂ := RingHom.id ℂ) Φ

private noncomputable def operatorBidualRetractionAux
    (Φ : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) : H →L[ℂ] H :=
  ContinuousLinearMap.adjoint
    (InnerProductSpace.continuousLinearMapOfBilin (operatorBidualForm Φ))

@[simp]
private theorem operatorBidualRetractionAux_inner
    (Φ : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) (g h : H) :
    ⟪h, operatorBidualRetractionAux Φ g⟫_ℂ = Φ (operatorCoefficient g h) := by
  calc
    ⟪h, operatorBidualRetractionAux Φ g⟫_ℂ =
        ⟪InnerProductSpace.continuousLinearMapOfBilin (operatorBidualForm Φ) h, g⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = operatorBidualForm Φ h g :=
      InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _
    _ = Φ (operatorCoefficient g h) := operatorBidualForm_apply Φ h g

private theorem norm_operatorBidualRetractionAux_apply_le
    (Φ : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) (g : H) :
    ‖operatorBidualRetractionAux Φ g‖ ≤ operatorDoubleDualOpNorm Φ * ‖g‖ := by
  rw [← innerSL_apply_norm ℂ (operatorBidualRetractionAux Φ g)]
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (operatorDoubleDualOpNorm_nonneg Φ) (norm_nonneg g))
  intro h
  calc
    ‖innerSL ℂ (operatorBidualRetractionAux Φ g) h‖ =
        ‖⟪h, operatorBidualRetractionAux Φ g⟫_ℂ‖ := by
      rw [innerSL_apply_apply, norm_inner_symm]
    _ = ‖Φ (operatorCoefficient g h)‖ := by rw [operatorBidualRetractionAux_inner]
    _ ≤ operatorDoubleDualOpNorm Φ * ‖operatorCoefficient g h‖ := by
      exact ContinuousLinearMap.le_opNorm
        (E := StrongDual ℂ (H →L[ℂ] H)) (F := ℂ) (σ₁₂ := RingHom.id ℂ) Φ _
    _ ≤ operatorDoubleDualOpNorm Φ * (‖g‖ * ‖h‖) :=
      mul_le_mul_of_nonneg_left (norm_operatorCoefficient_le g h)
        (operatorDoubleDualOpNorm_nonneg Φ)
    _ = (operatorDoubleDualOpNorm Φ * ‖g‖) * ‖h‖ := by ring

private theorem norm_operatorBidualRetractionAux_le
    (Φ : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) :
    ‖operatorBidualRetractionAux Φ‖ ≤ operatorDoubleDualOpNorm Φ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (operatorDoubleDualOpNorm_nonneg Φ)
  exact norm_operatorBidualRetractionAux_apply_le Φ

private noncomputable def operatorBidualRetractionLinear :
    StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H)) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun := operatorBidualRetractionAux
  map_add' := by
    intro Φ Ψ
    apply ContinuousLinearMap.ext
    intro g
    apply ext_inner_left ℂ
    intro h
    simp only [operatorBidualRetractionAux_inner, add_apply,
      inner_add_right]
  map_smul' := by
    intro c Φ
    apply ContinuousLinearMap.ext
    intro g
    apply ext_inner_left ℂ
    intro h
    simp only [operatorBidualRetractionAux_inner, smul_apply, inner_smul_right,
      smul_eq_mul, RingHom.id_apply]

@[simp]
private theorem operatorBidualRetractionLinear_apply
    (Φ : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) :
    operatorBidualRetractionLinear Φ = operatorBidualRetractionAux Φ :=
  rfl

/-- Let `H` be a complex normed inner-product space. The operator space is `H →L[ℂ] H`, and its
continuous dual and double dual have their operator norms. Assume `H` is complete.

The canonical contraction from the bidual of `B(H)` onto `B(H)`, characterized by weak-operator
coefficients. -/
@[no_expose]
noncomputable def operatorBidualRetraction :
    StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H)) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous (operatorBidualRetractionLinear (H := H)) 1 fun Φ => by
    simpa only [operatorBidualRetractionLinear_apply, one_mul,
      operatorDoubleDualOpNorm_eq_norm] using
      norm_operatorBidualRetractionAux_le (H := H) Φ

/-- Let `H` be a complex normed inner-product space. The operator space is `H →L[ℂ] H`, and its
continuous dual and double dual have their operator norms. Assume `H` is complete.

Characteristic coefficient identity for the operator-bidual retraction. -/
@[simp]
theorem operatorBidualRetraction_inner
    (Φ : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) (g h : H) :
    ⟪h, operatorBidualRetraction Φ g⟫_ℂ = Φ (operatorCoefficient g h) := by
  simpa only [operatorBidualRetraction, LinearMap.mkContinuous_apply,
    operatorBidualRetractionLinear_apply, operatorDoubleDualOpNorm_eq_norm] using
    operatorBidualRetractionAux_inner Φ g h

/-- Let `H` be a complex normed inner-product space. The operator space is `H →L[ℂ] H`, and its
continuous dual and double dual have their operator norms. Assume `H` is complete.

Pointwise contraction of the operator-bidual retraction. -/
theorem norm_operatorBidualRetraction_apply_le
    (Φ : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H))) :
    ‖operatorBidualRetraction Φ‖ ≤ operatorDoubleDualOpNorm Φ := by
  simpa only [operatorBidualRetraction, LinearMap.mkContinuous_apply,
    operatorBidualRetractionLinear_apply] using
    norm_operatorBidualRetractionAux_le Φ

/-- Let `H` be a complex normed inner-product space. The operator space is `H →L[ℂ] H`, and its
continuous dual and double dual have their operator norms. Assume `H` is complete.

The canonical operator norm of the operator-bidual retraction, exposed without installing a
global norm instance on the nested dual carrier. -/
@[no_expose]
noncomputable def operatorBidualRetractionOpNorm (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : ℝ :=
  ‖operatorBidualRetraction (H := H)‖

/-- Let `H` be a complex normed inner-product space. The operator space is `H →L[ℂ] H`, and its
continuous dual and double dual have their operator norms. Assume `H` is complete.

The operator norm of the canonical retraction is at most one. -/
theorem operatorBidualRetractionOpNorm_le :
    operatorBidualRetractionOpNorm H ≤ 1 :=
  LinearMap.mkContinuous_norm_le (operatorBidualRetractionLinear (H := H)) zero_le_one fun Φ => by
    simpa only [operatorBidualRetractionLinear_apply, one_mul,
      operatorDoubleDualOpNorm_eq_norm] using
      norm_operatorBidualRetractionAux_le (H := H) Φ

/-- Let `H` be a complex normed inner-product space. The operator space is `H →L[ℂ] H`, and its
continuous dual and double dual have their operator norms. Assume `H` is complete.

The canonical map is a left inverse to the inclusion into the double dual. -/
@[simp]
theorem operatorBidualRetraction_inclusionInDoubleDual (T : H →L[ℂ] H) :
    operatorBidualRetraction
        (NormedSpace.inclusionInDoubleDual ℂ (H →L[ℂ] H) T) = T := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro h
  rw [operatorBidualRetraction_inner]
  rw [NormedSpace.dual_def, operatorCoefficient_apply]

end

end MathlibExt.Analysis.InnerProductSpace
