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

public import MathlibExt.Analysis.CStarAlgebra.Grading.Module
public import MathlibExt.Analysis.CStarAlgebra.Module.DirectSum.Completion

/-!
# Gradings on completed Hilbert-module direct sums

A family of graded complete right modules induces the coordinatewise grading
on the literal finite-support sum and hence on its stock completion.  The
construction works for arbitrary, including empty, index types.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Topology
open scoped RightActions

namespace CStarModule.DirectSum

universe uB uI uE

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {gamma : CStarGrading B}
variable {I : Type uI} {E : I → Type uE}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
variable [∀ i, SMul Bᵐᵒᵖ (E i)] [∀ i, CStarModule Bᵐᵒᵖ (E i)]
variable [∀ i, CompleteSpace (E i)]

private def algebraicGeneratorLinearEquiv
    (delta : ∀ i, CStarModuleGrading gamma (E i)) :
    Algebraic B E ≃ₗ[ℂ] Algebraic B E :=
  (toDFinsupp (B := B) (E := E)).trans <|
    (DFinsupp.mapRange.linearEquiv fun i ↦
      (delta i).generator.toLinearEquiv).trans
        (toDFinsupp (B := B) (E := E)).symm

omit [StarOrderedRing Bᵐᵒᵖ] in
private theorem toDFinsupp_algebraicGeneratorLinearEquiv
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (x : Algebraic B E) (i : I) :
    toDFinsupp (algebraicGeneratorLinearEquiv delta x) i =
      (delta i).generator (toDFinsupp x i) :=
  rfl

omit [StarOrderedRing Bᵐᵒᵖ] in
private theorem support_algebraicGeneratorLinearEquiv
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (x : Algebraic B E) :
    support (algebraicGeneratorLinearEquiv delta x) = support x := by
  classical
  ext i
  rw [mem_support_iff, mem_support_iff,
    toDFinsupp_algebraicGeneratorLinearEquiv]
  constructor
  · intro h hx
    apply h
    simp [hx]
  · intro h hx
    apply h
    exact (delta i).generator.injective (by simpa using hx)

omit [StarOrderedRing Bᵐᵒᵖ] in
private theorem algebraicInner_generator
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (x y : Algebraic B E) :
    algebraicInner (algebraicGeneratorLinearEquiv delta x)
        (algebraicGeneratorLinearEquiv delta y) =
      MulOpposite.op
        (gamma.generatorAut (MulOpposite.unop (algebraicInner x y))) := by
  classical
  rw [algebraicInner_eq_sum, algebraicInner_eq_sum,
    support_algebraicGeneratorLinearEquiv]
  apply MulOpposite.unop_injective
  simp only [Finset.unop_sum, map_sum, MulOpposite.unop_op,
    toDFinsupp_algebraicGeneratorLinearEquiv]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [rightInner] using
    (delta i).generator_rightInner (toDFinsupp x i) (toDFinsupp y i)

/-- Coordinatewise grading generator on the algebraic finite-support sum. -/
@[no_expose]
def algebraicGenerator
    (delta : ∀ i, CStarModuleGrading gamma (E i)) :
    Algebraic B E ≃ₗᵢ[ℂ] Algebraic B E where
  toLinearEquiv := algebraicGeneratorLinearEquiv delta
  norm_map' x := by
    rw [norm_algebraic, norm_algebraic,
      algebraicInner_generator delta x x]
    simp only [MulOpposite.norm_unop, MulOpposite.norm_op,
      StarAlgEquiv.norm_map]

private theorem algebraicGenerator_apply
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (x : Algebraic B E) :
    algebraicGenerator delta x = algebraicGeneratorLinearEquiv delta x :=
  rfl

theorem algebraicGenerator_single
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (i : I) (x : E i) :
    algebraicGenerator delta (single (B := B) (E := E) i x) =
      single (B := B) (E := E) i ((delta i).generator x) := by
  change algebraicGeneratorLinearEquiv delta
      (single (B := B) (E := E) i x) = _
  apply (toDFinsupp (B := B) (E := E)).injective
  ext j
  by_cases hji : j = i
  · subst j
    simp only [toDFinsupp_algebraicGeneratorLinearEquiv,
      single_apply_same]
  · simp only [toDFinsupp_algebraicGeneratorLinearEquiv,
      single_apply_ne hji, map_zero]

/-- Canonical simp-normal form of coordinatewise generation on an algebraic
single-coordinate vector. -/
@[simp]
theorem algebraicGenerator_singleLinear
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (i : I) (x : E i) :
    algebraicGenerator delta (singleLinear (B := B) (E := E) i x) =
      singleLinear (B := B) (E := E) i ((delta i).generator x) := by
  simpa only [single_apply_eq_singleLinear] using
    algebraicGenerator_single delta i x

private def completedGeneratorCLM
    (delta : ∀ i, CStarModuleGrading gamma (E i)) :
    Completed B E →L[ℂ] Completed B E :=
  ((algebraicInclusion (B := B) (E := E)).toContinuousLinearMap.comp
    (algebraicGenerator delta).toLinearIsometry.toContinuousLinearMap).fromCompletion

@[simp]
private theorem completedGeneratorCLM_coe
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (x : Algebraic B E) :
    completedGeneratorCLM delta (x : Completed B E) =
      (algebraicGenerator delta x : Completed B E) := by
  rw [completedGeneratorCLM,
    ContinuousLinearMap.fromCompletion_apply_coe,
    ContinuousLinearMap.comp_apply]
  change algebraicInclusion (algebraicGenerator delta x) = _
  rw [algebraicInclusion_apply]

private theorem norm_completedGeneratorCLM
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (x : Completed B E) :
    ‖completedGeneratorCLM delta x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq
      (continuous_norm.comp (completedGeneratorCLM delta).continuous)
      continuous_norm) ?_
  intro y
  rw [completedGeneratorCLM_coe,
    UniformSpace.Completion.norm_coe,
    UniformSpace.Completion.norm_coe]
  exact (algebraicGenerator delta).norm_map y

private def completedGeneratorIsometry
    (delta : ∀ i, CStarModuleGrading gamma (E i)) :
    Completed B E →ₗᵢ[ℂ] Completed B E where
  toLinearMap := (completedGeneratorCLM delta).toLinearMap
  norm_map' := norm_completedGeneratorCLM delta

@[simp]
private theorem completedGeneratorIsometry_coe
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (x : Algebraic B E) :
    completedGeneratorIsometry delta (x : Completed B E) =
      (algebraicGenerator delta x : Completed B E) := by
  change completedGeneratorCLM delta (x : Completed B E) = _
  rw [completedGeneratorCLM_coe]

private theorem completedGeneratorIsometry_involutive
    (delta : ∀ i, CStarModuleGrading gamma (E i)) :
    Function.Involutive (completedGeneratorIsometry delta) := by
  intro x
  let G := completedGeneratorIsometry delta
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (G.continuous.comp G.continuous) continuous_id) ?_
  intro y
  simp only [completedGeneratorIsometry_coe]
  simp only [algebraicGenerator_apply]
  apply congrArg (fun z : Algebraic B E => (z : Completed B E))
  apply (toDFinsupp (B := B) (E := E)).injective
  ext i
  rw [toDFinsupp_algebraicGeneratorLinearEquiv,
    toDFinsupp_algebraicGeneratorLinearEquiv]
  exact (delta i).generator_involutive (toDFinsupp y i)

/-- Coordinatewise grading generator on the completed direct sum. -/
@[no_expose]
def completedGenerator
    (delta : ∀ i, CStarModuleGrading gamma (E i)) :
    Completed B E ≃L[ℂ] Completed B E where
  toFun := completedGeneratorIsometry delta
  invFun := completedGeneratorIsometry delta
  left_inv := completedGeneratorIsometry_involutive delta
  right_inv := completedGeneratorIsometry_involutive delta
  map_add' := map_add (completedGeneratorIsometry delta)
  map_smul' := map_smul (completedGeneratorIsometry delta)
  continuous_toFun := (completedGeneratorIsometry delta).continuous
  continuous_invFun := (completedGeneratorIsometry delta).continuous

private theorem completedGenerator_apply
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (x : Completed B E) :
    completedGenerator delta x = completedGeneratorIsometry delta x :=
  rfl

theorem completedGenerator_single
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (i : I) (x : E i) :
    completedGenerator delta (completedSingle (B := B) (E := E) i x) =
      completedSingle (B := B) (E := E) i ((delta i).generator x) := by
  rw [completedSingle_apply, completedSingle_apply]
  change completedGeneratorIsometry delta
      ((single (B := B) (E := E) i x : Algebraic B E) : Completed B E) = _
  rw [completedGeneratorIsometry_coe, algebraicGenerator_single]

/-- Canonical simp-normal form of the completed generator on an embedded
algebraic single-coordinate vector. -/
@[simp]
theorem completedGenerator_singleLinear
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (i : I) (x : E i) :
    completedGenerator delta
        ((singleLinear (B := B) (E := E) i x : Algebraic B E) : Completed B E) =
      ((singleLinear (B := B) (E := E) i ((delta i).generator x) :
        Algebraic B E) : Completed B E) := by
  change completedGeneratorIsometry delta
      ((singleLinear (B := B) (E := E) i x : Algebraic B E) : Completed B E) = _
  rw [completedGeneratorIsometry_coe, algebraicGenerator_singleLinear]

/-- The completed direct sum carries the coordinatewise module grading. -/
@[no_expose]
def grading
    (delta : ∀ i, CStarModuleGrading gamma (E i)) :
    CStarModuleGrading gamma (Completed B E) where
  generator := completedGenerator delta
  generator_involutive := completedGeneratorIsometry_involutive delta
  generator_right_smul := by
    intro x b
    let G := completedGenerator delta
    have hl : Continuous fun z : Completed B E => G (z <• b) :=
      G.continuous.comp (CStarModule.continuous_right_smul_const b)
    have hr : Continuous fun z : Completed B E => G z <• gamma.generatorAut b :=
      (CStarModule.continuous_right_smul_const (gamma.generatorAut b)).comp
        G.continuous
    refine UniformSpace.Completion.induction_on x (isClosed_eq hl hr) ?_
    intro y
    simp only [completedGenerator_apply]
    change completedGeneratorIsometry delta
        (((y : Algebraic B E) : Completed B E) <• b) =
      completedGeneratorIsometry delta (y : Completed B E) <•
        gamma.generatorAut b
    rw [← CStarModule.coe_completion_coeff_smul
        (A := Bᵐᵒᵖ) (E := Algebraic B E),
      completedGeneratorIsometry_coe, completedGeneratorIsometry_coe,
      ← CStarModule.coe_completion_coeff_smul
        (A := Bᵐᵒᵖ) (E := Algebraic B E)]
    apply congrArg (fun z : Algebraic B E => (z : Completed B E))
    change algebraicGeneratorLinearEquiv delta (y <• b) =
      algebraicGeneratorLinearEquiv delta y <• gamma.generatorAut b
    apply (toDFinsupp (B := B) (E := E)).injective
    ext i
    rw [toDFinsupp_algebraicGeneratorLinearEquiv,
      toDFinsupp_right_smul, (delta i).generator_right_smul,
      toDFinsupp_right_smul,
      toDFinsupp_algebraicGeneratorLinearEquiv]
  generator_rightInner := by
    intro x y
    let G := completedGenerator delta
    have hl : Continuous fun p : Completed B E × Completed B E =>
        CStarModule.rightInner (B := B) (G p.1) (G p.2) :=
      CStarModule.continuous_rightInner.comp
        ((G.continuous.comp continuous_fst).prodMk
          (G.continuous.comp continuous_snd))
    have hr : Continuous fun p : Completed B E × Completed B E =>
        gamma.generatorAut (CStarModule.rightInner (B := B) p.1 p.2) :=
      (StarAlgEquiv.isometry gamma.generatorAut).continuous.comp
        CStarModule.continuous_rightInner
    refine UniformSpace.Completion.induction_on₂ x y (isClosed_eq hl hr) ?_
    intro a b
    simp only [completedGenerator_apply]
    change CStarModule.rightInner (B := B)
        (completedGeneratorIsometry delta (a : Completed B E))
        (completedGeneratorIsometry delta (b : Completed B E)) =
      gamma.generatorAut
        (CStarModule.rightInner (B := B)
          (a : Completed B E) (b : Completed B E))
    rw [completedGeneratorIsometry_coe,
      completedGeneratorIsometry_coe]
    simp only [CStarModule.rightInner,
      CStarModule.completionCStarModule_inner_coe_coe,
      inner_eq_algebraicInner]
    simp only [algebraicGenerator_apply]
    rw [algebraicInner_generator]
    rfl

private theorem grading_generator
    (delta : ∀ i, CStarModuleGrading gamma (E i)) :
    (grading delta).generator = completedGenerator delta :=
  rfl

theorem grading_generator_completedSingle
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (i : I) (x : E i) :
    (grading delta).generator (completedSingle (B := B) (E := E) i x) =
      completedSingle (B := B) (E := E) i ((delta i).generator x) :=
  by
    rw [grading_generator, completedGenerator_single]

/-- Canonical simp-normal form of the completed direct-sum grading on an
embedded algebraic single-coordinate vector. -/
@[simp]
theorem grading_generator_singleLinear
    (delta : ∀ i, CStarModuleGrading gamma (E i))
    (i : I) (x : E i) :
    (grading delta).generator
        ((singleLinear (B := B) (E := E) i x : Algebraic B E) : Completed B E) =
      ((singleLinear (B := B) (E := E) i ((delta i).generator x) :
        Algebraic B E) : Completed B E) := by
  rw [grading_generator, completedGenerator_singleLinear]

end CStarModule.DirectSum
