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
public import MathlibExt.Analysis.CStarAlgebra.Module.Standard

/-!
# The coordinatewise grading of the standard C-star module

An explicit coefficient grading acts coordinatewise on finite-support
standard-module vectors. The action is isometric, so it extends uniquely to
the completed standard module. This file proves the coordinate, right-action,
and coefficient-valued inner-product formulas for that extension.
-/

@[expose] public section

noncomputable section

open Set
open scoped RightActions

universe uB uι

namespace CStarModuleGrading

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable {ι : Type uι}

local instance coefficientSpectralOrder : PartialOrder Bᵐᵒᵖ :=
  CStarAlgebra.spectralOrder Bᵐᵒᵖ

local instance coefficientSpectralOrderedRing : StarOrderedRing Bᵐᵒᵖ :=
  CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ

/-- **Grading generator on finitely supported standard vectors.** Let `B` be a graded nonunital complex
C*-algebra with generator `σ` and let `ι` be any index type. On the pre-Hilbert right module of
finitely supported `B`-valued families indexed by `ι`, the generator applies `σ` to each coordinate
and is a complex-linear equivalence. -/
def standardPreGenerator (γ : CStarGrading B) :
    CStarModule.Right.StandardPre B ι ≃ₗ[ℂ]
      CStarModule.Right.StandardPre B ι :=
    (CStarModule.Right.StandardPre.toFinsuppLinearEquiv
    (B := B) (ι := ι)).trans
    ((Finsupp.mapRange.linearEquiv
      (R := ℂ) (LinearEquiv.ofBijective
        (LinearMap.ofClass γ.generatorAut)
        γ.generatorAut.bijective)).trans
      (CStarModule.Right.StandardPre.toFinsuppLinearEquiv
        (B := B) (ι := ι)).symm)

@[simp]
theorem standardPreGenerator_apply (γ : CStarGrading B)
    (x : CStarModule.Right.StandardPre B ι) (i : ι) :
    standardPreGenerator (ι := ι) γ x i = γ.generatorAut (x i) := by
  change (Finsupp.mapRange.linearEquiv
    (R := ℂ) (LinearEquiv.ofBijective
      (LinearMap.ofClass γ.generatorAut)
      γ.generatorAut.bijective)
      (CStarModule.Right.StandardPre.toFinsupp x)) i = _
  change γ.generatorAut (x i) = γ.generatorAut (x i)
  rfl

theorem standardPreGenerator_involutive (γ : CStarGrading B) :
    Function.Involutive (standardPreGenerator (ι := ι) γ) := by
  intro x
  apply CStarModule.Right.StandardPre.toFinsupp.injective
  apply Finsupp.ext
  intro i
  change standardPreGenerator γ (standardPreGenerator γ x) i = x i
  rw [standardPreGenerator_apply, standardPreGenerator_apply,
    γ.generator_involutive]

theorem standardPreGenerator_right_smul (γ : CStarGrading B)
    (x : CStarModule.Right.StandardPre B ι) (b : B) :
    standardPreGenerator γ (x <• b) =
      standardPreGenerator γ x <• γ.generatorAut b := by
  apply CStarModule.Right.StandardPre.toFinsupp.injective
  apply Finsupp.ext
  intro i
  change standardPreGenerator γ (x <• b) i =
    (standardPreGenerator γ x <• γ.generatorAut b) i
  rw [standardPreGenerator_apply]
  simp only [CStarModule.Right.StandardPre.coe_op_smul,
    standardPreGenerator_apply]
  change γ.generatorAut (x i * b) =
    γ.generatorAut (x i) * γ.generatorAut b
  exact map_mul γ.generatorAut (x i) b

theorem standardPreGenerator_rightInner (γ : CStarGrading B)
    (x y : CStarModule.Right.StandardPre B ι) :
    CStarModule.rightInner (B := B)
        (standardPreGenerator γ x) (standardPreGenerator γ y) =
      γ.generatorAut (CStarModule.rightInner (B := B) x y) := by
  classical
  rw [CStarModule.Right.StandardPre.rightInner_apply,
    CStarModule.Right.StandardPre.rightInner_apply]
  have hsupp :
      (CStarModule.Right.StandardPre.toFinsupp
        (standardPreGenerator γ x)).support =
        (CStarModule.Right.StandardPre.toFinsupp x).support := by
    ext i
    simp [standardPreGenerator_apply]
  rw [Finsupp.sum, Finsupp.sum, hsupp, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [standardPreGenerator_apply, map_mul, map_star]

@[simp]
theorem norm_standardPreGenerator (γ : CStarGrading B)
    (x : CStarModule.Right.StandardPre B ι) :
    ‖standardPreGenerator γ x‖ = ‖x‖ := by
  calc
    ‖standardPreGenerator γ x‖ =
        √‖CStarModule.rightInner (B := B)
          (standardPreGenerator γ x) (standardPreGenerator γ x)‖ :=
      CStarModule.AdjointableOperator.norm_eq_sqrt_norm_rightInner _
    _ = √‖γ.generatorAut
        (CStarModule.rightInner (B := B) x x)‖ := by
      rw [standardPreGenerator_rightInner]
    _ = √‖CStarModule.rightInner (B := B) x x‖ := by
      rw [StarAlgEquiv.norm_map]
    _ = ‖x‖ :=
      (CStarModule.AdjointableOperator.norm_eq_sqrt_norm_rightInner x).symm

theorem standardComparison_norm (γ : CStarGrading B)
    (x : CStarModule.Right.StandardPre B ι) :
    ‖(CStarModule.Right.Standard.ofPre (B := B) (ι := ι)).toLinearMap
        (standardPreGenerator γ x)‖ =
      ‖(CStarModule.Right.Standard.ofPre
        (B := B) (ι := ι)).toLinearMap x‖ := by
  change ‖CStarModule.Right.Standard.ofPre (standardPreGenerator γ x)‖ =
    ‖CStarModule.Right.Standard.ofPre x‖
  rw [(CStarModule.Right.Standard.ofPre
      (B := B) (ι := ι)).norm_map,
    (CStarModule.Right.Standard.ofPre
      (B := B) (ι := ι)).norm_map,
    norm_standardPreGenerator]

/-- **Grading generator on the complete standard module.** Let `B` be a graded nonunital complex
C*-algebra with generator `σ` and let `ι` be any index type. The coordinatewise generator on
finitely supported `B`-valued families extends to a continuous complex-linear involution of their
completed standard right Hilbert module. -/
noncomputable def standardGenerator (γ : CStarGrading B) :
    CStarModule.Right.Standard B ι ≃L[ℂ]
      CStarModule.Right.Standard B ι :=
  ((standardPreGenerator (ι := ι) γ).extendOfIsometry
    (CStarModule.Right.Standard.ofPre
      (B := B) (ι := ι)).toLinearMap
    (CStarModule.Right.Standard.ofPre
      (B := B) (ι := ι)).toLinearMap
    (CStarModule.Right.Standard.denseRange_ofPre
      (B := B) (ι := ι))
    (CStarModule.Right.Standard.denseRange_ofPre
      (B := B) (ι := ι))
    (standardComparison_norm γ)).toContinuousLinearEquiv

@[simp]
theorem standardGenerator_ofPre (γ : CStarGrading B)
    (x : CStarModule.Right.StandardPre B ι) :
    standardGenerator (ι := ι) γ
        (CStarModule.Right.Standard.ofPre x) =
      CStarModule.Right.Standard.ofPre (standardPreGenerator γ x) := by
  unfold standardGenerator
  exact LinearEquiv.extendOfIsometry_eq
    (standardPreGenerator γ)
    (CStarModule.Right.Standard.ofPre
      (B := B) (ι := ι)).toLinearMap
    (CStarModule.Right.Standard.ofPre
      (B := B) (ι := ι)).toLinearMap
    (CStarModule.Right.Standard.denseRange_ofPre
      (B := B) (ι := ι))
    (CStarModule.Right.Standard.denseRange_ofPre
      (B := B) (ι := ι))
    (standardComparison_norm γ) x

theorem standardGenerator_coord (γ : CStarGrading B)
    (x : CStarModule.Right.Standard B ι) (i : ι) :
    CStarModule.Right.Standard.coord i (standardGenerator γ x) =
      γ.generatorAut (CStarModule.Right.Standard.coord i x) := by
  have hfun :
      (fun x : CStarModule.Right.Standard B ι ↦
        CStarModule.Right.Standard.coord i (standardGenerator γ x)) =
      (fun x : CStarModule.Right.Standard B ι ↦
        γ.generatorAut (CStarModule.Right.Standard.coord i x)) := by
    apply Continuous.ext_on
      (CStarModule.Right.Standard.denseRange_ofPre
        (B := B) (ι := ι))
    · exact (CStarModule.Right.Standard.coord (B := B) i).continuous.comp
        (standardGenerator γ).continuous
    · exact (StarAlgEquiv.isometry γ.generatorAut).continuous.comp
        (CStarModule.Right.Standard.coord (B := B) i).continuous
    · rintro _ ⟨a, rfl⟩
      change CStarModule.Right.Standard.coord i
          (standardGenerator γ (CStarModule.Right.Standard.ofPre a)) =
        γ.generatorAut
          (CStarModule.Right.Standard.coord i
            (CStarModule.Right.Standard.ofPre a))
      rw [standardGenerator_ofPre,
        CStarModule.Right.Standard.coord_ofPre,
        CStarModule.Right.Standard.coord_ofPre,
        standardPreGenerator_apply]
  exact congrFun hfun x

theorem standardGenerator_rightInner (γ : CStarGrading B)
    (x y : CStarModule.Right.Standard B ι) :
    CStarModule.rightInner (B := B)
        (standardGenerator γ x) (standardGenerator γ y) =
      γ.generatorAut (CStarModule.rightInner (B := B) x y) := by
  have hdense : DenseRange
      (fun p : CStarModule.Right.StandardPre B ι ×
          CStarModule.Right.StandardPre B ι ↦
        (CStarModule.Right.Standard.ofPre p.1,
          CStarModule.Right.Standard.ofPre p.2)) :=
    (CStarModule.Right.Standard.denseRange_ofPre
      (B := B) (ι := ι)).prodMap
      (CStarModule.Right.Standard.denseRange_ofPre
        (B := B) (ι := ι))
  have hfun :
      (fun p : CStarModule.Right.Standard B ι ×
          CStarModule.Right.Standard B ι ↦
        CStarModule.rightInner (B := B)
          (standardGenerator γ p.1) (standardGenerator γ p.2)) =
      (fun p : CStarModule.Right.Standard B ι ×
          CStarModule.Right.Standard B ι ↦
        γ.generatorAut
          (CStarModule.rightInner (B := B) p.1 p.2)) := by
    apply Continuous.ext_on hdense
    · exact CStarModule.continuous_rightInner.comp
        (((standardGenerator γ).continuous.comp continuous_fst).prodMk
          ((standardGenerator γ).continuous.comp continuous_snd))
    · exact (StarAlgEquiv.isometry γ.generatorAut).continuous.comp
        CStarModule.continuous_rightInner
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      change CStarModule.rightInner (B := B)
          (standardGenerator γ (CStarModule.Right.Standard.ofPre a))
          (standardGenerator γ (CStarModule.Right.Standard.ofPre b)) =
        γ.generatorAut
          (CStarModule.rightInner (B := B)
            (CStarModule.Right.Standard.ofPre a)
            (CStarModule.Right.Standard.ofPre b))
      rw [standardGenerator_ofPre, standardGenerator_ofPre,
        CStarModule.Right.Standard.rightInner_ofPre_ofPre,
        CStarModule.Right.Standard.rightInner_ofPre_ofPre,
        standardPreGenerator_rightInner]
  exact congrFun hfun (x, y)

/-- **Grading of the standard Hilbert module.** Let `B` be a graded nonunital complex C*-algebra with
generator `σ` and let `ι` be any index type. The completed standard right Hilbert `B`-module indexed
by `ι` has the grading extending coordinatewise application of `σ`. -/
def standard (γ : CStarGrading B) :
    CStarModuleGrading γ (CStarModule.Right.Standard B ι) where
  generator := standardGenerator γ
  generator_involutive x := by
    apply CStarModule.Right.Standard.coord_ext
    intro i
    rw [standardGenerator_coord, standardGenerator_coord,
      γ.generator_involutive]
  generator_right_smul x b := by
    apply CStarModule.Right.Standard.coord_ext
    intro i
    rw [standardGenerator_coord,
      CStarModule.Right.Standard.coord_right_smul,
      map_mul,
      CStarModule.Right.Standard.coord_right_smul,
      standardGenerator_coord]
  generator_rightInner := standardGenerator_rightInner γ

@[simp]
theorem standard_generator_coord (γ : CStarGrading B)
    (x : CStarModule.Right.Standard B ι) (i : ι) :
    CStarModule.Right.Standard.coord i ((standard γ).generator x) =
      γ.generatorAut (CStarModule.Right.Standard.coord i x) :=
  standardGenerator_coord γ x i

end CStarModuleGrading
