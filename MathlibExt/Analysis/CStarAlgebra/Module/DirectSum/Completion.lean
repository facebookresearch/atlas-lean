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

public import MathlibExt.Analysis.CStarAlgebra.Module.Completion
public import MathlibExt.Analysis.CStarAlgebra.Module.DirectSum.Algebraic

/-!
# Completed direct sums of right C-star modules

The Hilbert-module direct sum of an arbitrary family is the stock completion
of its literal finite-support pre-Hilbert direct sum.  Coordinate inclusions
are isometries, distinct coordinates are orthogonal, and their complex linear
span is dense.

No component completeness is needed: this construction also completes a
family of pre-Hilbert modules.  For finite complete families, later comparison
lemmas may identify this carrier with the usual finite product model.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped RightActions

namespace CStarModule.DirectSum

universe uB uI uE uX

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {I : Type uI} {E : I → Type uE}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
variable [∀ i, SMul Bᵐᵒᵖ (E i)] [∀ i, CStarModule Bᵐᵒᵖ (E i)]

/-- The actual completed Hilbert-module direct sum. -/
abbrev Completed (B : Type uB) [NonUnitalCStarAlgebra B]
    [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
    {I : Type uI} (E : I → Type uE)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, SMul Bᵐᵒᵖ (E i)] [∀ i, CStarModule Bᵐᵒᵖ (E i)] :=
  UniformSpace.Completion (Algebraic B E)

/-- The completed direct sum inherits the extended coefficient-valued inner
product and the stock completion norm. -/
noncomputable instance completedCStarModule : CStarModule Bᵐᵒᵖ (Completed B E) :=
  CStarModule.completionCStarModule (A := Bᵐᵒᵖ) (E := Algebraic B E)

/-- The canonical inclusion of the algebraic finite-support sum. -/
def algebraicInclusion : Algebraic B E →ₗᵢ[ℂ] Completed B E :=
  UniformSpace.Completion.toComplₗᵢ

@[simp]
theorem algebraicInclusion_apply (x : Algebraic B E) :
    algebraicInclusion x = (x : Completed B E) := by
  exact congrFun (UniformSpace.Completion.coe_toComplₗᵢ
    (𝕜 := ℂ) (E := Algebraic B E)) x

/-- A coordinate inclusion into the completed direct sum. -/
def completedSingle (i : I) : E i →ₗᵢ[ℂ] Completed B E :=
  algebraicInclusion.comp (single (B := B) (E := E) i)

@[simp]
theorem completedSingle_apply (i : I) (x : E i) :
    completedSingle (B := B) (E := E) i x =
      ((single (B := B) (E := E) i x : Algebraic B E) : Completed B E) := by
  change algebraicInclusion (single (B := B) (E := E) i x) = _
  rw [algebraicInclusion_apply]

@[simp, nolint simpNF]
theorem completedSingle_right_smul (i : I) (x : E i) (b : B) :
    completedSingle (B := B) (E := E) i (x <• b) =
      completedSingle (B := B) (E := E) i x <• b := by
  rw [completedSingle_apply, completedSingle_apply,
    ← CStarModule.coe_completion_coeff_smul
      (A := Bᵐᵒᵖ) (E := Algebraic B E)]
  congr 1
  exact singleLinear_right_smul (B := B) (E := E) i x b

@[simp, nolint simpNF]
theorem inner_completedSingle_same (i : I) (x y : E i) :
    inner Bᵐᵒᵖ (completedSingle (B := B) (E := E) i x)
        (completedSingle (B := B) (E := E) i y) = inner Bᵐᵒᵖ x y := by
  rw [completedSingle_apply, completedSingle_apply,
    CStarModule.completionCStarModule_inner_coe_coe]
  exact inner_single_same i x y

@[simp, nolint simpNF]
theorem inner_completedSingle_ne {i j : I} (h : i ≠ j) (x : E i) (y : E j) :
    inner Bᵐᵒᵖ (completedSingle (B := B) (E := E) i x)
        (completedSingle (B := B) (E := E) j y) = 0 := by
  rw [completedSingle_apply, completedSingle_apply,
    CStarModule.completionCStarModule_inner_coe_coe]
  exact inner_single_ne h x y

/-- The complex linear span of the coordinate inclusions is dense in the
completed direct sum. -/
theorem dense_span_completedSingle :
    Dense (Submodule.span ℂ
      (Set.range fun p : Σ i, E i ↦
        completedSingle (B := B) (E := E) p.1 p.2) : Set (Completed B E)) := by
  let S : Submodule ℂ (Completed B E) :=
    Submodule.span ℂ (Set.range fun p : Σ i, E i ↦
      completedSingle (B := B) (E := E) p.1 p.2)
  have hcoe : Set.range ((↑) : Algebraic B E → Completed B E) ⊆
      (S : Set (Completed B E)) := by
    rintro _ ⟨x, rfl⟩
    induction x using CStarModule.DirectSum.induction with
    | h0 => exact Submodule.zero_mem S
    | ha i z x hi hz ih =>
        change algebraicInclusion
          (singleLinear (B := B) (E := E) i z + x) ∈ S
        rw [map_add]
        have hsingle : algebraicInclusion (singleLinear (B := B) (E := E) i z) =
            completedSingle (B := B) (E := E) i z := by
          rw [completedSingle_apply, algebraicInclusion_apply,
            single_apply_eq_singleLinear]
        apply Submodule.add_mem S
        · rw [hsingle]
          exact Submodule.subset_span ⟨⟨i, z⟩, rfl⟩
        · change (x : Completed B E) ∈ (S : Set (Completed B E))
          exact ih
  exact Dense.mono hcoe UniformSpace.Completion.denseRange_coe

/-- Characteristic coordinate laws of a pre-Hilbert-module direct sum.
This reusable contract also recognizes incomplete concrete presentations. -/
structure IsPreModel
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [SMul Bᵐᵒᵖ X] [CStarModule Bᵐᵒᵖ X]
    (singleX : ∀ i, E i →L[ℂ] X) : Prop where
  /-- Coordinate inclusions preserve the right coefficient action. -/
  map_right_smul (i : I) (x : E i) (b : B) :
    singleX i (x <• b) = singleX i x <• b
  /-- Same-coordinate inclusions preserve the coefficient inner product. -/
  inner_same (i : I) (x y : E i) :
    rightInner (B := B) (singleX i x) (singleX i y) = rightInner (B := B) x y
  /-- Distinct coordinates are orthogonal. -/
  inner_ne {i j : I} (h : i ≠ j) (x : E i) (y : E j) :
    rightInner (B := B) (singleX i x) (singleX j y) = 0
  /-- Coordinate ranges have dense complex linear span. -/
  dense_span : Dense (Submodule.span ℂ
    (Set.range fun p : Σ i, E i ↦ singleX p.1 p.2) : Set X)

/-- Characteristic coordinate laws of a completed Hilbert-module direct sum.
Completeness is part of this contract rather than an accidental property of a
particular presentation. -/
structure IsModel
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [SMul Bᵐᵒᵖ X] [CStarModule Bᵐᵒᵖ X] [CompleteSpace X]
    (singleX : ∀ i, E i →L[ℂ] X) : Prop
    extends IsPreModel (B := B) (E := E) singleX where

/-- The literal choice-free completed construction satisfies the complete direct-sum
model contract. -/
theorem completed_isModel :
    IsModel (B := B) (E := E)
      (fun i ↦ (completedSingle (B := B) (E := E) i).toContinuousLinearMap) := by
  refine { toIsPreModel := ?_ }
  refine ⟨?_, ?_, ?_, dense_span_completedSingle (B := B) (E := E)⟩
  · intro i x b
    exact completedSingle_right_smul i x b
  · intro i x y
    change CStarModule.rightInner (B := B)
      (completedSingle (B := B) (E := E) i x)
      (completedSingle (B := B) (E := E) i y) = _
    simpa only [rightInner] using congrArg MulOpposite.unop
      (inner_completedSingle_same (B := B) (E := E) i x y)
  · intro i j h x y
    change CStarModule.rightInner (B := B)
      (completedSingle (B := B) (E := E) i x)
      (completedSingle (B := B) (E := E) j y) = 0
    change MulOpposite.unop
      (inner Bᵐᵒᵖ (completedSingle (B := B) (E := E) i x)
        (completedSingle (B := B) (E := E) j y)) = 0
    rw [inner_completedSingle_ne (B := B) (E := E) h x y]
    rfl

end CStarModule.DirectSum
