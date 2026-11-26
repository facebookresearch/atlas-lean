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
# Completed direct sums of right modules

For right pre-Hilbert `B`-modules `E_i`, complete their finite-support sum for the norm `sqrt ‖∑
i, ⟨x_i,x_i⟩_B‖`. The resulting `Completed B E` is a right Hilbert module. The maps `j_i : E_i →
Completed B E` are isometric, preserve right coefficients and same-coordinate inner products,
and have orthogonal ranges for distinct indices. Their complex linear span is dense.

The coordinate-presentation predicates record these action, inner-product, orthogonality and
density laws; the completed version additionally requires the target to be complete. Component
completeness is not needed.
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

/-- **Completed Hilbert-module direct sum.** Let `B` be a nonunital complex C-star algebra with
star-compatible order on `Bᵐᵒᵖ`, `I` an arbitrary index type, and `E_i` complex normed right
pre-Hilbert `B`-modules. `Completed B E` is the completion of their finite-support sum for
`‖x‖ = sqrt ‖∑ i ∈ support x, ⟨x_i,x_i⟩_B‖`. The fibers may be incomplete and `I` may be
empty. -/
abbrev Completed (B : Type uB) [NonUnitalCStarAlgebra B]
    [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
    {I : Type uI} (E : I → Type uE)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, SMul Bᵐᵒᵖ (E i)] [∀ i, CStarModule Bᵐᵒᵖ (E i)] :=
  UniformSpace.Completion (Algebraic B E)

/-- **Inner product on the completed direct sum.** The finite-sum coefficient inner product
extends continuously to the completion and gives its right Hilbert `B`-module structure. -/
noncomputable instance completedCStarModule : CStarModule Bᵐᵒᵖ (Completed B E) :=
  CStarModule.completionCStarModule (A := Bᵐᵒᵖ) (E := Algebraic B E)

/-- **Isometric inclusion of finite-support vectors.** The map from `Algebraic B E` into
`Completed B E` is the complex-linear isometric completion inclusion. -/
def algebraicInclusion : Algebraic B E →ₗᵢ[ℂ] Completed B E :=
  UniformSpace.Completion.toComplₗᵢ

@[simp]
theorem algebraicInclusion_apply (x : Algebraic B E) :
    algebraicInclusion x = (x : Completed B E) := by
  exact congrFun (UniformSpace.Completion.coe_toComplₗᵢ
    (𝕜 := ℂ) (E := Algebraic B E)) x

/-- **Isometric inclusion of a component into the completion.** `completedSingle i : E i →ₗᵢ[ℂ]
Completed B E` is the finite-support one-coordinate inclusion followed by completion. -/
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

/-- **Density of completed coordinate ranges.** The complex linear span of all vectors
`completedSingle i x` is dense in `Completed B E`. -/
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

/-- **Coordinate presentation of a pre-Hilbert direct sum.** A family of complex-linear continuous
maps `j_i : E_i → X` has this property when it preserves right coefficients and
same-coordinate inner products, different coordinate ranges are orthogonal, and the complex
span of the ranges is dense in `X`. -/
structure IsPreModel
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [SMul Bᵐᵒᵖ X] [CStarModule Bᵐᵒᵖ X]
    (singleX : ∀ i, E i →L[ℂ] X) : Prop where
  /-- **Right linearity of coordinate maps.** Each inclusion satisfies `j_i (x <• b) = j_i x <•
  b`. -/
  map_right_smul (i : I) (x : E i) (b : B) :
    singleX i (x <• b) = singleX i x <• b
  /-- **Inner product within one coordinate.** The coordinate map satisfies `⟨j_i x,j_i y⟩_B =
  ⟨x,y⟩_B`. -/
  inner_same (i : I) (x y : E i) :
    rightInner (B := B) (singleX i x) (singleX i y) = rightInner (B := B) x y
  /-- **Orthogonality of different coordinates.** If `i ≠ j`, then `⟨j_i x,j_j y⟩_B = 0` for all
  component vectors. -/
  inner_ne {i j : I} (h : i ≠ j) (x : E i) (y : E j) :
    rightInner (B := B) (singleX i x) (singleX j y) = 0
  /-- **Density of the coordinate span.** The complex linear span of the union of all
  coordinate-map ranges is dense in the ambient module `X`. -/
  dense_span : Dense (Submodule.span ℂ
    (Set.range fun p : Σ i, E i ↦ singleX p.1 p.2) : Set X)

/-- **Complete coordinate presentation of a direct sum.** A complete target module `X` with
coordinate maps satisfying `IsPreModel` is a completed direct-sum presentation. -/
structure IsModel
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [SMul Bᵐᵒᵖ X] [CStarModule Bᵐᵒᵖ X] [CompleteSpace X]
    (singleX : ∀ i, E i →L[ℂ] X) : Prop
    extends IsPreModel (B := B) (E := E) singleX where

/-- **Coordinate presentation of the constructed completion.** The maps `completedSingle i`
satisfy the action, inner-product, orthogonality and dense-span laws of `IsModel` on
`Completed B E`. -/
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
