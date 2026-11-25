/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.MapLeft.Bounded
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Completion

/-!
# Actual completed first-factor tensor operators

The bounded map on the genuine radical quotient is extended through the
stock completion inclusion. Its genuine paired adjoint is extended in the
same way and the adjoint equation follows by continuity and dense images.

The output is the literal CompletedTensor carrier with its already
constructed module data, not a supplied IsModel or chosen operator.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uF₁ uE₂

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [SMul B₁ᵐᵒᵖ F₁] [CStarModule B₁ᵐᵒᵖ F₁] [CompleteSpace F₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F₁ be a complete right Hilbert B₁-module and L an adjointable operator from E₁ to F₁.
The first-factor operator extends to a bounded complex-linear map between the completed
internal tensor products. -/
def completedLeftCLM
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ;
    CompletedTensor (E₁ := E₁) φ →L[ℂ] CompletedTensor (E₁ := F₁) φ := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ
  exact ((UniformSpace.Completion.toComplL :
    RadicalTensor (E₁ := F₁) φ →L[ℂ] CompletedTensor (E₁ := F₁) φ).comp
      (radicalLeftCLM φ L)).fromCompletion

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F₁ be a complete right Hilbert B₁-module and L an adjointable operator from E₁ to F₁.
On a radical-quotient vector, this extension is the completed image of the induced first-
factor map. -/
@[simp]
theorem completedLeftCLM_coe
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) (q : RadicalTensor (E₁ := E₁) φ) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ;
    completedLeftCLM φ L (q : CompletedTensor (E₁ := E₁) φ) =
      (radicalLeftMap φ L q : CompletedTensor (E₁ := F₁) φ) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ
  simp only [completedLeftCLM, ContinuousLinearMap.fromCompletion_apply_coe,
    ContinuousLinearMap.comp_apply, UniformSpace.Completion.coe_toComplL,
    radicalLeftCLM_apply]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F₁ be a complete right Hilbert B₁-module and L an adjointable operator from E₁ to F₁.
On a balanced algebraic tensor, this extension applies L to the first factor before passing to
the completed quotient. -/
@[simp]
theorem completedLeftCLM_fromBalanced
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) (z : BalancedTensor (E₁ := E₁) φ) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ;
    completedLeftCLM φ L (completedFromBalanced φ z) =
      completedFromBalanced φ (balancedLeftMap φ L z) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ
  rw [completedFromBalanced_apply, completedFromBalanced_apply,
    completedLeftCLM_coe, radicalLeftMap_mkQ]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F₁ be a complete right Hilbert B₁-module and L an adjointable operator from E₁ to F₁.
The norm of the image of a completed tensor z is at most the operator norm of L times the norm
of z. -/
theorem completedLeftCLM_norm_apply_le
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) (z : CompletedTensor (E₁ := E₁) φ) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ;
    ‖completedLeftCLM φ L z‖ ≤ ‖L‖ * ‖z‖ := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ
  refine UniformSpace.Completion.induction_on z
    (isClosed_le (completedLeftCLM φ L).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro q
  simpa only [completedLeftCLM_coe, UniformSpace.Completion.norm_coe] using
    radicalLeftMap_norm_le φ L q

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F₁ be a complete right Hilbert B₁-module and L an adjointable operator from E₁ to F₁.
The maps induced by L and its adjoint satisfy the coefficient-valued inner-product adjoint
identity on the completed tensor products. -/
theorem completedLeftCLM_inner_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁)
    (z : CompletedTensor (E₁ := E₁) φ) (w : CompletedTensor (E₁ := F₁) φ) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) φ) := completedCStarModule φ;
    rightInner (B := B₂) (completedLeftCLM φ L z) w =
      rightInner (B := B₂) z (completedLeftCLM φ L.adjointOperator w) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) φ) := completedCStarModule φ
  have hl : Continuous fun p :
      CompletedTensor (E₁ := E₁) φ × CompletedTensor (E₁ := F₁) φ =>
      rightInner (B := B₂) (completedLeftCLM φ L p.1) p.2 :=
    (CStarModule.continuous_rightInner (B := B₂)
      (E := CompletedTensor (E₁ := F₁) φ)).comp
        (((completedLeftCLM φ L).continuous.comp continuous_fst).prodMk continuous_snd)
  have hr : Continuous fun p :
      CompletedTensor (E₁ := E₁) φ × CompletedTensor (E₁ := F₁) φ =>
      rightInner (B := B₂) p.1 (completedLeftCLM φ L.adjointOperator p.2) :=
    (CStarModule.continuous_rightInner (B := B₂)
      (E := CompletedTensor (E₁ := E₁) φ)).comp
        (continuous_fst.prodMk
          ((completedLeftCLM φ L.adjointOperator).continuous.comp continuous_snd))
  refine UniformSpace.Completion.induction_on₂ z w (isClosed_eq hl hr) ?_
  intro q v
  obtain ⟨q, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
  obtain ⟨v, rfl⟩ := (radicalSpace (E₁ := F₁) φ).mkQ_surjective v
  have hq : ((radicalSpace (E₁ := E₁) φ).mkQ q :
      CompletedTensor (E₁ := E₁) φ) = completedFromBalanced φ q :=
    (completedFromBalanced_apply φ q).symm
  have hv : ((radicalSpace (E₁ := F₁) φ).mkQ v :
      CompletedTensor (E₁ := F₁) φ) = completedFromBalanced φ v :=
    (completedFromBalanced_apply φ v).symm
  rw [hq, hv, completedLeftCLM_fromBalanced, completedLeftCLM_fromBalanced,
    completedFromBalanced_inner, completedFromBalanced_inner]
  exact balancedLeftMap_inner_adjoint φ L q v

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F₁ be a complete right Hilbert B₁-module and L an adjointable operator from E₁ to F₁.
Applying L in the first factor defines an adjointable operator between the completed internal
tensor products, with the operator induced by the adjoint of L as its adjoint. -/
def completedLeftOperator
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) φ) := completedCStarModule φ;
    AdjointableOperator B₂ (CompletedTensor (E₁ := E₁) φ)
      (CompletedTensor (E₁ := F₁) φ) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) φ) := radicalRightAction φ
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) φ) := completedCStarModule φ
  exact
    { toContinuousLinearMap := completedLeftCLM φ L
      adjoint := completedLeftCLM φ L.adjointOperator
      isAdjointPair' :=
        (AdjointableOperator.isAdjointPair_iff_adjoint_inner
          (completedLeftCLM φ L) (completedLeftCLM φ L.adjointOperator)).mpr
            (completedLeftCLM_inner_adjoint φ L) }

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F₁ be a complete right Hilbert B₁-module and L an adjointable operator from E₁ to F₁.
The induced operator sends the pure tensor of x and y to the pure tensor of Lx and y. -/
@[simp]
theorem completedLeftOperator_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) (x : E₁) (y : E₂) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) φ) := completedCStarModule φ;
    completedLeftOperator φ L (completedPure φ x y) = completedPure φ (L x) y := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) φ) := completedCStarModule φ
  change completedLeftCLM φ L (completedPure φ x y) = completedPure φ (L x) y
  rw [completedPure_apply, completedPure_apply,
    completedLeftCLM_coe, radicalLeftMap_pure]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F₁ be a complete right Hilbert B₁-module and L an adjointable operator from E₁ to F₁.
Its adjoint sends the pure tensor of x and y to the pure tensor of L-adjoint x and y. -/
@[simp]
theorem completedLeftOperator_adjoint_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) (x : F₁) (y : E₂) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) φ) := completedCStarModule φ;
    (completedLeftOperator φ L).adjoint (completedPure φ x y) =
      completedPure φ (L.adjoint x) y := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) φ) := completedCStarModule φ
  change completedLeftCLM φ L.adjointOperator (completedPure φ x y) =
    completedPure φ (L.adjoint x) y
  rw [completedPure_apply, completedPure_apply, completedLeftCLM_coe,
    radicalLeftMap_pure, AdjointableOperator.adjointOperator_apply]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F₁ be a complete right Hilbert B₁-module and L an adjointable operator from E₁ to F₁.
The operator norm of the induced first-factor operator is at most the operator norm of L. -/
theorem completedLeftOperator_norm_le
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) φ) := completedCStarModule φ;
    ‖completedLeftOperator φ L‖ ≤ ‖L‖ := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) φ) := completedCStarModule φ
  rw [AdjointableOperator.norm_eq]
  change ‖completedLeftCLM φ L‖ ≤ ‖L‖
  exact ContinuousLinearMap.opNorm_le_bound _ (_root_.norm_nonneg L)
    (fun z => completedLeftCLM_norm_apply_le φ L z)

end CStarModule.InternalTensorProduct
