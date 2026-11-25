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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Tactic.Ring

/-!
# Pure-tensor bounds on internal-tensor models

The existing model determines the coefficient-inner formula and complex
linearity. The opposite orders and all five universes remain explicit.
These bounds do not construct a balanced tensor completion or an endpoint fibre.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped CStarAlgebra RightActions

namespace CStarModule.InternalTensorProduct.IsModel

universe uB₁ uB₂ uE₁ uE₂ uX

variable {B₁ : Type uB₁} {B₂ : Type uB₂}
variable [NonUnitalCStarAlgebra B₁] [PartialOrder B₁ᵐᵒᵖ]
variable [NonUnitalCStarAlgebra B₂] [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} {E₂ : Type uE₂} {X : Type uX}
variable [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [SMul B₁ᵐᵒᵖ E₁]
  [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [SMul B₂ᵐᵒᵖ E₂]
  [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul B₂ᵐᵒᵖ X]
  [CStarModule B₂ᵐᵒᵖ X] [CompleteSpace X]
variable {φ : B₁ →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End B₂ E₂}
variable {pure : E₁ → E₂ → X}

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, with a partial order on B₁ᵐᵒᵖ and a
star-compatible partial order on B₂ᵐᵒᵖ. Let E₁ be a complete normed right inner-product
B₁-module, and let E₂ and X be complete normed right inner-product B₂-modules, all with
compatible complex normed-space structures. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂. Let pure : E₁ × E₂ → X. Assume pure is complex-linear in
each variable, balances the B₁-actions, respects the B₂-action and satisfies the internal-tensor
inner-product law and has dense complex-linear span in X.

For x ∈ E₁ and y ∈ E₂, the pure-vector norm satisfies ‖pure(x,y)‖ ≤ ‖x‖ ‖y‖.
-/
theorem norm_pure_le (hX : CStarModule.InternalTensorProduct.IsModel φ pure)
    (x : E₁) (y : E₂) : ‖pure x y‖ ≤ ‖x‖ * ‖y‖ := by
  let a : B₁ := CStarModule.rightInner (B := B₁) x x
  have hgram := hX.2.2.2.2.2.2.1 x x y y
  have hTy : ‖φ a y‖ ≤ ‖φ a‖ * ‖y‖ := by
    simpa only [CStarModule.AdjointableOperator.norm_eq,
      CStarModule.AdjointableOperator.coe_toContinuousLinearMap] using
        (φ a).toContinuousLinearMap.le_opNorm y
  apply (sq_le_sq₀ (norm_nonneg (pure x y))
    (mul_nonneg (norm_nonneg x) (norm_nonneg y))).mp
  calc
    ‖pure x y‖ ^ 2 =
        ‖CStarModule.rightInner (B := B₂) (pure x y) (pure x y)‖ :=
      (CStarModule.norm_rightInner_self (B := B₂) (pure x y)).symm
    _ = ‖CStarModule.rightInner (B := B₂) y (φ a y)‖ := by
      simpa only [a] using congrArg (fun z : B₂ => ‖z‖) hgram
    _ ≤ ‖y‖ * ‖φ a y‖ := by
      simpa only [CStarModule.rightInner, MulOpposite.norm_unop] using
        (CStarModule.norm_inner_le E₂ (A := B₂ᵐᵒᵖ) (x := y) (y := φ a y))
    _ ≤ ‖y‖ * (‖φ a‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left hTy (norm_nonneg y)
    _ ≤ ‖y‖ * (‖a‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le φ a)
          (norm_nonneg y)) (norm_nonneg y)
    _ = (‖x‖ * ‖y‖) ^ 2 := by
      dsimp only [a]
      rw [CStarModule.norm_rightInner_self]
      ring

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, with a partial order on B₁ᵐᵒᵖ and a
star-compatible partial order on B₂ᵐᵒᵖ. Let E₁ be a complete normed right inner-product
B₁-module, and let E₂ and X be complete normed right inner-product B₂-modules, all with
compatible complex normed-space structures. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂. Let pure : E₁ × E₂ → X. Assume pure is complex-linear in
each variable, balances the B₁-actions, respects the B₂-action and satisfies the internal-tensor
inner-product law and has dense complex-linear span in X.

For a fixed y ∈ E₂, the pure-vector map x ↦ pure(x,y) is bounded and complex-linear from E₁ to
X.
-/
def pureLeftCLM (hX : CStarModule.InternalTensorProduct.IsModel φ pure)
    (y : E₂) : E₁ →L[ℂ] X := by
  let L : E₁ →ₗ[ℂ] X :=
    { toFun := fun x => pure x y
      map_add' := fun x z => hX.1 x z y
      map_smul' := fun c x => hX.2.2.1 c x y }
  exact L.mkContinuous ‖y‖ fun x => by
    change ‖pure x y‖ ≤ ‖y‖ * ‖x‖
    simpa only [mul_comm] using norm_pure_le hX x y

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, with a partial order on B₁ᵐᵒᵖ and a
star-compatible partial order on B₂ᵐᵒᵖ. Let E₁ be a complete normed right inner-product
B₁-module, and let E₂ and X be complete normed right inner-product B₂-modules, all with
compatible complex normed-space structures. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂. Let pure : E₁ × E₂ → X. Assume pure is complex-linear in
each variable, balances the B₁-actions, respects the B₂-action and satisfies the internal-tensor
inner-product law and has dense complex-linear span in X.

For y ∈ E₂, the bounded pure-vector map E₁ → X sends x to pure(x,y).
-/
@[simp]
theorem pureLeftCLM_apply (hX : CStarModule.InternalTensorProduct.IsModel φ pure)
    (x : E₁) (y : E₂) : pureLeftCLM hX y x = pure x y := by
  simp only [pureLeftCLM, LinearMap.mkContinuous_apply]
  rfl

end CStarModule.InternalTensorProduct.IsModel
