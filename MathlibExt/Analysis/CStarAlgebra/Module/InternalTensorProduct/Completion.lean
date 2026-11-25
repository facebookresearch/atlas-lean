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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.PreHilbert
public import MathlibExt.Analysis.CStarAlgebra.Module.Completion
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct

/-!
# The literal completed balanced internal tensor

The carrier is the stock completion of the actual algebraic radical quotient,
equipped with the named pre-Hilbert norm and dictionaries. The canonical pure
map passes through both genuine quotients and the stock completion inclusion.

All eight clauses of the existing IsModel interface are supplied below; no
output model, norm, module or completeness witness is an input. The input
modules use their given opposite orders and Hilbert dictionaries. The needed
positivity/null and completion parents are separate written proof proposals;
this file does not certify them or the Source presentation's existing choice.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped RightActions BigOperators

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂ uI uJ

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

The completed internal tensor is the norm completion of the balanced algebraic tensor after
quotienting by the radical of its coefficient-valued Gram form.
-/
abbrev CompletedTensor
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :=
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

The canonical complex-linear map from the balanced algebraic tensor to the completed internal
tensor first quotients by the Gram radical and then takes the completion image.
-/
def completedFromBalanced
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    BalancedTensor (E₁ := E₁) φ →ₗ[ℂ] CompletedTensor (E₁ := E₁) φ := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  exact (UniformSpace.Completion.toComplₗᵢ :
    RadicalTensor (E₁ := E₁) φ →ₗᵢ[ℂ]
      UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ)).toLinearMap.comp
        (radicalSpace (E₁ := E₁) φ).mkQ

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

For a balanced tensor z, its canonical completed image is the completion image of its class
modulo the Gram radical.
-/
theorem completedFromBalanced_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z : BalancedTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    completedFromBalanced φ z =
      ((radicalSpace φ).mkQ z :
        UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ)) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  change (UniformSpace.Completion.toComplₗᵢ :
    RadicalTensor (E₁ := E₁) φ →ₗᵢ[ℂ]
      UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ))
        ((radicalSpace φ).mkQ z) = _
  exact congrFun (UniformSpace.Completion.coe_toComplₗᵢ
    (𝕜 := ℂ) (E := RadicalTensor (E₁ := E₁) φ)) ((radicalSpace φ).mkQ z)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

The completed pure vector associated to x ∈ E₁ and y ∈ E₂ is the canonical completed image of
the balanced tensor x ⊗φ y.
-/
def completedPure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    E₁ → E₂ → CompletedTensor (E₁ := E₁) φ := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  exact fun x y => completedFromBalanced φ (balancedPure φ x y)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

For x ∈ E₁ and y ∈ E₂, the completed pure vector is the completion image of the radical-quotient
class of x ⊗φ y.
-/
theorem completedPure_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (x : E₁) (y : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    completedPure φ x y =
      ((radicalSpace φ).mkQ (balancedPure φ x y) :
        UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ)) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  change completedFromBalanced φ (balancedPure φ x y) = _
  exact completedFromBalanced_apply φ (balancedPure φ x y)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

The completed internal tensor is a right inner-product C*-module over B₂ for the Gram-form norm,
extended right action and completed inner product.
-/
@[instance_reducible]
def completedCStarModule
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  letI : CStarModule B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorCStarModule φ
  exact CStarModule.completionCStarModule
    (A := B₂ᵐᵒᵖ) (E := RadicalTensor (E₁ := E₁) φ)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

The canonical map from balanced tensors into the completion respects the right B₂-action.
-/
theorem completedFromBalanced_right_smul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z : BalancedTensor (E₁ := E₁) φ) (b : B₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    completedFromBalanced φ (balancedRightSMul φ b z) =
      completedFromBalanced φ z <• b := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorCStarModule φ
  rw [completedFromBalanced_apply, completedFromBalanced_apply]
  calc
    ((radicalSpace φ).mkQ (balancedRightSMul φ b z) :
        UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ)) =
      (radicalRightSMul φ b ((radicalSpace φ).mkQ z) :
        UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ)) :=
      congrArg
        (fun q : RadicalTensor (E₁ := E₁) φ =>
          (q : UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ)))
        (radicalRightSMul_mkQ φ b z).symm
    _ = ((radicalSpace φ).mkQ z :
        UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ)) <• b :=
      CStarModule.coe_completion_coeff_smul
        (A := B₂ᵐᵒᵖ) (E := RadicalTensor (E₁ := E₁) φ)
        (MulOpposite.op b) ((radicalSpace φ).mkQ z)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

The inner product of two canonical completed images is the Gram form of their balanced algebraic
representatives.
-/
theorem completedFromBalanced_inner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z w : BalancedTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) :=
      completedCStarModule φ;
    rightInner (B := B₂) (completedFromBalanced φ z) (completedFromBalanced φ w) =
      balancedInner φ z w := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorCStarModule φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) :=
    completedCStarModule φ
  rw [completedFromBalanced_apply, completedFromBalanced_apply]
  change MulOpposite.unop
      (inner B₂ᵐᵒᵖ
        ((radicalSpace φ).mkQ z :
          UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ))
        ((radicalSpace φ).mkQ w :
          UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ))) = _
  calc
    MulOpposite.unop
        (inner B₂ᵐᵒᵖ
          ((radicalSpace φ).mkQ z :
            UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ))
          ((radicalSpace φ).mkQ w :
            UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ))) =
      MulOpposite.unop (inner B₂ᵐᵒᵖ ((radicalSpace φ).mkQ z)
        ((radicalSpace φ).mkQ w)) :=
      congrArg MulOpposite.unop
        (CStarModule.completionCStarModule_inner_coe_coe
          (A := B₂ᵐᵒᵖ) (E := RadicalTensor (E₁ := E₁) φ)
          ((radicalSpace φ).mkQ z) ((radicalSpace φ).mkQ w))
    _ = radicalInner φ ((radicalSpace φ).mkQ z) ((radicalSpace φ).mkQ w) := by
      simpa only [MulOpposite.unop_op] using
        congrArg MulOpposite.unop
          (radicalTensorCStarModule_inner φ
            ((radicalSpace φ).mkQ z) ((radicalSpace φ).mkQ w))
    _ = balancedInner φ z w := radicalInner_mkQ_mkQ φ z w

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

For x, x′ ∈ E₁ and y ∈ E₂, the completed pure map satisfies pure(x+x′,y) = pure(x,y) +
pure(x′,y).
-/
@[simp]
theorem completedPure_add_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x x' : E₁) (y : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    completedPure φ (x + x') y = completedPure φ x y + completedPure φ x' y := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  simp only [completedPure, balancedPure_add_left, map_add]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

For x ∈ E₁ and y, y′ ∈ E₂, the completed pure map satisfies pure(x,y+y′) = pure(x,y) +
pure(x,y′).
-/
@[simp]
theorem completedPure_add_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : E₁) (y y' : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    completedPure φ x (y + y') = completedPure φ x y + completedPure φ x y' := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  simp only [completedPure, balancedPure_add_right, map_add]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

For c ∈ ℂ, x ∈ E₁ and y ∈ E₂, the completed pure map satisfies pure(cx,y) = c pure(x,y).
-/
@[simp]
theorem completedPure_smul_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (c : ℂ) (x : E₁) (y : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    completedPure φ (c • x) y = c • completedPure φ x y := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  simp only [completedPure, balancedPure_smul_left, map_smul]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

For c ∈ ℂ, x ∈ E₁ and y ∈ E₂, the completed pure map satisfies pure(x,cy) = c pure(x,y).
-/
@[simp]
theorem completedPure_smul_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (c : ℂ) (x : E₁) (y : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    completedPure φ x (c • y) = c • completedPure φ x y := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  simp only [completedPure, balancedPure_smul_right, map_smul]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

For x ∈ E₁, b ∈ B₁ and y ∈ E₂, completed pure vectors satisfy pure(xb,y) = pure(x,φ(b)y).
-/
@[simp]
theorem completedPure_balance
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : E₁) (b : B₁) (y : E₂) :
    completedPure φ (x <• b) y = completedPure φ x (φ b y) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  simp only [completedPure, balancedPure_balance]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

For x ∈ E₁, y ∈ E₂ and b ∈ B₂, completed pure vectors satisfy pure(x,yb) = pure(x,y)b.
-/
theorem completedPure_right_smul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : E₁) (y : E₂) (b : B₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    completedPure φ x (y <• b) = completedPure φ x y <• b := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  simpa only [completedPure, balancedRightSMul_pure] using
    completedFromBalanced_right_smul φ (balancedPure φ x y) b

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

For x, y ∈ E₁ and u, v ∈ E₂, the completed inner product satisfies ⟨pure(x,u),pure(y,v)⟩ =
⟨u,φ(⟨x,y⟩)v⟩.
-/
theorem rightInner_completedPure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x y : E₁) (u v : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) :=
      completedCStarModule φ;
    rightInner (B := B₂) (completedPure φ x u) (completedPure φ y v) =
      rightInner (B := B₂) u (φ (rightInner (B := B₁) x y) v) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) :=
    completedCStarModule φ
  simpa only [completedPure, balancedInner_pure_pure] using
    completedFromBalanced_inner φ (balancedPure φ x u) (balancedPure φ y v)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

For arbitrary finite index sets I and J, the inner product of ∑ᵢ pure(xᵢ,uᵢ) and ∑ⱼ pure(yⱼ,vⱼ)
is ∑ᵢ ∑ⱼ ⟨uᵢ,φ(⟨xᵢ,yⱼ⟩)vⱼ⟩, including empty index sets.
-/
theorem rightInner_sum_completedPure_sum_completedPure
    {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : I → E₁) (u : I → E₂) (y : J → E₁) (v : J → E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) :=
      completedCStarModule φ;
    rightInner (B := B₂) (∑ i, completedPure φ (x i) (u i))
        (∑ j, completedPure φ (y j) (v j)) =
      ∑ i, ∑ j, rightInner (B := B₂) (u i)
        (φ (rightInner (B := B₁) (x i) (y j)) (v j)) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) :=
    completedCStarModule φ
  have hx : (∑ i, completedPure φ (x i) (u i)) =
      completedFromBalanced φ (∑ i, balancedPure φ (x i) (u i)) := by
    simp only [completedPure, map_sum]
  have hy : (∑ j, completedPure φ (y j) (v j)) =
      completedFromBalanced φ (∑ j, balancedPure φ (y j) (v j)) := by
    simp only [completedPure, map_sum]
  rw [hx, hy, completedFromBalanced_inner, balancedInner_sum_pure_sum_pure]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

The completed pure vectors have dense complex-linear span in the completed internal tensor.
-/
theorem completedPure_dense_span
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    Dense (Submodule.span ℂ
      (Set.range fun p : E₁ × E₂ => completedPure φ p.1 p.2) :
        Set (CompletedTensor (E₁ := E₁) φ)) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let S : Submodule ℂ (CompletedTensor (E₁ := E₁) φ) :=
    Submodule.span ℂ (Set.range fun p : E₁ × E₂ => completedPure φ p.1 p.2)
  let f : BalancedTensor (E₁ := E₁) φ →ₗ[ℂ] CompletedTensor (E₁ := E₁) φ :=
    completedFromBalanced φ
  have htop : (⊤ : Submodule ℂ (BalancedTensor (E₁ := E₁) φ)) ≤ S.comap f := by
    rw [← balancedPure_span_eq_top φ]
    apply Submodule.span_le.2
    rintro _ ⟨p, rfl⟩
    change f (balancedPure φ p.1 p.2) ∈ S
    change completedPure φ p.1 p.2 ∈ S
    exact Submodule.subset_span ⟨p, rfl⟩
  have himage :
      Set.range ((↑) : RadicalTensor (E₁ := E₁) φ →
        UniformSpace.Completion (RadicalTensor (E₁ := E₁) φ)) ⊆
      (S : Set (CompletedTensor (E₁ := E₁) φ)) := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
    have hz := htop (show z ∈ (⊤ : Submodule ℂ (BalancedTensor (E₁ := E₁) φ)) from trivial)
    change f z ∈ S at hz
    apply (SetLike.mem_coe (p := S)).mpr
    rw [← completedFromBalanced_apply φ z]
    exact hz
  exact Dense.mono himage UniformSpace.Completion.denseRange_coe

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂.

The completed pure map satisfies all defining internal-tensor linearity, balancing,
right-action, inner-product and dense-span properties.
-/
theorem completed_isModel
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) :=
      completedCStarModule φ;
    IsModel φ (completedPure (E₁ := E₁) φ) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) :=
    completedCStarModule φ
  exact ⟨completedPure_add_left φ, completedPure_add_right φ,
    completedPure_smul_left φ, completedPure_smul_right φ,
    completedPure_balance φ, completedPure_right_smul φ,
    rightInner_completedPure φ, completedPure_dense_span φ⟩

end CStarModule.InternalTensorProduct
