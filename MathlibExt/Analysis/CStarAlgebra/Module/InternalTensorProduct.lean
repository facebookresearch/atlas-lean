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

public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable

/-!
# Internal tensor-product models for right C-star modules

This file records the characteristic interface for a completed balanced
internal tensor product.  It includes complex bilinearity, balancing, the
right action, the pure-tensor inner-product formula, and density.  These laws
rule out both arbitrary Hilbert modules and the ordinary tensor product over
the commutative scalar field.
-/

@[expose] public section

open Set
open scoped RightActions

namespace CStarModule

namespace InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂ uX

variable {B₁ : Type uB₁} {B₂ : Type uB₂}
variable {E₁ : Type uE₁} {E₂ : Type uE₂} {X : Type uX}
variable [NonUnitalCStarAlgebra B₁] [PartialOrder B₁ᵐᵒᵖ]
variable [NonUnitalCStarAlgebra B₂] [PartialOrder B₂ᵐᵒᵖ]
variable [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [SMul B₁ᵐᵒᵖ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [SMul B₂ᵐᵒᵖ E₂]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul B₂ᵐᵒᵖ X]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, each with a partial order on its
opposite algebra. Let E₁ be a complete normed right inner-product B₁-module, and let E₂ and X be
complete normed right inner-product B₂-modules, all with compatible complex normed-space
structures. Let φ be a nonunital complex star representation of B₁ by adjointable endomorphisms
of E₂.

A map pure : E₁ × E₂ → X represents the completed internal tensor product if it is
complex-linear in each argument, balances the B₁-actions, respects the B₂-action, satisfies
⟨pure(x,u), pure(y,v)⟩ = ⟨u, φ(⟨x,y⟩)v⟩, and its pure vectors have dense complex-linear span in
X.
-/
def IsModel
    [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
    [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]
    [CStarModule B₂ᵐᵒᵖ X] [CompleteSpace X]
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (pure : E₁ → E₂ → X) : Prop :=
  (∀ x y z, pure (x + y) z = pure x z + pure y z) ∧
  (∀ x y z, pure x (y + z) = pure x y + pure x z) ∧
  (∀ (c : ℂ) x y, pure (c • x) y = c • pure x y) ∧
  (∀ (c : ℂ) x y, pure x (c • y) = c • pure x y) ∧
  (∀ (x : E₁) (b : B₁) (y : E₂),
    pure (x <• b) y = pure x (φ b y)) ∧
  (∀ (x : E₁) (y : E₂) (b : B₂),
    pure x (y <• b) = pure x y <• b) ∧
  (∀ (x₁ y₁ : E₁) (x₂ y₂ : E₂),
    rightInner (B := B₂) (pure x₁ x₂) (pure y₁ y₂) =
      rightInner (B := B₂) x₂
        (φ (rightInner (B := B₁) x₁ y₁) y₂)) ∧
  Dense (Submodule.span ℂ
    (Set.range fun p : E₁ × E₂ ↦ pure p.1 p.2) : Set X)

end InternalTensorProduct

end CStarModule
