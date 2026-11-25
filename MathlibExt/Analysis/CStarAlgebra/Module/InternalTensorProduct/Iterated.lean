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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.MapLeft.Functoriality

/-!
# Right-associated completed internal tensors

For complete right modules `Eᵢ` over nonunital C-star algebras `Bᵢ` with star-compatible
opposite orders and complex nonunital star representations `φ : B₁ → End_(B₂)(E₂)` and `χ : B₂ →
End_(B₃)(E₃)`, the first coefficient acts on `E₂ ⊗_χ E₃` by `η(b)(y⊗z) = φ(b)y ⊗ z`.

Use this induced action to form `E₁ ⊗_η (E₂ ⊗_χ E₃)`. Its pure triples `R(x,y,z)` are
complex-trilinear, satisfy the two coefficient balancing relations, and carry the right `B₃`
action in their final factor. All norms are the completed coefficient inner-product norms. Zero
or degenerate representations are included.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped RightActions

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uB₃ uE₁ uE₂ uE₃

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {B₃ : Type uB₃} [NonUnitalCStarAlgebra B₃]
  [PartialOrder B₃ᵐᵒᵖ] [StarOrderedRing B₃ᵐᵒᵖ]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]
variable {E₃ : Type uE₃} [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
  [SMul B₃ᵐᵒᵖ E₃] [CStarModule B₃ᵐᵒᵖ E₃] [CompleteSpace E₃]

/-- **Induced coefficient action on an inner tensor.** Let `Eᵢ` be complete right modules over
nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. the star
homomorphism `η` on `E₂ ⊗_χ E₃` is determined by `η(b)(y⊗z) = φ(b)y ⊗ z`. -/
def inducedCompletedLeftAction
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ (CompletedTensor (E₁ := E₂) χ) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  exact (completedLeftStarAlgHom (E₁ := E₂) χ).toNonUnitalStarAlgHom.comp φ

omit [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ] in
/-- **Value of the induced coefficient representation.** Let `Eᵢ` be complete right modules over
nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms.
`inducedCompletedLeftAction φ χ b = completedLeftStarAlgHom χ (φ b)`. -/
theorem inducedCompletedLeftAction_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (b : B₁) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    inducedCompletedLeftAction φ χ b = completedLeftStarAlgHom χ (φ b) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  rfl

omit [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ] in
/-- **Induced coefficient action on a pure tensor.** Let `Eᵢ` be complete right modules over
nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms.
`η(b)(completedPure χ y z) = completedPure χ (φ b y) z`, where `η = inducedCompletedLeftAction
φ χ`. -/
@[simp]
theorem inducedCompletedLeftAction_completedPure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (b : B₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    inducedCompletedLeftAction φ χ b (completedPure χ y z) = completedPure χ (φ b y) z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  change completedLeftStarAlgHom χ (φ b) (completedPure χ y z) = completedPure χ (φ b y) z
  exact completedLeftStarAlgHom_pure χ (φ b) y z

omit [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ] in
/-- **Zero induced coefficient action.** Let `Eᵢ` be complete right modules over nonunital C-star
algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ → End_(B₂)(E₂)` and `χ : B₂ →
End_(B₃)(E₃)` be complex nonunital star homomorphisms. if the first representation is zero,
`inducedCompletedLeftAction 0 χ = 0`. -/
@[simp]
theorem inducedCompletedLeftAction_zero
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    inducedCompletedLeftAction (0 : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) χ = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  apply NonUnitalStarAlgHom.ext
  intro b
  change completedLeftStarAlgHom χ (0 : AdjointableOperator.End B₂ E₂) = 0
  exact map_zero (completedLeftStarAlgHom χ)

variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]

/-- **Right-associated internal tensor carrier.** Let `Eᵢ` be complete right modules over
nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. form `E₁
⊗_η (E₂ ⊗_χ E₃)`, with `η(b)(y⊗z) = φ(b)y⊗z`, by the two balanced radical quotients and norm
completions. -/
abbrev RightAssociatedCompletedTensor
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) : Type (max uE₁ uE₂ uE₃) :=
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  CompletedTensor (E₁ := E₁) (inducedCompletedLeftAction φ χ)

/-- **Pure vector of the right-associated tensor.** Let `Eᵢ` be complete right modules over
nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. this is `x
⊗_η (y ⊗_χ z)`, with `η` the induced coefficient action on the inner tensor. -/
def rightAssociatedCompletedPure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃)
    (x : E₁) (y : E₂) (z : E₃) : RightAssociatedCompletedTensor (E₁ := E₁) φ χ := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  exact completedPure η x (completedPure χ y z)

/-- **Nested formula for a right-associated pure tensor.** Let `Eᵢ` be complete right modules over
nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms.
`rightAssociatedCompletedPure φ χ x y z = completedPure η x (completedPure χ y z)`, where `η =
inducedCompletedLeftAction φ χ`. -/
theorem rightAssociatedCompletedPure_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x y z = completedPure η x (completedPure χ y z) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  rfl

/-- **Additivity in the first factor of a right-associated tensor.** Let `Eᵢ` be complete right
modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁
→ End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = rightAssociatedCompletedPure φ χ x y z`. Then `P(x+x',y,z) = P(x,y,z) +
P(x',y,z)`. -/
@[simp]
theorem rightAssociatedCompletedPure_add_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x x' : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ (x + x') y z =
      rightAssociatedCompletedPure φ χ x y z + rightAssociatedCompletedPure φ χ x' y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η (x + x') (completedPure χ y z) = completedPure η x (completedPure χ y z) +
    completedPure η x' (completedPure χ y z)
  exact completedPure_add_left η x x' (completedPure χ y z)

/-- **Additivity in the middle factor of a right-associated tensor.** Let `Eᵢ` be complete right
modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁
→ End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = rightAssociatedCompletedPure φ χ x y z`. Then `P(x,y+y',z) = P(x,y,z) +
P(x,y',z)`. -/
@[simp]
theorem rightAssociatedCompletedPure_add_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y y' : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x (y + y') z =
      rightAssociatedCompletedPure φ χ x y z + rightAssociatedCompletedPure φ χ x y' z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η x (completedPure χ (y + y') z) = completedPure η x (completedPure χ y z) +
    completedPure η x (completedPure χ y' z)
  rw [completedPure_add_left χ]
  exact completedPure_add_right η x (completedPure χ y z) (completedPure χ y' z)

/-- **Additivity in the final factor of a right-associated tensor.** Let `Eᵢ` be complete right
modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁
→ End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = rightAssociatedCompletedPure φ χ x y z`. Then `P(x,y,z+z') = P(x,y,z) +
P(x,y,z')`. -/
@[simp]
theorem rightAssociatedCompletedPure_add_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (z z' : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x y (z + z') =
      rightAssociatedCompletedPure φ χ x y z + rightAssociatedCompletedPure φ χ x y z' := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η x (completedPure χ y (z + z')) = completedPure η x (completedPure χ y z) +
    completedPure η x (completedPure χ y z')
  rw [completedPure_add_right χ]
  exact completedPure_add_right η x (completedPure χ y z) (completedPure χ y z')

/-- **Complex scaling in the first factor of a right-associated tensor.** Let `Eᵢ` be complete
right modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ
: B₁ → End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = rightAssociatedCompletedPure φ χ x y z`. Then `P(c • x,y,z) = c • P(x,y,z)`. -/
@[simp]
theorem rightAssociatedCompletedPure_smul_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (c : ℂ) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ (c • x) y z = c • rightAssociatedCompletedPure φ χ x y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η (c • x) (completedPure χ y z) = c • completedPure η x (completedPure χ y z)
  exact completedPure_smul_left η c x (completedPure χ y z)

/-- **Complex scaling in the middle factor of a right-associated tensor.** Let `Eᵢ` be complete
right modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ
: B₁ → End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = rightAssociatedCompletedPure φ χ x y z`. Then `P(x,c • y,z) = c • P(x,y,z)`. -/
@[simp]
theorem rightAssociatedCompletedPure_smul_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (c : ℂ) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x (c • y) z = c • rightAssociatedCompletedPure φ χ x y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η x (completedPure χ (c • y) z) = c • completedPure η x (completedPure χ y z)
  rw [completedPure_smul_left χ]
  exact completedPure_smul_right η c x (completedPure χ y z)

/-- **Complex scaling in the final factor of a right-associated tensor.** Let `Eᵢ` be complete
right modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ
: B₁ → End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = rightAssociatedCompletedPure φ χ x y z`. Then `P(x,y,c • z) = c • P(x,y,z)`. -/
@[simp]
theorem rightAssociatedCompletedPure_smul_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (c : ℂ) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x y (c • z) = c • rightAssociatedCompletedPure φ χ x y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η x (completedPure χ y (c • z)) = c • completedPure η x (completedPure χ y z)
  rw [completedPure_smul_right χ]
  exact completedPure_smul_right η c x (completedPure χ y z)

/-- **Zero in the first factor of a right-associated tensor.** Let `Eᵢ` be complete right modules
over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = rightAssociatedCompletedPure φ χ x y z`. Then `P(0,y,z) = 0`. -/
@[simp]
theorem rightAssociatedCompletedPure_zero_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ (0 : E₁) y z = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  simpa only [zero_smul] using
    rightAssociatedCompletedPure_smul_left φ χ (0 : ℂ) (0 : E₁) y z

/-- **Zero in the middle factor of a right-associated tensor.** Let `Eᵢ` be complete right modules
over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = rightAssociatedCompletedPure φ χ x y z`. Then `P(x,0,z) = 0`. -/
@[simp]
theorem rightAssociatedCompletedPure_zero_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x (0 : E₂) z = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  simpa only [zero_smul] using
    rightAssociatedCompletedPure_smul_middle φ χ (0 : ℂ) x (0 : E₂) z

/-- **Zero in the final factor of a right-associated tensor.** Let `Eᵢ` be complete right modules
over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = rightAssociatedCompletedPure φ χ x y z`. Then `P(x,y,0) = 0`. -/
@[simp]
theorem rightAssociatedCompletedPure_zero_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x y (0 : E₃) = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  simpa only [zero_smul] using
    rightAssociatedCompletedPure_smul_right φ χ (0 : ℂ) x y (0 : E₃)

/-- **Balancing the first coefficient action of a right-associated tensor.** Let `Eᵢ` be complete
right modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ
: B₁ → End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = rightAssociatedCompletedPure φ χ x y z`. Then `P(x <• b,y,z) = P(x,φ(b)y,z)`. -/
@[simp]
theorem rightAssociatedCompletedPure_balance_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (b : B₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ (x <• b) y z = rightAssociatedCompletedPure φ χ x (φ b y) z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η (x <• b) (completedPure χ y z) =
    completedPure η x (completedPure χ (φ b y) z)
  rw [completedPure_balance]
  rw [inducedCompletedLeftAction_completedPure]

/-- **Balancing the second coefficient action of a right-associated tensor.** Let `Eᵢ` be complete
right modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ
: B₁ → End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = rightAssociatedCompletedPure φ χ x y z`. Then `P(x,y <• b,z) = P(x,y,χ(b)z)`. -/
@[simp]
theorem rightAssociatedCompletedPure_balance_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (b : B₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x (y <• b) z = rightAssociatedCompletedPure φ χ x y (χ b z) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η x (completedPure χ (y <• b) z) =
    completedPure η x (completedPure χ y (χ b z))
  rw [completedPure_balance]

/-- **Right action in the final tensor factor of a right-associated tensor.** Let `Eᵢ` be complete
right modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ
: B₁ → End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = rightAssociatedCompletedPure φ χ x y z`. Then `P(x,y,z <• b) = P(x,y,z) <• b`. -/
@[simp]
theorem rightAssociatedCompletedPure_right_smul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (z : E₃) (b : B₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₁) η) := radicalRightAction η;
    rightAssociatedCompletedPure φ χ x y (z <• b) = rightAssociatedCompletedPure φ χ x y z <• b := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₁) η) := radicalRightAction η
  change completedPure η x (completedPure χ y (z <• b)) =
    completedPure η x (completedPure χ y z) <• b
  rw [completedPure_right_smul χ]
  exact completedPure_right_smul η x (completedPure χ y z) b

end CStarModule.InternalTensorProduct
