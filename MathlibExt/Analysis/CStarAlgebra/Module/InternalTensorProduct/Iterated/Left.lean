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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Iterated

/-!
# Left-associated completed internal tensors

For complete right modules `Eᵢ` over nonunital C-star algebras `Bᵢ` with star-compatible
opposite orders and complex nonunital star representations `φ : B₁ → End_(B₂)(E₂)` and `χ : B₂ →
End_(B₃)(E₃)`, first form `E₁ ⊗_φ E₂` as a right `B₂`-module. Its internal tensor with `E₃`
through `χ` gives `(E₁ ⊗_φ E₂) ⊗_χ E₃`.

Pure triples `L(x,y,z) = (x⊗y)⊗z` are complex-trilinear and satisfy `L(x <• b,y,z) =
L(x,φ(b)y,z)` and `L(x,y <• c,z) = L(x,y,χ(c)z)`. The right `B₃` action is on the last factor.
The construction uses the completed coefficient inner-product norms and permits zero algebras,
modules and representations.
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
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]
variable {E₃ : Type uE₃} [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
  [SMul B₃ᵐᵒᵖ E₃] [CStarModule B₃ᵐᵒᵖ E₃] [CompleteSpace E₃]

/-- **Left-associated internal tensor carrier.** Let `Eᵢ` be complete right modules over nonunital
C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ → End_(B₂)(E₂)` and `χ
: B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. form `(E₁ ⊗_φ E₂) ⊗_χ E₃` by
using the first completed tensor as the right `B₂`-module in the second internal tensor. -/
abbrev LeftAssociatedCompletedTensor
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) : Type (max uE₁ uE₂ uE₃) :=
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  CompletedTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ

/-- **Pure vector of the left-associated tensor.** Let `Eᵢ` be complete right modules over
nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms.
`leftAssociatedCompletedPure φ χ x y z` is the twice-completed pure tensor `(x⊗_φ y)⊗_χ z`. -/
def leftAssociatedCompletedPure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃)
    (x : E₁) (y : E₂) (z : E₃) : LeftAssociatedCompletedTensor (E₁ := E₁) φ χ := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  exact completedPure χ (completedPure φ x y) z

/-- **Nested formula for a left-associated pure tensor.** Let `Eᵢ` be complete right modules over
nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms.
`leftAssociatedCompletedPure φ χ x y z = completedPure χ (completedPure φ x y) z`. -/
theorem leftAssociatedCompletedPure_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x y z = completedPure χ (completedPure φ x y) z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  rfl

/-- **Additivity in the first factor of a left-associated tensor.** Let `Eᵢ` be complete right
modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁
→ End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = leftAssociatedCompletedPure φ χ x y z`. Then `P(x+x',y,z) = P(x,y,z) + P(x',y,z)`. -/
@[simp]
theorem leftAssociatedCompletedPure_add_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x x' : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ (x + x') y z =
      leftAssociatedCompletedPure φ χ x y z + leftAssociatedCompletedPure φ χ x' y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ (x + x') y) z = completedPure χ (completedPure φ x y) z +
    completedPure χ (completedPure φ x' y) z
  rw [completedPure_add_left φ]
  exact completedPure_add_left χ (completedPure φ x y) (completedPure φ x' y) z

/-- **Additivity in the middle factor of a left-associated tensor.** Let `Eᵢ` be complete right
modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁
→ End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = leftAssociatedCompletedPure φ χ x y z`. Then `P(x,y+y',z) = P(x,y,z) + P(x,y',z)`. -/
@[simp]
theorem leftAssociatedCompletedPure_add_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y y' : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x (y + y') z =
      leftAssociatedCompletedPure φ χ x y z + leftAssociatedCompletedPure φ χ x y' z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ x (y + y')) z = completedPure χ (completedPure φ x y) z +
    completedPure χ (completedPure φ x y') z
  rw [completedPure_add_right φ]
  exact completedPure_add_left χ (completedPure φ x y) (completedPure φ x y') z

/-- **Additivity in the final factor of a left-associated tensor.** Let `Eᵢ` be complete right
modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁
→ End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = leftAssociatedCompletedPure φ χ x y z`. Then `P(x,y,z+z') = P(x,y,z) + P(x,y,z')`. -/
@[simp]
theorem leftAssociatedCompletedPure_add_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (z z' : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x y (z + z') =
      leftAssociatedCompletedPure φ χ x y z + leftAssociatedCompletedPure φ χ x y z' := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ x y) (z + z') = completedPure χ (completedPure φ x y) z +
    completedPure χ (completedPure φ x y) z'
  exact completedPure_add_right χ (completedPure φ x y) z z'

/-- **Complex scaling in the first factor of a left-associated tensor.** Let `Eᵢ` be complete
right modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ
: B₁ → End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = leftAssociatedCompletedPure φ χ x y z`. Then `P(c • x,y,z) = c • P(x,y,z)`. -/
@[simp]
theorem leftAssociatedCompletedPure_smul_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (c : ℂ) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ (c • x) y z = c • leftAssociatedCompletedPure φ χ x y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ (c • x) y) z = c • completedPure χ (completedPure φ x y) z
  rw [completedPure_smul_left φ]
  exact completedPure_smul_left χ c (completedPure φ x y) z

/-- **Complex scaling in the middle factor of a left-associated tensor.** Let `Eᵢ` be complete
right modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ
: B₁ → End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = leftAssociatedCompletedPure φ χ x y z`. Then `P(x,c • y,z) = c • P(x,y,z)`. -/
@[simp]
theorem leftAssociatedCompletedPure_smul_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (c : ℂ) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x (c • y) z = c • leftAssociatedCompletedPure φ χ x y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ x (c • y)) z = c • completedPure χ (completedPure φ x y) z
  rw [completedPure_smul_right φ]
  exact completedPure_smul_left χ c (completedPure φ x y) z

/-- **Complex scaling in the final factor of a left-associated tensor.** Let `Eᵢ` be complete
right modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ
: B₁ → End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = leftAssociatedCompletedPure φ χ x y z`. Then `P(x,y,c • z) = c • P(x,y,z)`. -/
@[simp]
theorem leftAssociatedCompletedPure_smul_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (c : ℂ) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x y (c • z) = c • leftAssociatedCompletedPure φ χ x y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ x y) (c • z) = c • completedPure χ (completedPure φ x y) z
  exact completedPure_smul_right χ c (completedPure φ x y) z

/-- **Zero in the first factor of a left-associated tensor.** Let `Eᵢ` be complete right modules
over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = leftAssociatedCompletedPure φ χ x y z`. Then `P(0,y,z) = 0`. -/
@[simp]
theorem leftAssociatedCompletedPure_zero_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ (0 : E₁) y z = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  simpa only [zero_smul] using
    leftAssociatedCompletedPure_smul_left φ χ (0 : ℂ) (0 : E₁) y z

/-- **Zero in the middle factor of a left-associated tensor.** Let `Eᵢ` be complete right modules
over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = leftAssociatedCompletedPure φ χ x y z`. Then `P(x,0,z) = 0`. -/
@[simp]
theorem leftAssociatedCompletedPure_zero_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x (0 : E₂) z = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  simpa only [zero_smul] using
    leftAssociatedCompletedPure_smul_middle φ χ (0 : ℂ) x (0 : E₂) z

/-- **Zero in the final factor of a left-associated tensor.** Let `Eᵢ` be complete right modules
over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ : B₁ →
End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = leftAssociatedCompletedPure φ χ x y z`. Then `P(x,y,0) = 0`. -/
@[simp]
theorem leftAssociatedCompletedPure_zero_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x y (0 : E₃) = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  simpa only [zero_smul] using
    leftAssociatedCompletedPure_smul_right φ χ (0 : ℂ) x y (0 : E₃)

/-- **Balancing the first coefficient action of a left-associated tensor.** Let `Eᵢ` be complete
right modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ
: B₁ → End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = leftAssociatedCompletedPure φ χ x y z`. Then `P(x <• b,y,z) = P(x,φ(b)y,z)`. -/
@[simp]
theorem leftAssociatedCompletedPure_balance_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (b : B₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ (x <• b) y z = leftAssociatedCompletedPure φ χ x (φ b y) z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ (x <• b) y) z =
    completedPure χ (completedPure φ x (φ b y)) z
  rw [completedPure_balance]

/-- **Balancing the second coefficient action of a left-associated tensor.** Let `Eᵢ` be complete
right modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ
: B₁ → End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = leftAssociatedCompletedPure φ χ x y z`. Then `P(x,y <• b,z) = P(x,y,χ(b)z)`. -/
@[simp]
theorem leftAssociatedCompletedPure_balance_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (b : B₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x (y <• b) z = leftAssociatedCompletedPure φ χ x y (χ b z) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ x (y <• b)) z =
    completedPure χ (completedPure φ x y) (χ b z)
  rw [completedPure_right_smul, completedPure_balance]

/-- **Right action in the final tensor factor of a left-associated tensor.** Let `Eᵢ` be complete
right modules over nonunital C-star algebras `Bᵢ` with star-compatible opposite orders. Let `φ
: B₁ → End_(B₂)(E₂)` and `χ : B₂ → End_(B₃)(E₃)` be complex nonunital star homomorphisms. Put
`P(x,y,z) = leftAssociatedCompletedPure φ χ x y z`. Then `P(x,y,z <• b) = P(x,y,z) <• b`. -/
@[simp]
theorem leftAssociatedCompletedPure_right_smul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (z : E₃) (b : B₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalRightAction χ;
    leftAssociatedCompletedPure φ χ x y (z <• b) = leftAssociatedCompletedPure φ χ x y z <• b := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalRightAction χ
  change completedPure χ (completedPure φ x y) (z <• b) =
    completedPure χ (completedPure φ x y) z <• b
  exact completedPure_right_smul χ (completedPure φ x y) z b

end CStarModule.InternalTensorProduct
