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
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct

/-!
# The genuine algebraic map to a supplied internal-tensor model

The canonical tensor carrier is independently constructed. A real full
IsModel supplies its own pure map into F; complex tensor and quotient
universal properties construct the comparison into that given model.
Its actual inner formula proves radical annihilation and norm preservation.
No canonical backend, norm or output equivalence is obtained from F.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped TensorProduct

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂ uF

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [SMul B₂ᵐᵒᵖ F] [CStarModule B₂ᵐᵒᵖ F] [CompleteSpace F]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The complex-bilinear map T induces a
complex-linear map from the algebraic complex tensor product into F. -/
def rawModelMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) :
    AlgebraicTensor E₁ E₂ →ₗ[ℂ] F :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := T x
          map_add' := hT.2.1 x
          map_smul' := fun c y => hT.2.2.2.1 c x y }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        exact hT.1 x y z
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro y
        exact hT.2.2.1 c x y }

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. This algebraic comparison sends the
elementary tensor of x and y to T(x,y). -/
@[simp]
theorem rawModelMap_tmul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (x : E₁) (y : E₂) :
    rawModelMap φ T hT (x ⊗ₜ[ℂ] y) = T x y := by
  rw [rawModelMap, TensorProduct.lift.tmul]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. Every balancing relation lies in the
kernel of the algebraic comparison. -/
theorem balancingSpan_le_ker_rawModelMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) :
    balancingSpan (E₁ := E₁) φ ≤ LinearMap.ker (rawModelMap φ T hT) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨x, b, y⟩, rfl⟩
  change rawModelMap φ T hT (balanceRelation φ x b y) = 0
  rw [balanceRelation, map_sub, rawModelMap_tmul, rawModelMap_tmul,
    hT.2.2.2.2.1, sub_self]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The algebraic comparison therefore
defines a complex-linear map from the B₁-balanced tensor quotient into F. -/
def balancedModelMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) :
    BalancedTensor (E₁ := E₁) φ →ₗ[ℂ] F :=
  (balancingSpan φ).liftQ (rawModelMap φ T hT) (balancingSpan_le_ker_rawModelMap φ T hT)

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The balanced comparison on the class of
an algebraic tensor equals its algebraic comparison value. -/
theorem balancedModelMap_mkQ
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (z : AlgebraicTensor E₁ E₂) :
    balancedModelMap φ T hT ((balancingSpan φ).mkQ z) = rawModelMap φ T hT z := by
  simp only [balancedModelMap, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The balanced comparison sends an
elementary balanced tensor to T(x,y). -/
@[simp]
theorem balancedModelMap_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (x : E₁) (y : E₂) :
    balancedModelMap φ T hT (balancedPure φ x y) = T x y := by
  simp only [balancedPure, balancedModelMap_mkQ, rawModelMap_tmul]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The algebraic comparison preserves the
B₂-valued tensor inner product for every pair of algebraic tensors. -/
theorem rawModelMap_inner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T)
    (z w : AlgebraicTensor E₁ E₂) :
    rightInner (B := B₂) (rawModelMap φ T hT z) (rawModelMap φ T hT w) =
      rawInner φ z w := by
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    induction w using TensorProduct.inductionOn with
    | tmul y v =>
      simpa only [rawModelMap_tmul, rawInner_tmul_tmul] using
        hT.2.2.2.2.2.2.1 x y u v
    | add w w' hw hw' =>
      simp only [map_add, rightInner_add_right, hw, hw']
  | add z z' hz hz' =>
    simp only [map_add, rightInner_add_left, LinearMap.add_apply, hz, hz']

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The balanced comparison preserves the
B₂-valued inner product for every pair of balanced tensors. -/
theorem balancedModelMap_inner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T)
    (z w : BalancedTensor (E₁ := E₁) φ) :
    rightInner (B := B₂) (balancedModelMap φ T hT z) (balancedModelMap φ T hT w) =
      balancedInner φ z w := by
  obtain ⟨z, rfl⟩ := (balancingSpan φ).mkQ_surjective z
  obtain ⟨w, rfl⟩ := (balancingSpan φ).mkQ_surjective w
  simpa only [balancedModelMap_mkQ, balancedInner_mkQ_mkQ] using
    rawModelMap_inner φ T hT z w

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. Every vector in the radical of the
balanced inner form maps to zero in F. -/
theorem radicalSpace_le_ker_balancedModelMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) :
    radicalSpace (E₁ := E₁) φ ≤ LinearMap.ker (balancedModelMap φ T hT) := by
  intro z hz
  change balancedModelMap φ T hT z = 0
  apply (CStarModule.inner_self (A := B₂ᵐᵒᵖ) (E := F)).mp
  apply MulOpposite.unop_injective
  have hzero : rightInner (B := B₂)
      (balancedModelMap φ T hT z) (balancedModelMap φ T hT z) = 0 :=
    (balancedModelMap_inner φ T hT z z).trans ((mem_radicalSpace_iff φ z).mp hz z)
  simpa only [CStarModule.rightInner, MulOpposite.unop_zero] using hzero

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The balanced comparison defines a
complex-linear map from the radical quotient into F. -/
def radicalModelMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) :
    RadicalTensor (E₁ := E₁) φ →ₗ[ℂ] F :=
  (radicalSpace φ).liftQ (balancedModelMap φ T hT) (radicalSpace_le_ker_balancedModelMap φ T hT)

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The radical comparison evaluated on a
quotient class equals the balanced comparison of its representative. -/
theorem radicalModelMap_mkQ
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (z : BalancedTensor (E₁ := E₁) φ) :
    radicalModelMap φ T hT ((radicalSpace φ).mkQ z) = balancedModelMap φ T hT z := by
  simp only [radicalModelMap, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The radical comparison sends the class
of an elementary balanced tensor to T(x,y). -/
theorem radicalModelMap_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (x : E₁) (y : E₂) :
    radicalModelMap φ T hT ((radicalSpace φ).mkQ (balancedPure φ x y)) = T x y := by
  simp only [radicalModelMap_mkQ, balancedModelMap_pure]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The radical comparison preserves the B₂-
valued inner product for every pair of radical-quotient vectors. -/
theorem radicalModelMap_inner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T)
    (z w : RadicalTensor (E₁ := E₁) φ) :
    rightInner (B := B₂) (radicalModelMap φ T hT z) (radicalModelMap φ T hT w) =
      radicalInner φ z w := by
  obtain ⟨z, rfl⟩ := (radicalSpace φ).mkQ_surjective z
  obtain ⟨w, rfl⟩ := (radicalSpace φ).mkQ_surjective w
  simpa only [radicalModelMap_mkQ, radicalInner_mkQ_mkQ] using
    balancedModelMap_inner φ T hT z w

variable [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The radical comparison preserves the
norm defined by the coefficient-valued inner product. -/
theorem radicalModelMap_norm
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (q : RadicalTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    ‖radicalModelMap φ T hT q‖ = ‖q‖ := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  calc
    ‖radicalModelMap φ T hT q‖ =
        Real.sqrt ‖rightInner (B := B₂) (radicalModelMap φ T hT q) (radicalModelMap φ T hT q)‖ :=
      AdjointableOperator.norm_eq_sqrt_norm_rightInner _
    _ = Real.sqrt ‖radicalInner φ q q‖ := by rw [radicalModelMap_inner]
    _ = ‖q‖ := (radicalTensorNormedAddCommGroup_norm φ q).symm

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The radical comparison is a complex-
linear isometry into F. -/
def radicalModelIsometry
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    RadicalTensor (E₁ := E₁) φ →ₗᵢ[ℂ] F := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  exact { toLinearMap := radicalModelMap φ T hT
          norm_map' := radicalModelMap_norm φ T hT }

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. This linear isometry has the same value
as the radical comparison. -/
@[simp]
theorem radicalModelIsometry_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (q : RadicalTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedSpace φ;
    radicalModelIsometry φ T hT q = radicalModelMap φ T hT q := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  rfl

end CStarModule.InternalTensorProduct
