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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.ModelComparison.Algebraic
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Completion
public import MathlibExt.Analysis.CStarAlgebra.Module.Unitary
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The actual unitary from the literal tensor to a supplied completed model

The independently constructed canonical tensor maps into the given real
IsModel by the complex tensor/quotient universal properties. Its proved
inner identity yields an isometry. Stock completion, closed isometric
range and the supplied dense complex span prove actual surjectivity.
A unitary equivalence is constructed, never assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped RightActions

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂ uF

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
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
product, and has pure values with dense complex span. The radical comparison extends to a
complex-linear isometry from the completed internal tensor product into F. -/
def completedModelIsometry
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
    CompletedTensor (E₁ := E₁) φ →ₗᵢ[ℂ] F := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  exact (radicalModelIsometry φ T hT).fromCompletion

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. On the image of a radical-quotient
vector, the extended isometry has its radical comparison value. -/
@[simp]
theorem completedModelIsometry_coe
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (q : RadicalTensor (E₁ := E₁) φ) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
    completedModelIsometry φ T hT (q : CompletedTensor (E₁ := E₁) φ) =
      radicalModelMap φ T hT q := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  simp only [completedModelIsometry, LinearIsometry.fromCompletion_apply_coe,
    radicalModelIsometry_apply]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. On the completed image of a balanced
tensor, the isometry has its balanced comparison value. -/
@[simp]
theorem completedModelIsometry_fromBalanced
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (z : BalancedTensor (E₁ := E₁) φ) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
    completedModelIsometry φ T hT (completedFromBalanced φ z) =
      balancedModelMap φ T hT z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  rw [completedFromBalanced_apply, completedModelIsometry_coe, radicalModelMap_mkQ]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The completed isometry sends the
elementary completed tensor of x and y to T(x,y). -/
@[simp]
theorem completedModelIsometry_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (x : E₁) (y : E₂) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
    completedModelIsometry φ T hT (completedPure φ x y) = T x y := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  rw [completedPure_apply, completedModelIsometry_coe, radicalModelMap_pure]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The completed isometry preserves the B₂-
valued inner product. -/
theorem completedModelIsometry_inner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (z w : CompletedTensor (E₁ := E₁) φ) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    rightInner (B := B₂) (completedModelIsometry φ T hT z)
        (completedModelIsometry φ T hT w) =
      rightInner (B := B₂) z w := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  have hl : Continuous fun p :
      CompletedTensor (E₁ := E₁) φ × CompletedTensor (E₁ := E₁) φ =>
      rightInner (B := B₂) (completedModelIsometry φ T hT p.1)
        (completedModelIsometry φ T hT p.2) :=
    (CStarModule.continuous_rightInner (B := B₂) (E := F)).comp
      (((completedModelIsometry φ T hT).continuous.comp continuous_fst).prodMk
        ((completedModelIsometry φ T hT).continuous.comp continuous_snd))
  have hr : Continuous fun p :
      CompletedTensor (E₁ := E₁) φ × CompletedTensor (E₁ := E₁) φ =>
      rightInner (B := B₂) p.1 p.2 :=
    CStarModule.continuous_rightInner (B := B₂) (E := CompletedTensor (E₁ := E₁) φ)
  refine UniformSpace.Completion.induction_on₂ z w (isClosed_eq hl hr) ?_
  intro q v
  obtain ⟨q, rfl⟩ := (radicalSpace φ).mkQ_surjective q
  obtain ⟨v, rfl⟩ := (radicalSpace φ).mkQ_surjective v
  have hq : ((radicalSpace φ).mkQ q : CompletedTensor (E₁ := E₁) φ) =
      completedFromBalanced φ q := (completedFromBalanced_apply φ q).symm
  have hv : ((radicalSpace φ).mkQ v : CompletedTensor (E₁ := E₁) φ) =
      completedFromBalanced φ v := (completedFromBalanced_apply φ v).symm
  rw [hq, hv, completedModelIsometry_fromBalanced, completedModelIsometry_fromBalanced,
    completedFromBalanced_inner]
  exact balancedModelMap_inner φ T hT q v

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. Density of the span of the values of T
implies that the completed isometry is onto F. -/
theorem completedModelIsometry_surjective
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
    Function.Surjective (completedModelIsometry φ T hT) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let f : CompletedTensor (E₁ := E₁) φ →ₗᵢ[ℂ] F := completedModelIsometry φ T hT
  let R : Submodule ℂ F := f.toLinearMap.range
  let S : Submodule ℂ F := Submodule.span ℂ (Set.range fun p : E₁ × E₂ => T p.1 p.2)
  have hSR : S ≤ R := by
    apply Submodule.span_le.2
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact ⟨completedPure φ x y, completedModelIsometry_pure φ T hT x y⟩
  have hClosed : IsClosed (R : Set F) := by
    change IsClosed (Set.range f)
    exact f.antilipschitzWith.isClosed_range f.isometry.uniformContinuous
  have hDense : Dense (S : Set F) := hT.2.2.2.2.2.2.2
  have hTop : R = ⊤ := by
    apply top_unique
    calc
      ⊤ = S.topologicalClosure :=
        ((Submodule.dense_iff_topologicalClosure_eq_top).mp hDense).symm
      _ ≤ R.topologicalClosure := Submodule.topologicalClosure_mono hSR
      _ = R := hClosed.submodule_topologicalClosure_eq
  exact (LinearMap.range_eq_top).mp hTop

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The completed internal tensor product is
unitarily equivalent, as a right B₂-module, to F by the extension of T. -/
def completedTensorModelUnitary
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    UnitaryEquiv B₂ (CompletedTensor (E₁ := E₁) φ) F := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let e : CompletedTensor (E₁ := E₁) φ ≃ₗᵢ[ℂ] F :=
    LinearIsometryEquiv.ofSurjective (completedModelIsometry φ T hT)
      (completedModelIsometry_surjective φ T hT)
  exact UnitaryEquiv.ofLinearIsometryEquiv e (by
    intro z w
    simpa only [e, LinearIsometryEquiv.coe_ofSurjective] using
      completedModelIsometry_inner φ T hT z w)

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The forward value of this unitary
equivalence is the completed comparison isometry. -/
theorem completedTensorModelUnitary_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (z : CompletedTensor (E₁ := E₁) φ) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    completedTensorModelUnitary φ T hT z = completedModelIsometry φ T hT z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  simp only [completedTensorModelUnitary, UnitaryEquiv.ofLinearIsometryEquiv_apply,
    LinearIsometryEquiv.coe_ofSurjective]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The unitary equivalence sends the
elementary completed tensor of x and y to T(x,y). -/
@[simp]
theorem completedTensorModelUnitary_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (x : E₁) (y : E₂) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    completedTensorModelUnitary φ T hT (completedPure φ x y) = T x y := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  rw [completedTensorModelUnitary_apply, completedModelIsometry_pure]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The inverse unitary sends T(x,y) to the
elementary completed tensor of x and y. -/
@[simp]
theorem completedTensorModelUnitary_symm_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (x : E₁) (y : E₂) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    (completedTensorModelUnitary φ T hT).symm (T x y) = completedPure φ x y := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  rw [← completedTensorModelUnitary_pure φ T hT x y, UnitaryEquiv.symm_apply_apply]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Let F be a complete right Hilbert B₂-module. Suppose T from E₁ × E₂ to F is complex-
bilinear, balanced over B₁, right B₂-linear, preserves the coefficient-valued tensor inner
product, and has pure values with dense complex span. The unitary comparison commutes with the
right B₂ action. -/
theorem completedTensorModelUnitary_right_smul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (T : E₁ → E₂ → F) (hT : IsModel φ T) (z : CompletedTensor (E₁ := E₁) φ) (b : B₂) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    completedTensorModelUnitary φ T hT (z <• b) =
      completedTensorModelUnitary φ T hT z <• b := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  change (completedTensorModelUnitary φ T hT).toAdjointable (z <• b) =
    (completedTensorModelUnitary φ T hT).toAdjointable z <• b
  exact AdjointableOperator.map_right_smul _ z b

end CStarModule.InternalTensorProduct
