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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.MapLeft
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.PreHilbert

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Bounded first-factor maps on the literal internal tensor quotient

A square complement is constructed in the complete SOURCE End algebra.
The actual mapped tensor Gram form gives a positive remainder in the
unchanged caller coefficient order. Thus the already constructed radical
map is bounded for its genuine self-inner norm.

The quotient's normed dictionaries are the existing pre-Hilbert factories.
No tensor model, bound, norm, completed operator or faithfulness is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped TensorProduct RightActions

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

omit [CompleteSpace F₁] in
private theorem leftSquareComplement (L : AdjointableOperator B₁ E₁ F₁) :
    ∃ S : AdjointableOperator.End B₁ E₁, ∀ x : E₁,
      L.adjoint (L x) + S.adjoint (S x) = (‖L‖ ^ 2 : ℝ) • x := by
  let : PartialOrder (AdjointableOperator.End B₁ E₁) :=
    CStarAlgebra.spectralOrder _
  let : StarOrderedRing (AdjointableOperator.End B₁ E₁) :=
    CStarAlgebra.spectralOrderedRing _
  let K : AdjointableOperator.End B₁ E₁ := L.adjointOperator.comp L
  let r : ℝ := ‖L‖ ^ 2
  have hK : IsSelfAdjoint K := by
    change K.adjointOperator = K
    dsimp only [K]
    rw [AdjointableOperator.comp_adjointOperator,
      AdjointableOperator.adjointOperator_adjointOperator]
  have hKnorm : ‖K‖ = r := by
    simpa only [K, r, pow_two] using AdjointableOperator.norm_adjoint_comp_self L
  have hKle : K ≤ algebraMap ℝ (AdjointableOperator.End B₁ E₁) r := by
    simpa only [hKnorm] using IsSelfAdjoint.le_algebraMap_norm_self K hK
  let d : AdjointableOperator.End B₁ E₁ :=
    algebraMap ℝ (AdjointableOperator.End B₁ E₁) r - K
  have hd : 0 ≤ d := sub_nonneg.mpr hKle
  let S : AdjointableOperator.End B₁ E₁ := CFC.sqrt d
  have hs : star S * S = d := by
    dsimp only [S]
    rw [(CFC.sqrt_nonneg d).star_eq]
    exact CFC.sqrt_mul_sqrt_self d hd
  have hSquare : K + star S * S =
      algebraMap ℝ (AdjointableOperator.End B₁ E₁) r := by
    rw [add_comm K _, hs]
    exact sub_add_cancel _ _
  refine ⟨S, ?_⟩
  intro x
  have h := congrArg (fun T : AdjointableOperator.End B₁ E₁ => T x) hSquare
  simpa only [K, r, AdjointableOperator.add_apply,
    AdjointableOperator.comp_apply, AdjointableOperator.adjointOperator_apply,
    AdjointableOperator.mul_apply, AdjointableOperator.star_apply,
    IsScalarTower.algebraMap_apply ℝ ℂ (AdjointableOperator.End B₁ E₁),
    AdjointableOperator.algebraMap_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ)] using h

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] in
private theorem rawLeftMap_squareSplit
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁)
    (S : AdjointableOperator.End B₁ E₁)
    (hSquare : ∀ x : E₁, L.adjoint (L x) + S.adjoint (S x) = (‖L‖ ^ 2 : ℝ) • x)
    (z w : AlgebraicTensor E₁ E₂) :
    rawInner φ (rawLeftMap L z) (rawLeftMap L w) +
        rawInner φ (rawLeftMap S z) (rawLeftMap S w) =
      (‖L‖ ^ 2 : ℝ) • rawInner φ z w := by
  have hCoeff (x y : E₁) :
      rightInner (B := B₁) (L x) (L y) + rightInner (B := B₁) (S x) (S y) =
        (‖L‖ ^ 2 : ℝ) • rightInner (B := B₁) x y := by
    rw [L.adjoint_inner, S.adjoint_inner, ← rightInner_add_right, hSquare]
    calc
      rightInner (B := B₁) x ((‖L‖ ^ 2 : ℝ) • y) =
          rightInner (B := B₁) x (((‖L‖ ^ 2 : ℝ) : ℂ) • y) :=
        congrArg (fun v : E₁ => rightInner (B := B₁) x v)
          (RCLike.real_smul_eq_coe_smul (K := ℂ) (‖L‖ ^ 2) y)
      _ = ((‖L‖ ^ 2 : ℝ) : ℂ) • rightInner (B := B₁) x y :=
        rightInner_smul_right (B := B₁) ((‖L‖ ^ 2 : ℝ) : ℂ) x y
      _ = (‖L‖ ^ 2 : ℝ) • rightInner (B := B₁) x y :=
        (RCLike.real_smul_eq_coe_smul (K := ℂ) (‖L‖ ^ 2)
          (rightInner (B := B₁) x y)).symm
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    induction w using TensorProduct.inductionOn with
    | tmul y v =>
      simp only [rawLeftMap_tmul, rawInner_tmul_tmul]
      calc
        _ = rightInner (B := B₂) u
            ((φ (rightInner (B := B₁) (L x) (L y)) +
              φ (rightInner (B := B₁) (S x) (S y))) v) := by
          rw [AdjointableOperator.add_apply, rightInner_add_right]
        _ = rightInner (B := B₂) u
            (φ (rightInner (B := B₁) (L x) (L y) +
              rightInner (B := B₁) (S x) (S y)) v) := by rw [map_add]
        _ = rightInner (B := B₂) u
            (φ (((‖L‖ ^ 2 : ℝ) : ℂ) • rightInner (B := B₁) x y) v) := by
          exact congrArg (fun a : B₁ => rightInner (B := B₂) u (φ a v))
            ((hCoeff x y).trans
              (RCLike.real_smul_eq_coe_smul (K := ℂ) (‖L‖ ^ 2)
                (rightInner (B := B₁) x y)))
        _ = (‖L‖ ^ 2 : ℝ) •
            rightInner (B := B₂) u (φ (rightInner (B := B₁) x y) v) := by
          calc
            rightInner (B := B₂) u
                (φ (((‖L‖ ^ 2 : ℝ) : ℂ) • rightInner (B := B₁) x y) v) =
                rightInner (B := B₂) u
                  ((((‖L‖ ^ 2 : ℝ) : ℂ) • φ (rightInner (B := B₁) x y)) v) :=
              congrArg (fun Q : AdjointableOperator.End B₂ E₂ =>
                rightInner (B := B₂) u (Q v))
                (map_smul φ ((‖L‖ ^ 2 : ℝ) : ℂ) (rightInner (B := B₁) x y))
            _ = rightInner (B := B₂) u
                (((‖L‖ ^ 2 : ℝ) : ℂ) • (φ (rightInner (B := B₁) x y) v)) :=
              congrArg (fun w : E₂ => rightInner (B := B₂) u w)
                (AdjointableOperator.smul_apply ((‖L‖ ^ 2 : ℝ) : ℂ)
                  (φ (rightInner (B := B₁) x y)) v)
            _ = ((‖L‖ ^ 2 : ℝ) : ℂ) •
                rightInner (B := B₂) u (φ (rightInner (B := B₁) x y) v) :=
              rightInner_smul_right (B := B₂) ((‖L‖ ^ 2 : ℝ) : ℂ) u
                (φ (rightInner (B := B₁) x y) v)
            _ = (‖L‖ ^ 2 : ℝ) •
                rightInner (B := B₂) u (φ (rightInner (B := B₁) x y) v) :=
              (RCLike.real_smul_eq_coe_smul (K := ℂ) (‖L‖ ^ 2)
                (rightInner (B := B₂) u (φ (rightInner (B := B₁) x y) v))).symm
    | add w w' hw hw' =>
      simp only [map_add, smul_add]
      rw [add_add_add_comm, hw, hw']
  | add z z' hz hz' =>
    simp only [map_add, LinearMap.add_apply, smul_add]
    rw [add_add_add_comm, hz, hz']

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and F₁ be complete normed right inner-product B₁-modules and E₂
a complete normed right inner-product B₂-module, all with compatible complex normed-space
structures. Let φ represent B₁ by adjointable endomorphisms of E₂, and use the Gram-form norms
on the balanced tensor radical quotients.

For an adjointable L : E₁ → F₁ and a radical quotient vector q, the induced map satisfies
‖L_φ(q)‖ ≤ ‖L‖ ‖q‖.
-/
theorem radicalLeftMap_norm_le
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) (q : RadicalTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    ‖radicalLeftMap φ L q‖ ≤ ‖L‖ * ‖q‖ := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  obtain ⟨S, hS⟩ := leftSquareComplement L
  have hSplit :
      radicalInner φ (radicalLeftMap φ L q) (radicalLeftMap φ L q) +
        radicalInner φ (radicalLeftMap φ S q) (radicalLeftMap φ S q) =
      (‖L‖ ^ 2 : ℝ) • radicalInner φ q q := by
    obtain ⟨w, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
    obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective w
    simpa only [radicalLeftMap_mkQ, balancedLeftMap_mkQ,
      radicalInner_mkQ_mkQ, balancedInner_mkQ_mkQ] using
        rawLeftMap_squareSplit φ L S hS z z
  have hPosL : 0 ≤ MulOpposite.op
      (radicalInner φ (radicalLeftMap φ L q) (radicalLeftMap φ L q)) := by
    obtain ⟨w, hw⟩ := (radicalSpace (E₁ := F₁) φ).mkQ_surjective (radicalLeftMap φ L q)
    rw [← hw, radicalInner_mkQ_mkQ]
    exact balancedInner_self_nonneg φ w
  have hPosS : 0 ≤ MulOpposite.op
      (radicalInner φ (radicalLeftMap φ S q) (radicalLeftMap φ S q)) := by
    obtain ⟨w, hw⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective (radicalLeftMap φ S q)
    rw [← hw, radicalInner_mkQ_mkQ]
    exact balancedInner_self_nonneg φ w
  have hOp :
      MulOpposite.op (radicalInner φ (radicalLeftMap φ L q) (radicalLeftMap φ L q)) +
        MulOpposite.op (radicalInner φ (radicalLeftMap φ S q) (radicalLeftMap φ S q)) =
      (‖L‖ ^ 2 : ℝ) • MulOpposite.op (radicalInner φ q q) := by
    simpa only [MulOpposite.op_add, MulOpposite.op_smul] using
      congrArg MulOpposite.op hSplit
  have hle :
      MulOpposite.op (radicalInner φ (radicalLeftMap φ L q) (radicalLeftMap φ L q)) ≤
        (‖L‖ ^ 2 : ℝ) • MulOpposite.op (radicalInner φ q q) :=
    (le_add_of_nonneg_right hPosS).trans_eq hOp
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hPosL
  have hsq : ‖radicalLeftMap φ L q‖ ^ 2 ≤ (‖L‖ * ‖q‖) ^ 2 := by
    calc
      ‖radicalLeftMap φ L q‖ ^ 2 =
          ‖MulOpposite.op (radicalInner φ (radicalLeftMap φ L q) (radicalLeftMap φ L q))‖ := by
        rw [radicalTensorNormedAddCommGroup_norm,
          Real.sq_sqrt (_root_.norm_nonneg _), MulOpposite.norm_op]
      _ ≤ ‖(‖L‖ ^ 2 : ℝ) • MulOpposite.op (radicalInner φ q q)‖ := hn
      _ = (‖L‖ * ‖q‖) ^ 2 := by
        rw [_root_.norm_smul, Real.norm_of_nonneg (sq_nonneg ‖L‖),
          MulOpposite.norm_op]
        rw [radicalTensorNormedAddCommGroup_norm,
          mul_pow, Real.sq_sqrt (_root_.norm_nonneg _)]
  exact (sq_le_sq₀ (_root_.norm_nonneg (radicalLeftMap φ L q))
    (mul_nonneg (_root_.norm_nonneg L) (_root_.norm_nonneg q))).mp hsq

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and F₁ be complete normed right inner-product B₁-modules and E₂
a complete normed right inner-product B₂-module, all with compatible complex normed-space
structures. Let φ represent B₁ by adjointable endomorphisms of E₂, and use the Gram-form norms
on the balanced tensor radical quotients.

An adjointable L : E₁ → F₁ induces a bounded complex-linear map between the two balanced tensor
radical quotients.
-/
def radicalLeftCLM
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
    RadicalTensor (E₁ := E₁) φ →L[ℂ] RadicalTensor (E₁ := F₁) φ := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ
  exact (radicalLeftMap φ L).mkContinuous ‖L‖ (fun q => radicalLeftMap_norm_le φ L q)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and F₁ be complete normed right inner-product B₁-modules and E₂
a complete normed right inner-product B₂-module, all with compatible complex normed-space
structures. Let φ represent B₁ by adjointable endomorphisms of E₂, and use the Gram-form norms
on the balanced tensor radical quotients.

For an adjointable L : E₁ → F₁ and a radical quotient vector q, the bounded induced map
evaluates to the algebraically induced radical quotient image of q.
-/
@[simp]
theorem radicalLeftCLM_apply
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
    radicalLeftCLM φ L q = radicalLeftMap φ L q := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ
  rfl

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and F₁ be complete normed right inner-product B₁-modules and E₂
a complete normed right inner-product B₂-module, all with compatible complex normed-space
structures. Let φ represent B₁ by adjointable endomorphisms of E₂, and use the Gram-form norms
on the balanced tensor radical quotients.

For an adjointable L : E₁ → F₁, the operator norm of the induced bounded map between the tensor
radical quotients is at most ‖L‖.
-/
theorem radicalLeftCLM_norm_le
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
    ‖radicalLeftCLM φ L‖ ≤ ‖L‖ := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := F₁) φ) :=
    radicalTensorNormedSpace φ
  exact LinearMap.mkContinuous_norm_le (radicalLeftMap φ L) (_root_.norm_nonneg L)
    (fun q => radicalLeftMap_norm_le φ L q)

end CStarModule.InternalTensorProduct
