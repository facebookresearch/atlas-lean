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
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Binary products of right C-star modules

This file supplies the coordinate adjointable maps and block-diagonal
operators on the coefficient-inner-product product
`WithCStarModule Bᵐᵒᵖ (E × F)`.  This is not the raw product norm.

The coefficient, source and target universes are independent.  Completeness
is not needed for the operator calculus itself.
-/

@[expose] public section

noncomputable section

open scoped RightActions

namespace CStarModule

universe uB uE uF uE' uF'

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. The two-factor right
module has coefficient-valued inner product equal to the sum of the factor inner products, and
squared norm equal to the norm of that sum. -/
abbrev Product
    (B : Type uB) (E : Type uE) (F : Type uF) :=
  WithCStarModule Bᵐᵒᵖ (E × F)

namespace Product

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. The first-coordinate
inclusion into the Hilbert-module product is adjointable; its adjoint is projection onto the
first coordinate. -/
def inl : AdjointableOperator B E (WithCStarModule Bᵐᵒᵖ (E × F)) where
  toContinuousLinearMap :=
    (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
      (E := E × F)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℂ E F)
  adjoint :=
    (ContinuousLinearMap.fst ℂ E F).comp
      (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
        (E := E × F)).toContinuousLinearMap
  isAdjointPair' :=
    (AdjointableOperator.isAdjointPair_iff_adjoint_inner _ _).2 <| by
      intro x y
      simp [rightInner, WithCStarModule.prod_inner]

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. The second-coordinate
inclusion into the Hilbert-module product is adjointable; its adjoint is projection onto the
second coordinate. -/
def inr : AdjointableOperator B F (WithCStarModule Bᵐᵒᵖ (E × F)) where
  toContinuousLinearMap :=
    (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
      (E := E × F)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr ℂ E F)
  adjoint :=
    (ContinuousLinearMap.snd ℂ E F).comp
      (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
        (E := E × F)).toContinuousLinearMap
  isAdjointPair' :=
    (AdjointableOperator.isAdjointPair_iff_adjoint_inner _ _).2 <| by
      intro x y
      simp [rightInner, WithCStarModule.prod_inner]

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. Projection from the
Hilbert-module product onto the first coordinate is adjointable, with first-coordinate
inclusion as adjoint. -/
def fst : AdjointableOperator B (WithCStarModule Bᵐᵒᵖ (E × F)) E :=
  (inl (B := B) (E := E) (F := F)).adjointOperator

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. Projection from the
Hilbert-module product onto the second coordinate is adjointable, with second-coordinate
inclusion as adjoint. -/
def snd : AdjointableOperator B (WithCStarModule Bᵐᵒᵖ (E × F)) F :=
  (inr (B := B) (E := E) (F := F)).adjointOperator

@[simp]
theorem inl_apply (x : E) :
    inl (B := B) (E := E) (F := F) x =
      ((x, 0) : WithCStarModule Bᵐᵒᵖ (E × F)) :=
  rfl

@[simp]
theorem inr_apply (x : F) :
    inr (B := B) (E := E) (F := F) x =
      ((0, x) : WithCStarModule Bᵐᵒᵖ (E × F)) :=
  rfl

@[simp]
theorem fst_apply (x : WithCStarModule Bᵐᵒᵖ (E × F)) :
    fst (B := B) (E := E) (F := F) x = x.1 :=
  rfl

@[simp]
theorem snd_apply (x : WithCStarModule Bᵐᵒᵖ (E × F)) :
    snd (B := B) (E := E) (F := F) x = x.2 :=
  rfl

@[simp]
theorem inl_adjoint_apply (x : WithCStarModule Bᵐᵒᵖ (E × F)) :
    (inl (B := B) (E := E) (F := F)).adjoint x = x.1 :=
  rfl

@[simp]
theorem inr_adjoint_apply (x : WithCStarModule Bᵐᵒᵖ (E × F)) :
    (inr (B := B) (E := E) (F := F)).adjoint x = x.2 :=
  rfl

@[simp]
theorem fst_adjoint_apply (x : E) :
    (fst (B := B) (E := E) (F := F)).adjoint x =
      ((x, 0) : WithCStarModule Bᵐᵒᵖ (E × F)) :=
  rfl

@[simp]
theorem snd_adjoint_apply (x : F) :
    (snd (B := B) (E := E) (F := F)).adjoint x =
      ((0, x) : WithCStarModule Bᵐᵒᵖ (E × F)) :=
  rfl

end Product

namespace AdjointableOperator

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
variable {F' : Type uF'} [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [SMul Bᵐᵒᵖ F'] [CStarModule Bᵐᵒᵖ F']

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. A pair of adjointable
maps defines the block-diagonal adjointable map between the two Hilbert-module products. -/
def prodMap (T : AdjointableOperator B E E')
    (S : AdjointableOperator B F F') :
    AdjointableOperator B (WithCStarModule Bᵐᵒᵖ (E × F))
      (WithCStarModule Bᵐᵒᵖ (E' × F')) :=
  (Product.inl (B := B) (E := E') (F := F')).comp
      (T.comp (Product.fst (B := B) (E := E) (F := F))) +
    (Product.inr (B := B) (E := E') (F := F')).comp
      (S.comp (Product.snd (B := B) (E := E) (F := F)))

@[simp]
theorem prodMap_apply (T : AdjointableOperator B E E')
    (S : AdjointableOperator B F F')
    (x : WithCStarModule Bᵐᵒᵖ (E × F)) :
    prodMap T S x =
      ((T x.1, S x.2) : WithCStarModule Bᵐᵒᵖ (E' × F')) := by
  change ((T x.1, 0) : WithCStarModule Bᵐᵒᵖ (E' × F')) +
      (0, S x.2) = (T x.1, S x.2)
  apply (WithCStarModule.equiv Bᵐᵒᵖ (E' × F')).injective
  change (T x.1 + 0, 0 + S x.2) = (T x.1, S x.2)
  rw [add_zero, zero_add]

@[simp]
theorem prodMap_adjointOperator (T : AdjointableOperator B E E')
    (S : AdjointableOperator B F F') :
    (prodMap T S).adjointOperator =
      prodMap T.adjointOperator S.adjointOperator := by
  apply AdjointableOperator.toContinuousLinearMap_injective
  change (prodMap T S).adjoint =
    (prodMap T.adjointOperator S.adjointOperator).toContinuousLinearMap
  apply AdjointableOperator.adjoint_unique
    (B := B) (prodMap T S).toContinuousLinearMap
  · exact (prodMap T S).adjoint_inner
  · intro x y
    change rightInner (B := B) (prodMap T S x) y =
      rightInner (B := B) x
        (prodMap T.adjointOperator S.adjointOperator y)
    rw [prodMap_apply, prodMap_apply]
    change rightInner (B := B) (T x.1) y.1 +
        rightInner (B := B) (S x.2) y.2 =
      rightInner (B := B) x.1 (T.adjoint y.1) +
        rightInner (B := B) x.2 (S.adjoint y.2)
    rw [T.adjoint_inner, S.adjoint_inner]

@[simp]
theorem prodMap_zero :
    prodMap (0 : AdjointableOperator B E E')
      (0 : AdjointableOperator B F F') = 0 := by
  ext x
  rw [prodMap_apply]
  change ((0, 0) : WithCStarModule Bᵐᵒᵖ (E' × F')) = 0
  rfl

@[simp]
theorem prodMap_add (T U : AdjointableOperator B E E')
    (S V : AdjointableOperator B F F') :
    prodMap (T + U) (S + V) = prodMap T S + prodMap U V := by
  ext x
  simp only [prodMap_apply, add_apply]
  apply (WithCStarModule.equiv Bᵐᵒᵖ (E' × F')).injective
  rfl

@[simp]
theorem prodMap_id :
    prodMap (AdjointableOperator.id (B := B) (E := E))
        (AdjointableOperator.id (B := B) (E := F)) =
      AdjointableOperator.id := by
  ext x
  rw [prodMap_apply]
  change ((x.1, x.2) : WithCStarModule Bᵐᵒᵖ (E × F)) = x
  apply (WithCStarModule.equiv Bᵐᵒᵖ (E × F)).injective
  exact Prod.eta _

@[simp]
theorem prodMap_comp
    (T : AdjointableOperator B E E') (S : AdjointableOperator B F F')
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
      [SMul Bᵐᵒᵖ E''] [CStarModule Bᵐᵒᵖ E'']
    {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace ℂ F'']
      [SMul Bᵐᵒᵖ F''] [CStarModule Bᵐᵒᵖ F'']
    (T' : AdjointableOperator B E' E'')
    (S' : AdjointableOperator B F' F'') :
    (prodMap T' S').comp (prodMap T S) =
      prodMap (T'.comp T) (S'.comp S) := by
  ext x
  rw [comp_apply, prodMap_apply, prodMap_apply, prodMap_apply]
  rfl

end AdjointableOperator

end CStarModule
