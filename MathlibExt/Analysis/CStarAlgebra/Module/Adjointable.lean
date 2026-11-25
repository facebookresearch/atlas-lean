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

public import MathlibExt.Analysis.CStarAlgebra.Module.Right
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Adjointable operators on right C-star modules

This file bundles bounded operators between right C-star modules together
with their uniquely determined adjoints.  Right modules over `B` are modeled
as `CStarModule Bᵐᵒᵖ E`; the stored equation is the source-oriented formula

`rightInner (T x) y = rightInner x (T.adjoint y)`.

The coefficient, source, and target universes are independent.  The carrier
stores continuous complex-linear maps, but right `B`-linearity is derived
from the adjoint equation rather than repeated as a field.  Cross-module maps
carry their operator norm, and endomorphisms form a normed star ring satisfying
the C-star square identity.  Automatic boundedness from a raw adjoint pair,
completeness, compact operators, and regular operators are separate analytic
layers.

Importing this file installs no adjoint on arbitrary continuous linear maps
and no `SMul B E` instance.
-/

@[expose] public section

open scoped RightActions

namespace CStarModule

open Filter

universe uB uE uF uG

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

An adjointable operator from E to F consists of bounded complex-linear maps T : E → F and T* : F
→ E satisfying ⟨Tx, y⟩ = ⟨x, T*y⟩ for the coefficient-valued right inner products.
-/
structure AdjointableOperator
    (B : Type uB) (E : Type uE) (F : Type uF)
    [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
    [CStarModule Bᵐᵒᵖ F]
    extends E →L[ℂ] F where
  /--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

For an adjointable map T : E → F, this is its bounded complex-linear adjoint T* : F → E.
-/
  adjoint : F →L[ℂ] E
  /--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

The forward map T : E → F and the bounded adjoint T* : F → E satisfy ⟨Tx, y⟩ = ⟨x, T*y⟩ for all
x ∈ E and y ∈ F.
-/
  isAdjointPair' : LinearMap.IsAdjointPair
    (LinearMap.flip (CStarModule.innerₛₗ (A := Bᵐᵒᵖ) (E := E)))
    ((CStarModule.innerₛₗ (A := Bᵐᵒᵖ) (E := F)).flip)
    toContinuousLinearMap adjoint

namespace AdjointableOperator

variable {B : Type uB} {E : Type uE} {F : Type uF} {G : Type uG}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F]
variable [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G]
  [CStarModule Bᵐᵒᵖ G]

@[simp]
theorem isAdjointPair_iff_adjoint_inner
    (T : E →L[ℂ] F) (S : F →L[ℂ] E) :
    LinearMap.IsAdjointPair
        (LinearMap.flip (CStarModule.innerₛₗ (A := Bᵐᵒᵖ) (E := E)))
        ((CStarModule.innerₛₗ (A := Bᵐᵒᵖ) (E := F)).flip) T S ↔
      ∀ x y,
        rightInner (B := B) (T x) y =
          rightInner (B := B) x (S y) := by
  constructor
  · intro h x y
    have h0 := h x y
    change inner Bᵐᵒᵖ y (T x) = inner Bᵐᵒᵖ (S y) x at h0
    have h' : inner Bᵐᵒᵖ (T x) y = inner Bᵐᵒᵖ x (S y) := by
      have hs := congrArg star h0
      rw [CStarModule.star_inner, CStarModule.star_inner] at hs
      exact hs
    exact congrArg MulOpposite.unop h'
  · intro h x y
    change inner Bᵐᵒᵖ y (T x) = inner Bᵐᵒᵖ (S y) x
    have h' : inner Bᵐᵒᵖ (T x) y = inner Bᵐᵒᵖ x (S y) := by
      have hu := h x y
      change MulOpposite.unop (inner Bᵐᵒᵖ (T x) y) =
        MulOpposite.unop (inner Bᵐᵒᵖ x (S y)) at hu
      exact MulOpposite.unop_injective hu
    have hs := congrArg star h'
    rw [CStarModule.star_inner, CStarModule.star_inner] at hs
    exact hs

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

For an adjointable T : E → F and vectors x ∈ E and y ∈ F, the forward map and its adjoint
satisfy ⟨Tx, y⟩ = ⟨x, T*y⟩.
-/
theorem adjoint_inner_toContinuousLinearMap
    (T : AdjointableOperator B E F) (x : E) (y : F) :
    rightInner (B := B) (T.toContinuousLinearMap x) y =
      rightInner (B := B) x (T.adjoint y) :=
  (isAdjointPair_iff_adjoint_inner T.toContinuousLinearMap T.adjoint).1
    T.isAdjointPair' x y

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E be a normed
right inner-product module over B, with compatible complex normed-space structures.

If x and y have the same coefficient-valued inner product with every vector in the second slot,
then x = y.
-/
theorem ext_rightInner_left {x y : E}
    (h : ∀ z : E,
      rightInner (B := B) x z = rightInner (B := B) y z) :
    x = y := by
  apply CStarModule.ext_rightInner (B := B)
  intro z
  calc
    rightInner (B := B) z x = star (rightInner (B := B) x z) :=
      (star_rightInner x z).symm
    _ = star (rightInner (B := B) y z) := congrArg star (h z)
    _ = rightInner (B := B) z y := star_rightInner y z

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

Let T : E → F and S₁, S₂ : F → E be bounded complex-linear maps. If both S₁ and S₂ satisfy the
adjoint identity with T for every pair of vectors, then S₁ = S₂.
-/
theorem adjoint_unique
    (T : E →L[ℂ] F) {S₁ S₂ : F →L[ℂ] E}
    (h₁ : ∀ x y,
      rightInner (B := B) (T x) y = rightInner (B := B) x (S₁ y))
    (h₂ : ∀ x y,
      rightInner (B := B) (T x) y = rightInner (B := B) x (S₂ y)) :
    S₁ = S₂ := by
  ext y
  apply CStarModule.ext_rightInner (B := B)
  intro x
  exact (h₁ x y).symm.trans (h₂ x y)

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

The map sending an adjointable operator to its forward bounded complex-linear map is injective.
-/
theorem toContinuousLinearMap_injective :
    Function.Injective
      (fun T : AdjointableOperator B E F ↦ T.toContinuousLinearMap) := by
  intro T S hforward
  have hT := (isAdjointPair_iff_adjoint_inner
    T.toContinuousLinearMap T.adjoint).1 T.isAdjointPair'
  have hS := (isAdjointPair_iff_adjoint_inner
    S.toContinuousLinearMap S.adjoint).1 S.isAdjointPair'
  change T.toContinuousLinearMap = S.toContinuousLinearMap at hforward
  have hadjoint : T.adjoint = S.adjoint := by
    apply adjoint_unique (B := B) T.toContinuousLinearMap
    · exact hT
    · intro x y
      rw [hforward]
      exact hS x y
  cases T
  cases S
  simp_all

instance : FunLike (AdjointableOperator B E F) E F where
  coe T := T.toContinuousLinearMap
  coe_injective :=
    DFunLike.coe_injective.comp toContinuousLinearMap_injective

instance : ContinuousLinearMapClass
    (AdjointableOperator B E F) ℂ E F where
  map_add T x y := by
    change T.toContinuousLinearMap (x + y) =
      T.toContinuousLinearMap x + T.toContinuousLinearMap y
    exact T.toContinuousLinearMap.map_add x y
  map_smulₛₗ T c x := by
    change T.toContinuousLinearMap (c • x) =
      c • T.toContinuousLinearMap x
    exact T.toContinuousLinearMap.map_smul c x
  map_continuous T := by
    change Continuous T.toContinuousLinearMap
    exact T.toContinuousLinearMap.continuous

@[simp]
theorem coe_toContinuousLinearMap (T : AdjointableOperator B E F) :
    ((T.toContinuousLinearMap : E →L[ℂ] F) : E → F) = T :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

For an adjointable T : E → F and x ∈ E, y ∈ F, the right inner products satisfy ⟨Tx, y⟩ = ⟨x,
T*y⟩.
-/
@[simp]
theorem adjoint_inner (T : AdjointableOperator B E F) (x : E) (y : F) :
    rightInner (B := B) (T x) y =
      rightInner (B := B) x (T.adjoint y) :=
  adjoint_inner_toContinuousLinearMap T x y

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

Two adjointable operators E → F are equal whenever they agree on every vector of E.
-/
@[ext]
theorem ext {T S : AdjointableOperator B E F}
    (h : ∀ x, T x = S x) : T = S := by
  have hforward : T.toContinuousLinearMap = S.toContinuousLinearMap := by
    ext x
    exact h x
  have hadjoint : T.adjoint = S.adjoint := by
    apply adjoint_unique (B := B) T.toContinuousLinearMap
    · exact T.adjoint_inner_toContinuousLinearMap
    · intro x y
      rw [hforward]
      exact S.adjoint_inner_toContinuousLinearMap x y
  cases T
  cases S
  simp_all

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E be a normed
right inner-product module over B, with compatible complex normed-space structures.

The identity map on E is adjointable and is its own adjoint.
-/
def id : AdjointableOperator B E E where
  toContinuousLinearMap := ContinuousLinearMap.id ℂ E
  adjoint := ContinuousLinearMap.id ℂ E
  isAdjointPair' := (isAdjointPair_iff_adjoint_inner
    (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ E)).2 <| by
    intro x y
    rfl

@[simp]
theorem id_apply (x : E) : id (B := B) x = x :=
  rfl

@[simp]
theorem id_adjoint : (id (B := B) (E := E)).adjoint =
    ContinuousLinearMap.id ℂ E :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

The zero map E → F is adjointable, with zero adjoint F → E.
-/
def zero : AdjointableOperator B E F where
  toContinuousLinearMap := 0
  adjoint := 0
  isAdjointPair' := (isAdjointPair_iff_adjoint_inner
    (0 : E →L[ℂ] F) (0 : F →L[ℂ] E)).2 <| by
    intro x y
    simp

instance : Zero (AdjointableOperator B E F) :=
  ⟨zero⟩

@[simp]
theorem zero_apply (x : E) : (0 : AdjointableOperator B E F) x = 0 :=
  rfl

@[simp]
theorem zero_adjoint : (0 : AdjointableOperator B E F).adjoint = 0 :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

The sum of two adjointable maps E → F is adjointable, with adjoint equal to the sum of their
adjoints.
-/
def add (T S : AdjointableOperator B E F) :
    AdjointableOperator B E F where
  toContinuousLinearMap := T.toContinuousLinearMap + S.toContinuousLinearMap
  adjoint := T.adjoint + S.adjoint
  isAdjointPair' := (isAdjointPair_iff_adjoint_inner
    (T.toContinuousLinearMap + S.toContinuousLinearMap)
    (T.adjoint + S.adjoint)).2 <| by
    intro x y
    rw [add_apply, rightInner_add_left,
      add_apply, rightInner_add_right,
      T.adjoint_inner_toContinuousLinearMap,
      S.adjoint_inner_toContinuousLinearMap]

instance : Add (AdjointableOperator B E F) :=
  ⟨add⟩

@[simp]
theorem add_apply (T S : AdjointableOperator B E F) (x : E) :
    (T + S) x = T x + S x :=
  rfl

@[simp]
theorem add_adjoint (T S : AdjointableOperator B E F) :
    (T + S).adjoint = T.adjoint + S.adjoint :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

The negative of an adjointable map E → F is adjointable, with adjoint equal to the negative
adjoint.
-/
def neg (T : AdjointableOperator B E F) :
    AdjointableOperator B E F where
  toContinuousLinearMap := -T.toContinuousLinearMap
  adjoint := -T.adjoint
  isAdjointPair' := (isAdjointPair_iff_adjoint_inner
    (-T.toContinuousLinearMap) (-T.adjoint)).2 <| by
    intro x y
    rw [neg_apply, rightInner_neg_left,
      neg_apply, rightInner_neg_right,
      T.adjoint_inner_toContinuousLinearMap]

instance : Neg (AdjointableOperator B E F) :=
  ⟨neg⟩

@[simp]
theorem neg_apply (T : AdjointableOperator B E F) (x : E) :
    (-T) x = -(T x) :=
  rfl

@[simp]
theorem neg_adjoint (T : AdjointableOperator B E F) :
    (-T).adjoint = -T.adjoint :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

For c ∈ ℂ and an adjointable map T : E → F, scalar multiplication gives the adjointable map cT
with adjoint conjugate(c) T*.
-/
def smul (c : ℂ) (T : AdjointableOperator B E F) :
    AdjointableOperator B E F where
  toContinuousLinearMap := c • T.toContinuousLinearMap
  adjoint := star c • T.adjoint
  isAdjointPair' := (isAdjointPair_iff_adjoint_inner
    (c • T.toContinuousLinearMap) (star c • T.adjoint)).2 <| by
    intro x y
    rw [smul_apply, rightInner_smul_left,
      smul_apply, rightInner_smul_right,
      T.adjoint_inner_toContinuousLinearMap]

instance : SMul ℂ (AdjointableOperator B E F) :=
  ⟨smul⟩

@[simp]
theorem smul_apply (c : ℂ) (T : AdjointableOperator B E F) (x : E) :
    (c • T) x = c • T x :=
  rfl

@[simp]
theorem smul_adjoint (c : ℂ) (T : AdjointableOperator B E F) :
    (c • T).adjoint = star c • T.adjoint :=
  rfl

instance : AddCommGroup (AdjointableOperator B E F) where
  add := (· + ·)
  add_assoc T S R := by
    ext x
    simp only [add_apply, add_assoc]
  zero := 0
  zero_add T := by
    ext x
    simp only [zero_apply, add_apply, zero_add]
  add_zero T := by
    ext x
    simp only [zero_apply, add_apply, add_zero]
  nsmul := nsmulRec
  neg := Neg.neg
  zsmul := zsmulRec
  neg_add_cancel T := by
    ext x
    change -(T x) + T x = 0
    exact neg_add_cancel (T x)
  add_comm T S := by
    ext x
    simp only [add_apply, add_comm]

@[simp]
theorem sub_adjoint (T S : AdjointableOperator B E F) :
    (T - S).adjoint = T.adjoint - S.adjoint := by
  rw [show T - S = T + -S from sub_eq_add_neg T S,
    add_adjoint, neg_adjoint]
  exact (sub_eq_add_neg _ _).symm

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

Sending an adjointable map E → F to its forward bounded complex-linear map defines an additive
homomorphism.
-/
def forwardAddHom : AdjointableOperator B E F →+
    (E →L[ℂ] F) where
  toFun := AdjointableOperator.toContinuousLinearMap
  map_zero' := rfl
  map_add' _ _ := rfl

theorem forwardAddHom_injective :
    Function.Injective
      (forwardAddHom (B := B) (E := E) (F := F)) := by
  intro T S h
  apply ext
  intro x
  exact congrArg (fun f : E →L[ℂ] F ↦ f x) h

instance : Module ℂ (AdjointableOperator B E F) :=
  Function.Injective.module ℂ
    (forwardAddHom (B := B) (E := E) (F := F))
    forwardAddHom_injective fun _ _ ↦ rfl

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

Sending an adjointable map E → F to its forward bounded complex-linear map defines a
complex-linear map.
-/
def forwardLinearMap : AdjointableOperator B E F →ₗ[ℂ]
    (E →L[ℂ] F) where
  toFun := AdjointableOperator.toContinuousLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable instance : NormedAddCommGroup
    (AdjointableOperator B E F) :=
  NormedAddCommGroup.induced (AdjointableOperator B E F) (E →L[ℂ] F)
    (forwardAddHom (B := B) (E := E) (F := F))
    forwardAddHom_injective

instance : NormedSpace ℂ (AdjointableOperator B E F) where
  norm_smul_le c T := by
    change ‖c • T.toContinuousLinearMap‖ ≤
      ‖c‖ * ‖T.toContinuousLinearMap‖
    exact norm_smul_le c T.toContinuousLinearMap

@[simp]
theorem norm_eq (T : AdjointableOperator B E F) :
    ‖T‖ = ‖T.toContinuousLinearMap‖ :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

The forgetful map from adjointable operators E → F to bounded complex-linear maps E → F
preserves distances in the operator norm.
-/
theorem isometry_toContinuousLinearMap :
    Isometry (fun T : AdjointableOperator B E F ↦
      T.toContinuousLinearMap) := by
  apply Isometry.of_dist_eq
  intro T S
  rfl

theorem norm_eq_sqrt_norm_rightInner (x : E) :
    ‖x‖ = √‖rightInner (B := B) x x‖ := by
  rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ)]
  congr 2

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures.

For an adjointable map T : E → F, the operator norm of T* is at most the operator norm of T.
-/
theorem norm_adjoint_le [StarOrderedRing Bᵐᵒᵖ]
    (T : AdjointableOperator B E F) :
    ‖T.adjoint‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound T.adjoint (norm_nonneg T)
  intro y
  by_cases hy : ‖T.adjoint y‖ = 0
  · rw [hy]
    exact mul_nonneg (norm_nonneg T) (norm_nonneg y)
  · have hypos : 0 < ‖T.adjoint y‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
    have hsq : ‖T.adjoint y‖ ^ 2 ≤
        (‖T‖ * ‖y‖) * ‖T.adjoint y‖ := by
      calc
        ‖T.adjoint y‖ ^ 2 =
            ‖rightInner (B := B) (T.adjoint y) (T.adjoint y)‖ :=
          (CStarModule.norm_rightInner_self (B := B) (T.adjoint y)).symm
        _ = ‖rightInner (B := B)
            (T.toContinuousLinearMap (T.adjoint y)) y‖ := by
          rw [T.adjoint_inner_toContinuousLinearMap]
        _ ≤ ‖T.toContinuousLinearMap (T.adjoint y)‖ * ‖y‖ := by
          rw [rightInner, MulOpposite.norm_unop]
          exact CStarModule.norm_inner_le F
        _ ≤ (‖T‖ * ‖T.adjoint y‖) * ‖y‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
          simpa only [norm_eq] using
            T.toContinuousLinearMap.le_opNorm (T.adjoint y)
        _ = (‖T‖ * ‖y‖) * ‖T.adjoint y‖ := by
          ac_rfl
    exact le_of_mul_le_mul_right
      (by simpa only [pow_two] using hsq) hypos

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E, F and G be
normed right inner-product modules over B, with compatible complex normed-space structures.

For adjointable T : E → F and S : F → G, their composite S ∘ T is adjointable and has adjoint T*
∘ S*.
-/
def comp (S : AdjointableOperator B F G)
    (T : AdjointableOperator B E F) :
    AdjointableOperator B E G where
  toContinuousLinearMap := S.toContinuousLinearMap.comp T.toContinuousLinearMap
  adjoint := T.adjoint.comp S.adjoint
  isAdjointPair' := (isAdjointPair_iff_adjoint_inner
    (S.toContinuousLinearMap.comp T.toContinuousLinearMap)
    (T.adjoint.comp S.adjoint)).2 <| by
    intro x z
    rw [ContinuousLinearMap.comp_apply,
      S.adjoint_inner_toContinuousLinearMap,
      ContinuousLinearMap.comp_apply,
      T.adjoint_inner_toContinuousLinearMap]

@[simp]
theorem comp_apply (S : AdjointableOperator B F G)
    (T : AdjointableOperator B E F) (x : E) :
    S.comp T x = S (T x) :=
  rfl

@[simp]
theorem comp_adjoint (S : AdjointableOperator B F G)
    (T : AdjointableOperator B E F) :
    (S.comp T).adjoint = T.adjoint.comp S.adjoint :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E, F and G be
normed right inner-product modules over B, with compatible complex normed-space structures.

For adjointable T : E → F and S : F → G, the operator norm satisfies ‖S ∘ T‖ ≤ ‖S‖ ‖T‖.
-/
theorem norm_comp_le (S : AdjointableOperator B F G)
    (T : AdjointableOperator B E F) :
    ‖S.comp T‖ ≤ ‖S‖ * ‖T‖ := by
  change ‖S.toContinuousLinearMap.comp T.toContinuousLinearMap‖ ≤
    ‖S.toContinuousLinearMap‖ * ‖T.toContinuousLinearMap‖
  exact ContinuousLinearMap.opNorm_comp_le _ _

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E, F and G be
normed right inner-product modules over B, with compatible complex normed-space structures.

For a fixed adjointable S : F → G, postcomposition T ↦ S ∘ T is a bounded complex-linear map
from the adjointable maps E → F to those E → G.
-/
noncomputable def postcompCLM (S : AdjointableOperator B F G) :
    AdjointableOperator B E F →L[ℂ] AdjointableOperator B E G :=
  LinearMap.mkContinuous
    { toFun := fun T ↦ S.comp T
      map_add' := by
        intro T U
        ext x
        change S.toContinuousLinearMap (T x + U x) =
          S.toContinuousLinearMap (T x) + S.toContinuousLinearMap (U x)
        exact S.toContinuousLinearMap.map_add (T x) (U x)
      map_smul' := by
        intro c T
        ext x
        change S.toContinuousLinearMap (c • T x) =
          c • S.toContinuousLinearMap (T x)
        exact S.toContinuousLinearMap.map_smul c (T x) }
    ‖S‖ fun T ↦ by
      change ‖S.comp T‖ ≤ ‖S‖ * ‖T‖
      exact norm_comp_le S T

@[simp]
theorem postcompCLM_apply (S : AdjointableOperator B F G)
    (T : AdjointableOperator B E F) :
    postcompCLM S T = S.comp T :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E, F and G be
normed right inner-product modules over B, with compatible complex normed-space structures.

For a fixed adjointable T : E → F, precomposition S ↦ S ∘ T is a bounded complex-linear map from
the adjointable maps F → G to those E → G.
-/
noncomputable def precompCLM (T : AdjointableOperator B E F) :
    AdjointableOperator B F G →L[ℂ] AdjointableOperator B E G :=
  LinearMap.mkContinuous
    { toFun := fun S ↦ S.comp T
      map_add' := by
        intro S U
        ext x
        rfl
      map_smul' := by
        intro c S
        ext x
        rfl }
    ‖T‖ fun S ↦ by
      change ‖S.comp T‖ ≤ ‖T‖ * ‖S‖
      simpa only [mul_comm] using norm_comp_le S T

@[simp]
theorem precompCLM_apply (T : AdjointableOperator B E F)
    (S : AdjointableOperator B F G) :
    precompCLM T S = S.comp T :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

The adjoint T* of an adjointable map T : E → F is an adjointable map F → E, with adjoint T.
-/
def adjointOperator (T : AdjointableOperator B E F) :
    AdjointableOperator B F E where
  toContinuousLinearMap := T.adjoint
  adjoint := T.toContinuousLinearMap
  isAdjointPair' := (isAdjointPair_iff_adjoint_inner
    T.adjoint T.toContinuousLinearMap).2 <| by
    intro y x
    have h := congrArg star
      (T.adjoint_inner_toContinuousLinearMap x y)
    simpa only [star_rightInner] using h.symm

@[simp]
theorem adjointOperator_apply (T : AdjointableOperator B E F) (y : F) :
    T.adjointOperator y = T.adjoint y :=
  rfl

@[simp]
theorem adjointOperator_adjoint (T : AdjointableOperator B E F) :
    T.adjointOperator.adjoint = T.toContinuousLinearMap :=
  rfl

@[simp]
theorem adjointOperator_adjointOperator (T : AdjointableOperator B E F) :
    T.adjointOperator.adjointOperator = T := by
  ext x
  rfl

@[simp]
theorem comp_adjointOperator (S : AdjointableOperator B F G)
    (T : AdjointableOperator B E F) :
    (S.comp T).adjointOperator =
      T.adjointOperator.comp S.adjointOperator := by
  ext x
  rfl

@[simp]
theorem zero_adjointOperator :
    (0 : AdjointableOperator B E F).adjointOperator = 0 := by
  ext x
  rfl

@[simp]
theorem add_adjointOperator (T S : AdjointableOperator B E F) :
    (T + S).adjointOperator = T.adjointOperator + S.adjointOperator := by
  ext x
  rfl

@[simp]
theorem neg_adjointOperator (T : AdjointableOperator B E F) :
    (-T).adjointOperator = -T.adjointOperator := by
  ext x
  rfl

@[simp]
theorem sub_adjointOperator (T S : AdjointableOperator B E F) :
    (T - S).adjointOperator = T.adjointOperator - S.adjointOperator := by
  ext x
  rfl

@[simp]
theorem smul_adjointOperator (c : ℂ) (T : AdjointableOperator B E F) :
    (c • T).adjointOperator = star c • T.adjointOperator := by
  ext x
  rfl

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures.

The adjoint bounded complex-linear map of any adjointable T : E → F has operator norm ‖T‖.
-/
theorem norm_adjoint [StarOrderedRing Bᵐᵒᵖ]
    (T : AdjointableOperator B E F) :
    ‖T.adjoint‖ = ‖T‖ := by
  apply le_antisymm (norm_adjoint_le T)
  calc
    ‖T‖ = ‖T.adjointOperator.adjoint‖ := by
      rfl
    _ ≤ ‖T.adjointOperator‖ := norm_adjoint_le T.adjointOperator
    _ = ‖T.adjoint‖ := by
      rfl

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures.

The adjoint, viewed as an adjointable map F → E, has the same operator norm as the original map
E → F.
-/
@[simp]
theorem norm_adjointOperator [StarOrderedRing Bᵐᵒᵖ]
    (T : AdjointableOperator B E F) :
    ‖T.adjointOperator‖ = ‖T‖ :=
  norm_adjoint T

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures.

Taking adjoints is an isometry from the adjointable maps E → F to the adjointable maps F → E.
-/
theorem isometry_adjointOperator [StarOrderedRing Bᵐᵒᵖ] :
    Isometry (fun T : AdjointableOperator B E F ↦ T.adjointOperator) := by
  apply Isometry.of_dist_eq
  intro T S
  rw [dist_eq_norm, dist_eq_norm, ← sub_adjointOperator,
    norm_adjointOperator]

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures.

The map sending an adjointable T : E → F to its adjoint bounded complex-linear map F → E is an
isometry.
-/
theorem isometry_adjoint [StarOrderedRing Bᵐᵒᵖ] :
    Isometry (fun T : AdjointableOperator B E F ↦ T.adjoint) := by
  apply Isometry.of_dist_eq
  intro T S
  rw [dist_eq_norm, dist_eq_norm]
  rw [← sub_adjoint, norm_adjoint]

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures.

Taking adjoints is continuous between the two adjointable operator spaces equipped with their
operator norms.
-/
theorem continuous_adjointOperator [StarOrderedRing Bᵐᵒᵖ] :
    Continuous (fun T : AdjointableOperator B E F ↦ T.adjointOperator) :=
  isometry_adjointOperator.continuous

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be complete normed right inner-product modules over
B, with compatible complex normed-space structures.

The space of adjointable maps E → F is complete for the forward operator norm.
-/
noncomputable instance [StarOrderedRing Bᵐᵒᵖ]
    [CompleteSpace E] [CompleteSpace F] :
    CompleteSpace (AdjointableOperator B E F) :=
  Metric.complete_of_cauchySeq_tendsto fun T hT ↦ by
    have hforwardCauchy :
        CauchySeq (fun n ↦ (T n).toContinuousLinearMap) :=
      isometry_toContinuousLinearMap.uniformContinuous.comp_cauchySeq hT
    obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hforwardCauchy
    have hadjointCauchy : CauchySeq (fun n ↦ (T n).adjoint) :=
      isometry_adjoint.uniformContinuous.comp_cauchySeq hT
    obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hadjointCauchy
    have hpair : ∀ x y,
        rightInner (B := B) (f x) y = rightInner (B := B) x (g y) := by
      intro x y
      have hfx : Tendsto (fun n ↦ (T n).toContinuousLinearMap x)
          atTop (nhds (f x)) :=
        (ContinuousLinearMap.apply ℂ F x).continuous.continuousAt.tendsto.comp hf
      have hgy : Tendsto (fun n ↦ (T n).adjoint y)
          atTop (nhds (g y)) :=
        (ContinuousLinearMap.apply ℂ E y).continuous.continuousAt.tendsto.comp hg
      have hleft : Tendsto
          (fun n ↦ rightInner (B := B)
            ((T n).toContinuousLinearMap x) y)
          atTop (nhds (rightInner (B := B) (f x) y)) :=
        (continuous_rightInner_left (B := B) y).continuousAt.tendsto.comp hfx
      have hright : Tendsto
          (fun n ↦ rightInner (B := B) x ((T n).adjoint y))
          atTop (nhds (rightInner (B := B) x (g y))) :=
        (continuous_rightInner_right (B := B) x).continuousAt.tendsto.comp hgy
      apply tendsto_nhds_unique hleft
      apply hright.congr'
      exact Eventually.of_forall fun n ↦
        ((T n).adjoint_inner_toContinuousLinearMap x y).symm
    let A : AdjointableOperator B E F :=
      { toContinuousLinearMap := f
        adjoint := g
        isAdjointPair' :=
          (isAdjointPair_iff_adjoint_inner f g).2 hpair }
    refine ⟨A, isometry_toContinuousLinearMap.tendsto_nhds_iff.mpr ?_⟩
    change Tendsto (fun n ↦ (T n).toContinuousLinearMap) atTop (nhds f)
    exact hf

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E and F be normed right inner-product modules over B, with
compatible complex normed-space structures.

Every adjointable T : E → F satisfies the C*-identity ‖T* ∘ T‖ = ‖T‖².
-/
theorem norm_adjoint_comp_self [StarOrderedRing Bᵐᵒᵖ]
    (T : AdjointableOperator B E F) :
    ‖T.adjointOperator.comp T‖ = ‖T‖ * ‖T‖ := by
  refine le_antisymm ?_ ?_
  · calc
      ‖T.adjointOperator.comp T‖ ≤
          ‖T.adjointOperator‖ * ‖T‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖T‖ * ‖T‖ := by rw [norm_adjointOperator]
  · rw [← sq, ← Real.sqrt_le_sqrt_iff (norm_nonneg _),
      Real.sqrt_sq (norm_nonneg _)]
    apply ContinuousLinearMap.opNorm_le_bound T.toContinuousLinearMap
      (Real.sqrt_nonneg _)
    intro x
    have hinner :
        ‖rightInner (B := B) x (T.adjointOperator.comp T x)‖ ≤
          ‖T.adjointOperator.comp T‖ * ‖x‖ * ‖x‖ := by
      calc
        ‖rightInner (B := B) x (T.adjointOperator.comp T x)‖ ≤
            ‖x‖ * ‖T.adjointOperator.comp T x‖ := by
          rw [rightInner, MulOpposite.norm_unop]
          exact CStarModule.norm_inner_le E
        _ ≤ ‖x‖ * (‖T.adjointOperator.comp T‖ * ‖x‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg x)
          exact (T.adjointOperator.comp T).toContinuousLinearMap.le_opNorm x
        _ = ‖T.adjointOperator.comp T‖ * ‖x‖ * ‖x‖ := by
          ac_rfl
    calc
      ‖T x‖ = √‖rightInner (B := B) (T x) (T x)‖ :=
        norm_eq_sqrt_norm_rightInner (B := B) (T x)
      _ = √‖rightInner (B := B) x
          (T.adjointOperator.comp T x)‖ := by
        rw [T.adjoint_inner]
        rfl
      _ ≤ √(‖T.adjointOperator.comp T‖ * ‖x‖ * ‖x‖) :=
        Real.sqrt_le_sqrt hinner
      _ = √‖T.adjointOperator.comp T‖ * ‖x‖ := by
        rw [mul_assoc, Real.sqrt_mul (norm_nonneg _) (‖x‖ * ‖x‖),
          Real.sqrt_mul_self (norm_nonneg x)]

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

Every adjointable T : E → F respects the right coefficient action: T(xb) = (Tx)b for x ∈ E and b
∈ B.
-/
theorem map_right_smul (T : AdjointableOperator B E F) (x : E) (b : B) :
    T (x <• b) = T x <• b := by
  apply ext_rightInner_left (B := B)
  intro y
  rw [T.adjoint_inner, rightInner_left_smul,
    rightInner_left_smul, T.adjoint_inner]

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E be a normed
right inner-product module over B, with compatible complex normed-space structures.

The adjointable endomorphisms of E are the bounded complex-linear maps E → E admitting bounded
adjoints for the coefficient-valued right inner product.
-/
abbrev End (B : Type uB) (E : Type uE)
    [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] :=
  AdjointableOperator B E E

instance : One (End B E) :=
  ⟨id⟩

instance : Mul (End B E) :=
  ⟨fun S T ↦ S.comp T⟩

instance : NonUnitalRing (End B E) := by
  apply Function.Injective.nonUnitalRing
    (fun T : End B E ↦ T.toContinuousLinearMap)
    (forwardAddHom_injective (B := B) (E := E) (F := E))
  · rfl
  · intro T S
    rfl
  · intro T S
    rfl
  · intro T
    rfl
  · intro T S
    exact map_sub (forwardAddHom (B := B) (E := E) (F := E)) T S
  · intro n T
    exact map_nsmul (forwardAddHom (B := B) (E := E) (F := E)) n T
  · intro n T
    exact map_zsmul (forwardAddHom (B := B) (E := E) (F := E)) n T

instance : Monoid (End B E) where
  mul := (· * ·)
  one := 1
  mul_assoc T S R := by
    ext x
    rfl
  one_mul T := by
    ext x
    rfl
  mul_one T := by
    ext x
    rfl
  npow := npowRec
  npow_zero _ := rfl
  npow_succ _ _ := rfl

instance : NatCast (End B E) :=
  ⟨Nat.unaryCast⟩

instance : Semiring (End B E) where
  zero_mul T := by
    ext x
    change (0 : E) = 0
    rfl
  mul_zero T := by
    ext x
    change T (0 : E) = 0
    exact map_zero T.toContinuousLinearMap
  left_distrib T S R := by
    ext x
    change T (S x + R x) = T (S x) + T (R x)
    exact map_add T.toContinuousLinearMap (S x) (R x)
  right_distrib T S R := by
    ext x
    change T (R x) + S (R x) = T (R x) + S (R x)
    rfl
  natCast_zero := rfl
  natCast_succ _ := rfl

instance : IntCast (End B E) :=
  ⟨Int.castDef⟩

instance : Ring (End B E) :=
  Ring.mk (neg_add_cancel := neg_add_cancel)

noncomputable instance : NonUnitalNormedRing (End B E) where
  dist_eq _ _ := rfl
  norm_mul_le S T := by
    change ‖S.toContinuousLinearMap.comp T.toContinuousLinearMap‖ ≤
      ‖S.toContinuousLinearMap‖ * ‖T.toContinuousLinearMap‖
    exact ContinuousLinearMap.opNorm_comp_le _ _

noncomputable instance : NormedRing (End B E) where
  dist_eq _ _ := rfl
  norm_mul_le S T := by
    change ‖S.toContinuousLinearMap.comp T.toContinuousLinearMap‖ ≤
      ‖S.toContinuousLinearMap‖ * ‖T.toContinuousLinearMap‖
    exact ContinuousLinearMap.opNorm_comp_le _ _

instance : StarAddMonoid (End B E) where
  star := adjointOperator
  star_involutive := adjointOperator_adjointOperator
  star_add T S := by
    ext x
    rfl

instance : StarRing (End B E) where
  star_add T S := by
    ext x
    rfl
  star_mul S T := by
    ext x
    rfl

instance [StarOrderedRing Bᵐᵒᵖ] : NormedStarGroup (End B E) where
  norm_star_le T := by
    rw [show star T = T.adjointOperator from rfl,
      norm_adjointOperator]

instance [StarOrderedRing Bᵐᵒᵖ] : CStarRing (End B E) where
  norm_mul_self_le T :=
    le_of_eq (norm_adjoint_comp_self T).symm

@[simp]
theorem one_apply (x : E) : (1 : End B E) x = x :=
  rfl

@[simp]
theorem mul_apply (S T : End B E) (x : E) :
    (S * T) x = S (T x) :=
  rfl

@[simp]
theorem star_apply (T : End B E) (x : E) :
    star T x = T.adjoint x :=
  rfl

@[simp]
theorem star_adjoint (T : End B E) :
    (star T).adjoint = T.toContinuousLinearMap :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E be a normed
right inner-product module over B, with compatible complex normed-space structures.

Adjointable endomorphisms of E form a complex algebra, with multiplication given by composition
and unit given by the identity map.
-/
noncomputable instance : Algebra ℂ (End B E) where
  toSMul := inferInstance
  algebraMap :=
    { toFun := fun c ↦ c • 1
      map_one' := by
        ext x
        change (1 : ℂ) • x = x
        exact one_smul ℂ x
      map_mul' := by
        intro c d
        ext x
        change (c * d) • x = c • d • x
        exact mul_smul c d x
      map_zero' := by
        ext x
        change (0 : ℂ) • x = 0
        exact zero_smul ℂ x
      map_add' := by
        intro c d
        ext x
        change (c + d) • x = c • x + d • x
        exact add_smul c d x }
  commutes' := by
    intro c T
    ext x
    change c • T x = T.toContinuousLinearMap (c • x)
    exact (T.toContinuousLinearMap.map_smul c x).symm
  smul_def' := by
    intro c T
    ext x
    rfl

@[simp]
theorem algebraMap_apply (c : ℂ) (x : E) :
    algebraMap ℂ (End B E) c x = c • x := by
  rfl

noncomputable instance : NormedAlgebra ℂ (End B E) where
  norm_smul_le c T := by
    rw [norm_eq, norm_eq]
    exact norm_smul_le c T.toContinuousLinearMap

instance : StarModule ℂ (End B E) where
  star_smul c T := smul_adjointOperator c T

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a complete normed right inner-product module over B,
with compatible complex normed-space structures.

The adjointable endomorphisms of E form a unital complex C*-algebra, with the operator norm and
adjoint involution.
-/
noncomputable instance [StarOrderedRing Bᵐᵒᵖ] [CompleteSpace E] :
    CStarAlgebra (End B E) where

end AdjointableOperator

end CStarModule
