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

public import MathlibExt.Analysis.CStarAlgebra.Grading
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Tactic.FinCases

/-!
# Algebraic Koszul tensor operations

The carrier is a grading-indexed copy of the ordinary complex algebraic
tensor. The product is a genuine bilinear map obtained from the finite
projection-sum braiding and the nonunital coefficient multiplication maps.
The signed star is a conjugate-linear map obtained from the corresponding
real-sign projection sum and the ordinary tensor star.

This is the strict operation prefix. Associativity, involutivity of the
signed star and reversal of products are further proof obligations; no
nonunital ring or star-ring instance is asserted here. The grading action
constructed below is an actual order-two linear action on the raw carrier.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped TensorProduct BigOperators

namespace CStarGrading

universe uA uB

/-- **Algebraic tensor carrier for two gradings.** Let `A,B` be nonunital complex C*-algebras with
`ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. The graded algebraic tensor carrier has underlying complex vector space `A
⊗[ℂ] B`, indexed by the chosen coefficient gradings. -/
structure AlgebraicTensorProduct
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (γA : CStarGrading A) (γB : CStarGrading B) where
  /-- The underlying ordinary complex tensor. -/
  toTensor : A ⊗[ℂ] B

namespace AlgebraicTensorProduct

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable (γA : CStarGrading A) (γB : CStarGrading B)

@[ext]
theorem ext {x y : AlgebraicTensorProduct γA γB}
    (h : x.toTensor = y.toTensor) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- **Carrier equivalence of the graded algebraic tensor.** Let `A,B` be nonunital complex C*-algebras
with `ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their
complex algebraic tensor product. Its underlying set is equivalent to the ordinary complex algebraic
tensor product `A ⊗[ℂ] B`. -/
def equiv : AlgebraicTensorProduct γA γB ≃ A ⊗[ℂ] B where
  toFun := toTensor
  invFun := AlgebraicTensorProduct.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (AlgebraicTensorProduct γA γB) :=
  (equiv γA γB).addCommGroup

instance instModule : Module ℂ (AlgebraicTensorProduct γA γB) := by
  let e : AlgebraicTensorProduct γA γB ≃+ A ⊗[ℂ] B :=
    { equiv γA γB with map_add' := fun _ _ => rfl }
  exact e.module ℂ

/-- **Linear equivalence of the graded algebraic tensor.** Let `A,B` be nonunital complex C*-algebras
with `ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their
complex algebraic tensor product. The carrier identification with `A ⊗[ℂ] B` is a complex-linear
equivalence. -/
def linearEquiv : AlgebraicTensorProduct γA γB ≃ₗ[ℂ] A ⊗[ℂ] B := by
  let e : AlgebraicTensorProduct γA γB ≃+ A ⊗[ℂ] B :=
    { equiv γA γB with map_add' := fun _ _ => rfl }
  exact e.linearEquiv ℂ

/-- **Inclusion of an algebraic tensor into the graded carrier.** Let `A,B` be nonunital complex
C*-algebras with `ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and
use their complex algebraic tensor product. The carrier identification gives a complex-linear map
from `A ⊗[ℂ] B` into the graded algebraic tensor carrier. -/
def ofTensor : A ⊗[ℂ] B →ₗ[ℂ] AlgebraicTensorProduct γA γB :=
  (linearEquiv γA γB).symm.toLinearMap

@[simp]
theorem toTensor_ofTensor (z : A ⊗[ℂ] B) :
    (ofTensor γA γB z).toTensor = z := rfl

@[simp]
theorem ofTensor_toTensor (z : AlgebraicTensorProduct γA γB) :
    ofTensor γA γB z.toTensor = z := by cases z; rfl

/-- **Elementary tensor in the graded carrier.** Let `A,B` be nonunital complex C*-algebras with `ℤ/2ℤ`
gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. For `a ∈ A`, `b ∈ B`, the elementary tensor is the element corresponding
to `a ⊗ b`. -/
def tmul (a : A) (b : B) : AlgebraicTensorProduct γA γB :=
  ofTensor γA γB (a ⊗ₜ[ℂ] b)

@[simp]
theorem toTensor_tmul (a : A) (b : B) :
    (tmul γA γB a b).toTensor = a ⊗ₜ[ℂ] b := rfl

/-- **Koszul sign operator on the algebraic tensor.** Let `A,B` be nonunital complex C*-algebras with
`ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. The complex-linear sign operator sends `a ⊗ b` to `∑ p q, (-1)^(p q) a_p ⊗
b_q`. -/
def signProjection : A ⊗[ℂ] B →ₗ[ℂ] A ⊗[ℂ] B :=
  ∑ p : ZMod 2, ∑ q : ZMod 2,
    degreeSign (p * q) •
      TensorProduct.map (γA.partProjection p).toLinearMap
        (γB.partProjection q).toLinearMap

/-- **Koszul sign formula for an elementary tensor.** Let `A,B` be nonunital complex C*-algebras with
`ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. For every `a ∈ A`, `b ∈ B`, the sign operator has value `∑ p q, (-1)^(p q)
a_p ⊗ b_q`, summing over both parity degrees. -/
theorem signProjection_tmul (a : A) (b : B) :
    signProjection γA γB (a ⊗ₜ[ℂ] b) =
      ∑ p : ZMod 2, ∑ q : ZMod 2,
        degreeSign (p * q) •
          (γA.partProjection p a ⊗ₜ[ℂ] γB.partProjection q b) := by
  simp only [signProjection, LinearMap.sum_apply, LinearMap.smul_apply,
    TensorProduct.map_tmul, ContinuousLinearMap.coe_coe]

/-- **Signed exchange of algebraic tensor factors.** Let `A,B` be nonunital complex C*-algebras with
`ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. The complex-linear braiding `A ⊗ B → B ⊗ A` sends `a ⊗ b` to `∑ p q,
(-1)^(p q) b_q ⊗ a_p`. -/
def rawBraiding : A ⊗[ℂ] B →ₗ[ℂ] B ⊗[ℂ] A :=
  (TensorProduct.comm ℂ A B).toLinearMap.comp (signProjection γA γB)

/-- **Signed braiding formula on an elementary tensor.** Let `A,B` be nonunital complex C*-algebras with
`ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. For all `a ∈ A`, `b ∈ B`, braiding gives `∑ p q, (-1)^(p q) b_q ⊗ a_p` in
`B ⊗ A`. -/
theorem rawBraiding_tmul (a : A) (b : B) :
    rawBraiding γA γB (a ⊗ₜ[ℂ] b) =
      ∑ p : ZMod 2, ∑ q : ZMod 2,
        degreeSign (p * q) •
          (γB.partProjection q b ⊗ₜ[ℂ] γA.partProjection p a) := by
  change (TensorProduct.comm ℂ A B)
      (signProjection γA γB (a ⊗ₜ[ℂ] b)) = _
  simp only [signProjection, LinearMap.sum_apply, LinearMap.smul_apply,
    TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    map_sum, map_smul, TensorProduct.comm_tmul]

open TensorProduct (assoc map) in
/-- **Signed bilinear tensor multiplication.** Let `A,B` be nonunital complex C*-algebras with `ℤ/2ℤ`
gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. The complex-bilinear map sends `(a ⊗ b,c ⊗ d)` to `∑ p q, (-1)^(p q) (a
c_q) ⊗ (b_p d)`. The signed reassociation follows Eric Wieser's graded tensor-product construction
using the nonunital multiplications of the factors. -/
def rawMulMap : A ⊗[ℂ] B →ₗ[ℂ] A ⊗[ℂ] B →ₗ[ℂ] A ⊗[ℂ] B := by
  refine TensorProduct.curry ?_
  refine map (LinearMap.mul' ℂ A) (LinearMap.mul' ℂ B) ∘ₗ ?_
  refine (assoc ℂ _ _ _).symm.toLinearMap ∘ₗ
    .lTensor _ ?_ ∘ₗ (assoc ℂ _ _ _).toLinearMap
  refine (assoc ℂ _ _ _).toLinearMap ∘ₗ
    .rTensor _ ?_ ∘ₗ (assoc ℂ _ _ _).symm.toLinearMap
  exact rawBraiding γB γA

/-- **Signed multiplication on arbitrary elementary tensors.** Let `A,B` be nonunital complex
C*-algebras with `ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and
use their complex algebraic tensor product. For `a,c ∈ A` and `b,d ∈ B`, the bilinear multiplication
of `a ⊗ b` and `c ⊗ d` is `∑ p q, (-1)^(p q) (a c_q) ⊗ (b_p d)`. -/
theorem rawMulMap_tmul_tmul (a c : A) (b d : B) :
    rawMulMap γA γB (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] d) =
      ∑ p : ZMod 2, ∑ q : ZMod 2,
        degreeSign (p * q) •
          ((a * γA.partProjection q c) ⊗ₜ[ℂ]
            (γB.partProjection p b * d)) := by
  rw [rawMulMap]
  dsimp only [TensorProduct.curry_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.assoc_tmul,
    TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  rw [rawBraiding_tmul]
  simp only [map_sum, TensorProduct.tmul_sum,
    TensorProduct.sum_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul,
    TensorProduct.map_tmul, LinearMap.mul'_apply, smul_mul_assoc]

/-- **Conjugate-linear star of the graded tensor.** Let `A,B` be nonunital complex C*-algebras with
`ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. The conjugate-linear star map on `A ⊗ B` sends `a ⊗ b` to `∑ p q, (-1)^(p
q) (a_p)* ⊗ (b_q)*`. -/
def rawStarMap : A ⊗[ℂ] B →ₗ⋆[ℂ] A ⊗[ℂ] B :=
  (starLinearEquiv ℂ (A := A ⊗[ℂ] B)).toLinearMap.comp
    (signProjection γA γB)

/-- **Signed star formula on an elementary tensor.** Let `A,B` be nonunital complex C*-algebras with
`ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. For all `a ∈ A`, `b ∈ B`, the conjugate-linear star map has value `∑ p q,
(-1)^(p q) (a_p)* ⊗ (b_q)*`. -/
theorem rawStarMap_tmul (a : A) (b : B) :
    rawStarMap γA γB (a ⊗ₜ[ℂ] b) =
      ∑ p : ZMod 2, ∑ q : ZMod 2,
        degreeSign (p * q) •
          (star (γA.partProjection p a) ⊗ₜ[ℂ]
            star (γB.partProjection q b)) := by
  change star (signProjection γA γB (a ⊗ₜ[ℂ] b)) = _
  simp only [signProjection, LinearMap.sum_apply, LinearMap.smul_apply,
    TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    star_sum, star_smul, star_degreeSign, TensorProduct.star_tmul]

/-- **Bilinear multiplication of the graded tensor carrier.** Let `A,B` be nonunital complex C*-algebras
with `ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their
complex algebraic tensor product. The signed complex-bilinear multiplication is transported to the
graded carrier; on elementary tensors it uses the Koszul sign from the crossing `B` and `A` factors. -/
def mulMap : AlgebraicTensorProduct γA γB →ₗ[ℂ]
    AlgebraicTensorProduct γA γB →ₗ[ℂ] AlgebraicTensorProduct γA γB :=
  ((rawMulMap γA γB).compl₁₂ (linearEquiv γA γB).toLinearMap
    (linearEquiv γA γB).toLinearMap).compr₂ (ofTensor γA γB)

instance instMul : Mul (AlgebraicTensorProduct γA γB) where
  mul x y := mulMap γA γB x y

/-- **Conjugate-linear involution of the graded tensor carrier.** Let `A,B` be nonunital complex
C*-algebras with `ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and
use their complex algebraic tensor product. The signed conjugate-linear star map is transported to
the graded carrier, with sign `(-1)^(p q)` on tensors of degrees `p,q`. -/
def starMap : AlgebraicTensorProduct γA γB →ₗ⋆[ℂ]
    AlgebraicTensorProduct γA γB :=
  (ofTensor γA γB).comp ((rawStarMap γA γB).comp (linearEquiv γA γB).toLinearMap)

instance instStar : Star (AlgebraicTensorProduct γA γB) where
  star x := starMap γA γB x

/-- **Ordinary tensor formula for a graded product.** Let `A,B` be nonunital complex C*-algebras with
`ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. For `a,c ∈ A` and `b,d ∈ B`, the product of their elementary graded
tensors, identified in `A ⊗ B`, is `∑ p q, (-1)^(p q) (a c_q) ⊗ (b_p d)`. -/
theorem toTensor_tmul_mul_tmul (a c : A) (b d : B) :
    (tmul γA γB a b * tmul γA γB c d).toTensor =
      ∑ p : ZMod 2, ∑ q : ZMod 2,
        degreeSign (p * q) •
          ((a * γA.partProjection q c) ⊗ₜ[ℂ]
            (γB.partProjection p b * d)) := by
  change rawMulMap γA γB (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] d) = _
  exact rawMulMap_tmul_tmul γA γB a c b d

/-- **Ordinary tensor formula for graded star.** Let `A,B` be nonunital complex C*-algebras with `ℤ/2ℤ`
gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. For arbitrary `a ∈ A`, `b ∈ B`, the star of their elementary graded
tensor, identified in `A ⊗ B`, is `∑ p q, (-1)^(p q) (a_p)* ⊗ (b_q)*`. -/
theorem toTensor_star_tmul (a : A) (b : B) :
    (star (tmul γA γB a b)).toTensor =
      ∑ p : ZMod 2, ∑ q : ZMod 2,
        degreeSign (p * q) •
          (star (γA.partProjection p a) ⊗ₜ[ℂ]
            star (γB.partProjection q b)) := by
  change rawStarMap γA γB (a ⊗ₜ[ℂ] b) = _
  exact rawStarMap_tmul γA γB a b

private theorem projection_eq_if_of_mem
    {C : Type*} [NonUnitalCStarAlgebra C] (γ : CStarGrading C)
    {m : ZMod 2} {c : C} (hc : c ∈ γ.part m) (n : ZMod 2) :
    γ.partProjection n c = if n = m then c else 0 := by
  by_cases h : n = m
  · subst n
    rw [ite_eq_left rfl]
    exact γ.partProjection_eq_self_of_mem hc
  · rw [ite_eq_right h]
    exact γ.partProjection_eq_zero_of_mem_ne hc (Ne.symm h)

/-- **Koszul product sign from crossing degrees.** Let `A,B` be nonunital complex C*-algebras with
`ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. For `a,c ∈ A` and `b,d ∈ B`, if `b` has degree `p` and `c` has degree `q`,
then `(a ⊗ b)(c ⊗ d) = (-1)^(p q) (a c) ⊗ (b d)`. The degrees of `a` and `d` are unrestricted. -/
theorem tmul_mul_tmul_of_mem (a c : A) (b d : B)
    {p q : ZMod 2} (hb : b ∈ γB.part p) (hc : c ∈ γA.part q) :
    tmul γA γB a b * tmul γA γB c d =
      degreeSign (p * q) • tmul γA γB (a * c) (b * d) := by
  apply (linearEquiv γA γB).injective
  change (tmul γA γB a b * tmul γA γB c d).toTensor =
    degreeSign (p * q) • ((a * c) ⊗ₜ[ℂ] (b * d))
  rw [toTensor_tmul_mul_tmul]
  simp [projection_eq_if_of_mem γA hc, projection_eq_if_of_mem γB hb,
    TensorProduct.ite_tmul, TensorProduct.tmul_ite]

/-- **Star of a homogeneous elementary tensor.** Let `A,B` be nonunital complex C*-algebras with `ℤ/2ℤ`
gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. If `a ∈ A` has degree `p` and `b ∈ B` has degree `q`, then `(a ⊗ b)* =
(-1)^(p q) a* ⊗ b*`. -/
theorem star_tmul_of_mem (a : A) (b : B)
    {p q : ZMod 2} (ha : a ∈ γA.part p) (hb : b ∈ γB.part q) :
    star (tmul γA γB a b) =
      degreeSign (p * q) • tmul γA γB (star a) (star b) := by
  apply (linearEquiv γA γB).injective
  change (star (tmul γA γB a b)).toTensor =
    degreeSign (p * q) • (star a ⊗ₜ[ℂ] star b)
  rw [toTensor_star_tmul]
  simp [projection_eq_if_of_mem γA ha, projection_eq_if_of_mem γB hb,
    apply_ite, TensorProduct.ite_tmul]

/-- **Factorwise grading generator of the algebraic tensor.** Let `A,B` be nonunital complex C*-algebras
with `ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their
complex algebraic tensor product. The complex-linear equivalence `a ⊗ b ↦ γ_A(1)a ⊗ γ_B(1)b` is the
factorwise degree-one generator. -/
def generator : AlgebraicTensorProduct γA γB ≃ₗ[ℂ]
    AlgebraicTensorProduct γA γB := by
  let LA : A ≃ₗ[ℂ] A := LinearEquiv.ofBijective
    (LinearMap.ofClass γA.generatorAut) γA.generatorAut.bijective
  let LB : B ≃ₗ[ℂ] B := LinearEquiv.ofBijective
    (LinearMap.ofClass γB.generatorAut) γB.generatorAut.bijective
  exact (linearEquiv γA γB).trans
    ((TensorProduct.congr LA LB).trans (linearEquiv γA γB).symm)

@[simp]
theorem generator_tmul (a : A) (b : B) :
    generator γA γB (tmul γA γB a b) =
      tmul γA γB (γA.generatorAut a) (γB.generatorAut b) := by
  apply (linearEquiv γA γB).injective
  change TensorProduct.map (LinearMap.ofClass γA.generatorAut)
      (LinearMap.ofClass γB.generatorAut) (a ⊗ₜ[ℂ] b) =
    γA.generatorAut a ⊗ₜ[ℂ] γB.generatorAut b
  exact TensorProduct.map_tmul _ _ a b

/-- **The algebraic tensor generator has order two.** Let `A,B` be nonunital complex C*-algebras with
`ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. The factorwise degree-one generator is an involution on the entire
algebraic tensor carrier. -/
theorem generator_involutive : Function.Involutive (generator γA γB) := by
  have h : ∀ z : A ⊗[ℂ] B,
      generator γA γB (generator γA γB (ofTensor γA γB z)) =
        ofTensor γA γB z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
        change generator γA γB (generator γA γB (tmul γA γB a b)) =
          tmul γA γB a b
        rw [generator_tmul, generator_tmul,
          γA.generator_involutive, γB.generator_involutive]
    | add x y hx hy =>
        simp only [map_add, hx, hy]
  intro z
  simpa only [ofTensor_toTensor] using h z.toTensor

/-- **Linear parity action on the algebraic tensor.** Let `A,B` be nonunital complex C*-algebras with
`ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their complex
algebraic tensor product. Degree zero acts by the identity and degree one acts by the factorwise
generator `γ_A(1) ⊗ γ_B(1)`. -/
def gradingAction (n : ZMod 2) : AlgebraicTensorProduct γA γB ≃ₗ[ℂ]
    AlgebraicTensorProduct γA γB :=
  if n = 0 then LinearEquiv.refl ℂ _ else generator γA γB

@[simp]
theorem gradingAction_zero (z : AlgebraicTensorProduct γA γB) :
    gradingAction γA γB 0 z = z := by simp [gradingAction]

/-- **Composition of the algebraic tensor parity action.** Let `A,B` be nonunital complex C*-algebras
with `ℤ/2ℤ` gradings `γ_A,γ_B`. Write `a_p` and `b_q` for their degree projections, and use their
complex algebraic tensor product. For `m,n ∈ ℤ/2ℤ` and any tensor `z`, action by `m+n` equals action
by `n` followed by action by `m`. -/
theorem gradingAction_add (m n : ZMod 2) (z : AlgebraicTensorProduct γA γB) :
    gradingAction γA γB (m + n) z =
      gradingAction γA γB m (gradingAction γA γB n z) := by
  have h0 : gradingAction γA γB (0 : ZMod 2) = LinearEquiv.refl ℂ _ := by
    unfold gradingAction
    exact ite_eq_left rfl
  have h1 : gradingAction γA γB (1 : ZMod 2) = generator γA γB := by
    unfold gradingAction
    exact ite_eq_right (show (1 : ZMod 2) ≠ 0 by decide)
  have hm : m = 0 ∨ m = 1 := by
    fin_cases m
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hn : n = 0 ∨ n = 1 := by
    fin_cases n
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hm with rfl | rfl <;> rcases hn with rfl | rfl
  · simp only [zero_add, h0, LinearEquiv.refl_apply]
  · simp only [zero_add, h0, h1, LinearEquiv.refl_apply]
  · simp only [add_zero, h0, h1, LinearEquiv.refl_apply]
  · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    simpa only [h11, h0, h1, LinearEquiv.refl_apply] using
      (generator_involutive γA γB z).symm

end AlgebraicTensorProduct

end CStarGrading
