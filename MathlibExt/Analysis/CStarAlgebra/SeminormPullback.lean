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

public import MathlibExt.Analysis.CStarAlgebra.Seminorm
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Pulling back an actual C-star norm along a nonunital star-algebra homomorphism

The norm of the original target, composed with the actual homomorphism,
is a complex seminorm on the original source. Multiplication, involution
and the square law follow from the homomorphism's preservation fields and
the target's actual C-star-ring norm laws.

Source and target universes are independent. The source has no supplied
norm or topology, and the homomorphism need not preserve a unit, be
injective or have nonzero image. No completed model is chosen.

General composition also transports any actual C-star seminorm on a
norm-free nonunital target. It reuses the computed composition of complex
seminorms and retains the original multiplication and involution.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarSeminorm

universe uA uB

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarRing A] [StarModule ℂ A]
section Composition

variable {B : Type uB} [NonUnitalRing B] [Module ℂ B]
variable [IsScalarTower ℂ B B] [SMulCommClass ℂ B B] [StarRing B] [StarModule ℂ B]

/-- **Pullback of a C*-seminorm.** Let `A,B` be nonunital complex star algebras with scalar-compatible
involutions. For a C*-seminorm `p` on `B` and a nonunital complex star homomorphism `φ : A → B`, the
function `x ↦ p(φ(x))` is a C*-seminorm on `A`. -/
def comp (p : CStarSeminorm B) (φ : A →⋆ₙₐ[ℂ] B) : CStarSeminorm A := by
  let f : A →ₗ[ℂ] B :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun c x => map_smul φ c x }
  refine
    { toSeminorm := p.toSeminorm.comp f
      mul_le' := ?_
      map_star' := ?_
      cstar_identity' := ?_ }
  · intro x y
    change p (φ (x * y)) ≤ p (φ x) * p (φ y)
    rw [map_mul]
    exact p.mul_le' (φ x) (φ y)
  · intro x
    change p (φ (star x)) = p (φ x)
    rw [StarHomClass.map_star φ x]
    exact p.map_star (φ x)
  · intro x
    change p (φ (star x * x)) = p (φ x) ^ 2
    rw [map_mul, StarHomClass.map_star φ x]
    exact p.map_star_mul_self (φ x)

/-- **Evaluation of a pulled-back C*-seminorm.** Let `A,B` be nonunital complex star algebras with
scalar-compatible involutions. For a C*-seminorm `p` on `B`, a nonunital complex star homomorphism
`φ : A → B`, and `x ∈ A`, the pulled-back seminorm has value `p(φ(x))`. -/
@[simp]
theorem comp_apply (p : CStarSeminorm B) (φ : A →⋆ₙₐ[ℂ] B) (x : A) :
    p.comp φ x = p (φ x) :=
  rfl

end Composition

variable {B : Type uB} [NonUnitalNormedRing B] [NormedSpace ℂ B] [StarRing B] [CStarRing B]

/-- **Pullback of a C*-norm.** Let `A` be a nonunital complex star algebra with scalar-compatible
involution, let `B` be a nonunital normed ring satisfying the C*-identity and carrying a complex
normed vector-space structure, and let `φ : A → B` be a nonunital complex star homomorphism.
Completeness of `B` is not required. The function `x ↦ ‖φ(x)‖` is a C*-seminorm on `A`. -/
def ofNonUnitalStarAlgHom (φ : A →⋆ₙₐ[ℂ] B) : CStarSeminorm A := by
  let f : A →ₗ[ℂ] B :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun c x => map_smul φ c x }
  refine
    { toSeminorm := (normSeminorm ℂ B).comp f
      mul_le' := ?_
      map_star' := ?_
      cstar_identity' := ?_ }
  · intro x y
    change ‖φ (x * y)‖ ≤ ‖φ x‖ * ‖φ y‖
    rw [map_mul]
    exact norm_mul_le _ _
  · intro x
    change ‖φ (star x)‖ = ‖φ x‖
    rw [StarHomClass.map_star φ x, norm_star]
  · intro x
    change ‖φ (star x * x)‖ = ‖φ x‖ ^ 2
    rw [map_mul, StarHomClass.map_star φ x, CStarRing.norm_star_mul_self, pow_two]

/-- **Value of a pulled-back C*-norm.** Let `A` be a nonunital complex star algebra with
scalar-compatible involution, let `B` be a nonunital normed ring satisfying the C*-identity and
carrying a complex normed vector-space structure, and let `φ : A → B` be a nonunital complex star
homomorphism. Completeness of `B` is not required. For every `x ∈ A`, the pulled-back C*-seminorm
equals `‖φ(x)‖`. -/
@[simp]
theorem ofNonUnitalStarAlgHom_apply (φ : A →⋆ₙₐ[ℂ] B) (x : A) :
    ofNonUnitalStarAlgHom φ x = ‖φ x‖ :=
  rfl

end CStarSeminorm
