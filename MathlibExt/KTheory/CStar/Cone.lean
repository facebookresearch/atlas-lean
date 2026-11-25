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

public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.ZeroAtInfty

/-!
# The cone of a C-star algebra

The cone of a complex nonunital C-star algebra is the algebra of continuous
functions on the nonnegative real half-line which vanish at infinity.
-/

@[expose] public section

open scoped CStarAlgebra NNReal ZeroAtInfty

namespace CStarKTheory

noncomputable section

universe u v w

/-- Let `A` be a possibly nonunital complex C*-algebra. The cone of each algebra is its
supremum-norm algebra of continuous functions on the nonnegative reals which vanish at infinity.

The canonical cone `C₀(ℝ≥0, A)`. -/
abbrev Cone (A : Type u) [NonUnitalCStarAlgebra A] :=
  C₀(ℝ≥0, A)

namespace Cone

/-- Let `A` be a possibly nonunital complex C*-algebra. The cone of each algebra is its
supremum-norm algebra of continuous functions on the nonnegative reals which vanish at infinity.

Evaluation of a cone function at the endpoint zero. -/
def evalZero (A : Type u) [NonUnitalCStarAlgebra A] :
    Cone A →⋆ₙₐ[ℂ] A where
  toFun f := f 0
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem evalZero_apply
    (A : Type u) [NonUnitalCStarAlgebra A] (f : Cone A) :
    evalZero A f = f 0 :=
  rfl

/-- Let `A`, `B` be possibly nonunital complex C*-algebras. The cone of each algebra is its
supremum-norm algebra of continuous functions on the nonnegative reals which vanish at infinity.

Pointwise coefficient postcomposition on cones. -/
def map
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : A →⋆ₙₐ[ℂ] B) : Cone A →⋆ₙₐ[ℂ] Cone B :=
  ZeroAtInftyContinuousMap.nonUnitalStarAlgHom_postcomp phi

@[simp]
theorem map_apply
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : A →⋆ₙₐ[ℂ] B) (f : Cone A) (t : ℝ≥0) :
    map phi f t = phi (f t) :=
  rfl

@[simp]
theorem map_id (A : Type u) [NonUnitalCStarAlgebra A] :
    map (NonUnitalStarAlgHom.id ℂ A) =
      NonUnitalStarAlgHom.id ℂ (Cone A) :=
  ZeroAtInftyContinuousMap.nonUnitalStarAlgHom_postcomp_id ℝ≥0 A

theorem map_comp
    {A : Type u} {B : Type v} {C : Type w}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (phi : A →⋆ₙₐ[ℂ] B) (psi : B →⋆ₙₐ[ℂ] C) :
    map (psi.comp phi) = (map psi).comp (map phi) :=
  ZeroAtInftyContinuousMap.nonUnitalStarAlgHom_postcomp_comp psi phi

/-- Let `A`, `B` be possibly nonunital complex C*-algebras. The cone of each algebra is its
supremum-norm algebra of continuous functions on the nonnegative reals which vanish at infinity.

Evaluation at zero is natural under coefficient homomorphisms. -/
theorem evalZero_naturality
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : A →⋆ₙₐ[ℂ] B) :
    (evalZero B).comp (map phi) = phi.comp (evalZero A) := by
  apply NonUnitalStarAlgHom.ext
  intro f
  rfl

end Cone

end

end CStarKTheory
