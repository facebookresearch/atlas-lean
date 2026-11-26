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

public import Mathlib.Analysis.CStarAlgebra.Module.Synonym
public import Mathlib.Analysis.InnerProductSpace.Basic
public import MathlibExt.Analysis.CStarAlgebra.Module.Right

import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Algebra.Module.RingHom

/-!
# Complex inner-product spaces as right C-star modules

For a complex normed inner-product space `H`, `ScalarRight H` is the carrier `WithCStarModule
ℂᵐᵒᵖ H`. Write `q : ScalarRight H ≃L[ℂ] H` for `equivL H`. The right scalar action and inner
product satisfy `q (x <• c) = c • q x` and `rightInner x y = ⟪q x, q y⟫_ℂ`. The opposite-valued
inner product is `MulOpposite.op ⟪q x, q y⟫_ℂ`, with the conjugate-linear-first convention.

The norm is `‖q x‖`; the uniformity and bornology are pulled back along `q`. Consequently `q` is
an isometry and `ScalarRight H` is complete exactly when `H` is complete. The module
construction also applies to incomplete inner-product spaces. The coefficient order is the order
on self-adjoint complex scalars, under the `ComplexOrder` scope.

The inner-product convention agrees with Lance Chapter 1, Blackadar §13.1 and Connes II.Appendix
A.
-/

public section

open scoped ComplexOrder InnerProductSpace RightActions

universe u

/-- **Complex spaces as right scalar modules.** `ScalarRight H` is `WithCStarModule ℂᵐᵒᵖ H`,
identified with `H` by `WithCStarModule.equiv ℂᵐᵒᵖ H`. -/
abbrev ScalarRight (H : Type u) : Type u :=
  WithCStarModule ℂᵐᵒᵖ H

namespace ScalarRight

/-- **Complex scalar multiplication.** For a complex module `H`, the complex module structure on
`ScalarRight H` satisfies `q (c • x) = c • q x`, where `q = WithCStarModule.equiv ℂᵐᵒᵖ H`. -/
@[expose, instance_reducible]
def instComplexModule (H : Type u) [AddCommGroup H] [Module ℂ H] :
    Module ℂ (ScalarRight H) :=
  inferInstanceAs (Module ℂ H)

/-- **Right complex scalar action.** For a complex module `H` with an additive group, put `q =
WithCStarModule.equiv ℂᵐᵒᵖ H`. For `a : ℂᵐᵒᵖ` define `a • x = q.symm (a.unop • q x)`. Right
multiplication by `c : ℂ` thus corresponds to scalar multiplication by `c` on `H`. -/
@[expose, instance_reducible]
def instOppositeSMul (H : Type u) [AddCommGroup H] [Module ℂ H] :
    SMul ℂᵐᵒᵖ (ScalarRight H) where
  smul a x :=
    (WithCStarModule.equiv ℂᵐᵒᵖ H).symm
      (MulOpposite.unop a • WithCStarModule.equiv ℂᵐᵒᵖ H x)

/-- **Module structure over opposite complex scalars.** For a complex module `H` with an additive
group, let `q = WithCStarModule.equiv ℂᵐᵒᵖ H`. The action `a • x = q.symm (a.unop • q x)`
makes `ScalarRight H` an `ℂᵐᵒᵖ`-module. -/
@[expose, instance_reducible]
def instOppositeModule (H : Type u) [AddCommGroup H] [Module ℂ H] :
    Module ℂᵐᵒᵖ (ScalarRight H) := by
  let : Module ℂ (ScalarRight H) := instComplexModule H
  exact Module.compHom (ScalarRight H)
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun a b => mul_comm (MulOpposite.unop b) (MulOpposite.unop a) }

/-- **Agreement of the right scalar actions.** The scalar action of `instOppositeModule H` equals
`instOppositeSMul H`; both send `a, x` to `q.symm (a.unop • q x)`. -/
theorem oppositeModule_toSMul
    (H : Type u) [AddCommGroup H] [Module ℂ H] :
    (instOppositeModule H).toSMul = instOppositeSMul H :=
  rfl

/-- **Norm and metric on the right scalar module.** For a normed additive group `H`, let `q =
WithCStarModule.equiv ℂᵐᵒᵖ H`. Pull back the norm and metric along this equivalence, so `‖x‖ =
‖q x‖` and `dist x y = dist (q x) (q y)`. -/
@[expose, instance_reducible]
def instNormedAddCommGroup (H : Type u) [NormedAddCommGroup H] :
    NormedAddCommGroup (ScalarRight H) :=
  NormedAddCommGroup.induced (ScalarRight H) H
    (WithCStarModule.addEquiv ℂᵐᵒᵖ H)
    (WithCStarModule.equiv ℂᵐᵒᵖ H).injective

/-- **Uniformity of the right scalar module.** The uniformity of `instNormedAddCommGroup H` is the
comap of the uniformity of `H` along `WithCStarModule.equiv ℂᵐᵒᵖ H`. -/
theorem normedAddCommGroup_uniformSpace
    (H : Type u) [NormedAddCommGroup H] :
    (instNormedAddCommGroup H).toUniformSpace =
      (inferInstance : UniformSpace H).comap (WithCStarModule.equiv ℂᵐᵒᵖ H) :=
  rfl

/-- **Bounded sets in the right scalar module.** Its bornology is induced by `q =
WithCStarModule.equiv ℂᵐᵒᵖ H`; boundedness is measured by the corresponding subset of `H`. -/
theorem normedAddCommGroup_bornology
    (H : Type u) [NormedAddCommGroup H] :
    (instNormedAddCommGroup H).toBornology =
      Bornology.induced (WithCStarModule.equiv ℂᵐᵒᵖ H) :=
  rfl

/-- **Complex normed-space structure.** The norm `‖x‖ = ‖q x‖` and complex action `q (c • x) = c •
q x` make `ScalarRight H` a complex normed space whenever `H` is one. -/
@[expose, instance_reducible]
def instNormedSpace
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H] :
    let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    NormedSpace ℂ (ScalarRight H) := by
  let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := instComplexModule H
  exact
    { toModule := instComplexModule H
      norm_smul_le := fun c x => by
        change ‖c • WithCStarModule.equiv ℂᵐᵒᵖ H x‖ ≤
          ‖c‖ * ‖WithCStarModule.equiv ℂᵐᵒᵖ H x‖
        exact norm_smul_le _ _ }

/-- **Scalar action underlying the normed space.** `(instNormedSpace H).toModule =
instComplexModule H`; both actions satisfy `q (c • x) = c • q x`. -/
theorem normedSpace_toModule
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H] :
    let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    (instNormedSpace H).toModule = instComplexModule H := by
  let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  rfl

/-- **Identification with the complex normed space.** `equivL H : ScalarRight H ≃L[ℂ] H` is the
continuous complex-linear identification `q`, for the norm and scalar structures defined in
this module. -/
@[expose]
def equivL (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H] :
    let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let : Module ℂ (ScalarRight H) := instComplexModule H
    ScalarRight H ≃L[ℂ] H := by
  let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := instComplexModule H
  exact WithCStarModule.equivL (A := ℂᵐᵒᵖ) (E := H) ℂ

theorem equivL_apply
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H] (x : ScalarRight H) :
    equivL H x = WithCStarModule.equiv ℂᵐᵒᵖ H x :=
  rfl

theorem equivL_symm_apply
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H] (x : H) :
    (equivL H).symm x = (WithCStarModule.equiv ℂᵐᵒᵖ H).symm x :=
  rfl

/-- **Norm under scalar-module identification.** For a normed additive group `H`, the norm of `x`
in `instNormedAddCommGroup H` is `‖WithCStarModule.equiv ℂᵐᵒᵖ H x‖`. -/
@[simp]
theorem norm_apply
    (H : Type u) [NormedAddCommGroup H] (x : ScalarRight H) :
    (instNormedAddCommGroup H).toNorm.norm x =
      ‖WithCStarModule.equiv ℂᵐᵒᵖ H x‖ :=
  rfl

/-- **Isometry of the scalar-module identification.** For a complex normed space `H`, `equivL H`
preserves distances for `instNormedAddCommGroup H`. -/
theorem isometry_equivL
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H] :
    let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    Isometry (equivL H) := by
  let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  exact Isometry.of_dist_eq fun _ _ => rfl

/-- **Opposite scalar multiplication under identification.** For `c : ℂ`, `q ((instOppositeSMul
H).smul (MulOpposite.op c) x) = c • q x`, where `q = equivL H`. -/
@[simp]
theorem op_smul_apply
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H]
    (c : ℂ) (x : ScalarRight H) :
    equivL H ((instOppositeSMul H).smul (MulOpposite.op c) x) =
      c • equivL H x :=
  rfl

/-- **Right scalar multiplication under identification.** With `instOppositeSMul H`, `equivL H (x
<• c) = c • equivL H x` for every `x` and `c : ℂ`. -/
@[simp]
theorem right_smul_apply
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H]
    (x : ScalarRight H) (c : ℂ) :
    let : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    equivL H (x <• c) = c • equivL H x := by
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  rfl

/-- **Opposite-valued scalar inner product.** For a complex inner-product space `H`, define the
inner product on `ScalarRight H` by `inner x y = MulOpposite.op ⟪q x, q y⟫_ℂ`. -/
@[expose, instance_reducible]
def instInner (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Inner ℂᵐᵒᵖ (ScalarRight H) where
  inner x y := MulOpposite.op
    ⟪WithCStarModule.equiv ℂᵐᵒᵖ H x, WithCStarModule.equiv ℂᵐᵒᵖ H y⟫_ℂ

@[simp]
theorem op_inner_apply
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : ScalarRight H) :
    (instInner H).inner x y = MulOpposite.op ⟪equivL H x, equivL H y⟫_ℂ :=
  rfl

/-- **Right C-star module from an inner-product space.** The norm, complex action, right action
and inner product defined above make `ScalarRight H` a `CStarModule ℂᵐᵒᵖ`. Its right inner
product is `⟪q x, q y⟫_ℂ` and its norm is `‖q x‖`; completeness of `H` is not required. -/
@[expose, instance_reducible]
def cStarModule
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let : Module ℂ (ScalarRight H) := instComplexModule H
    let : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    CStarModule ℂᵐᵒᵖ (ScalarRight H) := by
  let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := instComplexModule H
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  exact {
    toInner := instInner H
    inner_add_right := by
      intro x y z
      apply MulOpposite.unop_injective
      change
        ⟪WithCStarModule.equiv ℂᵐᵒᵖ H x,
          WithCStarModule.equiv ℂᵐᵒᵖ H y + WithCStarModule.equiv ℂᵐᵒᵖ H z⟫_ℂ =
        ⟪WithCStarModule.equiv ℂᵐᵒᵖ H x, WithCStarModule.equiv ℂᵐᵒᵖ H y⟫_ℂ +
          ⟪WithCStarModule.equiv ℂᵐᵒᵖ H x, WithCStarModule.equiv ℂᵐᵒᵖ H z⟫_ℂ
      exact inner_add_right _ _ _
    inner_self_nonneg := by
      intro x
      change (0 : ℂ) ≤
        ⟪WithCStarModule.equiv ℂᵐᵒᵖ H x, WithCStarModule.equiv ℂᵐᵒᵖ H x⟫_ℂ
      rw [← inner_self_ofReal_re, RCLike.ofReal_nonneg]
      exact inner_self_nonneg
    inner_self := by
      intro x
      constructor
      · intro hx
        apply (WithCStarModule.equiv ℂᵐᵒᵖ H).injective
        rw [WithCStarModule.equiv_zero]
        apply (inner_self_eq_zero (𝕜 := ℂ)).mp
        have h := congrArg MulOpposite.unop hx
        change MulOpposite.unop
            (MulOpposite.op
              ⟪WithCStarModule.equiv ℂᵐᵒᵖ H x,
                WithCStarModule.equiv ℂᵐᵒᵖ H x⟫_ℂ) = 0 at h
        simpa only [MulOpposite.unop_op] using h
      · rintro rfl
        simp
    inner_op_smul_right := by
      intro a x y
      apply MulOpposite.unop_injective
      change
        ⟪WithCStarModule.equiv ℂᵐᵒᵖ H x,
          MulOpposite.unop a • WithCStarModule.equiv ℂᵐᵒᵖ H y⟫_ℂ =
        ⟪WithCStarModule.equiv ℂᵐᵒᵖ H x, WithCStarModule.equiv ℂᵐᵒᵖ H y⟫_ℂ *
          MulOpposite.unop a
      rw [inner_smul_right, mul_comm]
    inner_smul_right_complex := by
      intro c x y
      apply MulOpposite.unop_injective
      change
        ⟪WithCStarModule.equiv ℂᵐᵒᵖ H x,
          c • WithCStarModule.equiv ℂᵐᵒᵖ H y⟫_ℂ =
        c •
          ⟪WithCStarModule.equiv ℂᵐᵒᵖ H x, WithCStarModule.equiv ℂᵐᵒᵖ H y⟫_ℂ
      exact inner_smul_right_eq_smul _ _ _
    star_inner := by
      intro x y
      apply MulOpposite.unop_injective
      change
        star
          ⟪WithCStarModule.equiv ℂᵐᵒᵖ H x, WithCStarModule.equiv ℂᵐᵒᵖ H y⟫_ℂ =
        ⟪WithCStarModule.equiv ℂᵐᵒᵖ H y, WithCStarModule.equiv ℂᵐᵒᵖ H x⟫_ℂ
      simp
    norm_eq_sqrt_norm_inner_self := by
      intro x
      change ‖WithCStarModule.equiv ℂᵐᵒᵖ H x‖ =
        √‖MulOpposite.op
          ⟪WithCStarModule.equiv ℂᵐᵒᵖ H x,
            WithCStarModule.equiv ℂᵐᵒᵖ H x⟫_ℂ‖
      rw [MulOpposite.norm_op]
      simpa only [← inner_self_re_eq_norm] using
        norm_eq_sqrt_re_inner (WithCStarModule.equiv ℂᵐᵒᵖ H x)
  }

/-- **Inner product of the scalar C-star module.** `(cStarModule H).toInner = instInner H`, so its
opposite-valued inner product is `MulOpposite.op ⟪q x, q y⟫_ℂ`. -/
theorem cStarModule_toInner
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let : Module ℂ (ScalarRight H) := instComplexModule H
    let : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    (cStarModule H).toInner = instInner H := by
  let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := instComplexModule H
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  rfl

/-- **Right inner-product formula.** For the C-star module structure above,
`CStarModule.rightInner (B := ℂ) x y = ⟪equivL H x, equivL H y⟫_ℂ`. -/
@[simp]
theorem rightInner_apply
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : ScalarRight H) :
    let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let : Module ℂ (ScalarRight H) := instComplexModule H
    let : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    CStarModule.rightInner (B := ℂ) x y = ⟪equivL H x, equivL H y⟫_ℂ := by
  let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := instComplexModule H
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  rfl

/-- **Completeness of the right scalar module.** With the transported norm and uniformity,
`CompleteSpace (ScalarRight H) ↔ CompleteSpace H`. -/
theorem completeSpace_iff
    (H : Type u) [NormedAddCommGroup H] :
    let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    CompleteSpace (ScalarRight H) ↔ CompleteSpace H := by
  let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff

end ScalarRight
