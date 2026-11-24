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
# An explicit canonical right scalar model

The carrier is exactly `WithCStarModule ℂᵐᵒᵖ H`. The functions in this module supply its
canonical scalar, norm and inner-product dictionaries; no target-specific global instance is
registered. This prevents the generic synonym's inherited opposite action or its product/Pi
C-star-module constructions from silently selecting a different dictionary.

The original norm, uniformity and bornology are transported through the existing equivalence.
Every public characteristic uses the chosen factory data explicitly or pins them by local
instance bindings in its result type. No opposite action is installed on `H`.

The core requires only a complex inner-product space, not completeness. Lance Chapter 1,
Blackadar §13.1 and Connes II.Appendix A use conjugate-linear first/linear second conventions.
The standard `ComplexOrder` scope supplies the coefficient order; it is not installed globally.
-/

public section

open scoped ComplexOrder InnerProductSpace RightActions

universe u

/-- The existing coefficient-indexed carrier; this introduces no new synonym mechanism. -/
abbrev ScalarRight (H : Type u) : Type u :=
  WithCStarModule ℂᵐᵒᵖ H

namespace ScalarRight

/-- The ordinary complex module is copied exactly as in the synonym's inherited instance. -/
@[expose, instance_reducible]
def instComplexModule (H : Type u) [AddCommGroup H] [Module ℂ H] :
    Module ℂ (ScalarRight H) :=
  inferInstanceAs (Module ℂ H)

/-- The chosen opposite scalar action, independent of any opposite action already on `H`. -/
@[expose, instance_reducible]
def instOppositeSMul (H : Type u) [AddCommGroup H] [Module ℂ H] :
    SMul ℂᵐᵒᵖ (ScalarRight H) where
  smul a x :=
    (WithCStarModule.equiv ℂᵐᵒᵖ H).symm
      (MulOpposite.unop a • WithCStarModule.equiv ℂᵐᵒᵖ H x)

/-- The chosen opposite module, pulled back from the fixed ordinary complex module. -/
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

/-- These two factories choose exactly the same opposite scalar data. -/
theorem oppositeModule_toSMul
    (H : Type u) [AddCommGroup H] [Module ℂ H] :
    (instOppositeModule H).toSMul = instOppositeSMul H :=
  rfl

/-- The fixed original norm and metric, with the inherited comap uniformity and bornology. -/
@[expose, instance_reducible]
def instNormedAddCommGroup (H : Type u) [NormedAddCommGroup H] :
    NormedAddCommGroup (ScalarRight H) :=
  NormedAddCommGroup.induced (ScalarRight H) H
    (WithCStarModule.addEquiv ℂᵐᵒᵖ H)
    (WithCStarModule.equiv ℂᵐᵒᵖ H).injective

/-- The factory's uniformity is exactly the synonym's inherited uniformity. -/
theorem normedAddCommGroup_uniformSpace
    (H : Type u) [NormedAddCommGroup H] :
    (instNormedAddCommGroup H).toUniformSpace =
      (inferInstance : UniformSpace H).comap (WithCStarModule.equiv ℂᵐᵒᵖ H) :=
  rfl

/-- The factory's bornology is exactly the synonym's inherited bornology. -/
theorem normedAddCommGroup_bornology
    (H : Type u) [NormedAddCommGroup H] :
    (instNormedAddCommGroup H).toBornology =
      Bornology.induced (WithCStarModule.equiv ℂᵐᵒᵖ H) :=
  rfl

/-- The normed space uses the chosen norm and the chosen ordinary complex module. -/
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

/-- The complex module in the normed-space factory is the chosen complex module. -/
theorem normedSpace_toModule
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H] :
    let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    (instNormedSpace H).toModule = instComplexModule H := by
  let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  rfl

/-- Reuse the existing continuous linear equivalence with its dictionaries fixed by `H`. -/
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

/-- The chosen norm is exactly the original norm; no ambient synonym norm is consulted. -/
@[simp]
theorem norm_apply
    (H : Type u) [NormedAddCommGroup H] (x : ScalarRight H) :
    (instNormedAddCommGroup H).toNorm.norm x =
      ‖WithCStarModule.equiv ℂᵐᵒᵖ H x‖ :=
  rfl

/-- The fixed metric makes the canonical equivalence an isometry. -/
theorem isometry_equivL
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H] :
    let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    Isometry (equivL H) := by
  let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  exact Isometry.of_dist_eq fun _ _ => rfl

/-- The chosen opposite action has the original complex scalar formula. -/
@[simp]
theorem op_smul_apply
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H]
    (c : ℂ) (x : ScalarRight H) :
    equivL H ((instOppositeSMul H).smul (MulOpposite.op c) x) =
      c • equivL H x :=
  rfl

/-- Existing right-action notation agrees once the exact opposite action is installed locally. -/
@[simp]
theorem right_smul_apply
    (H : Type u) [NormedAddCommGroup H] [NormedSpace ℂ H]
    (x : ScalarRight H) (c : ℂ) :
    let : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    equivL H (x <• c) = c • equivL H x := by
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  rfl

/-- The chosen opposite-valued inner product, not an ambient C-star-module inner product. -/
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

/-- The full canonical pre-Hilbert dictionary, with every target dictionary pinned. -/
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

/-- The C-star factory uses the exact inner factory, not a second inner dictionary. -/
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

/-- The existing right-inner product agrees under the fully pinned local factory dictionary. -/
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

/-- Completeness is inherited through the original uniformity, with the factory metric fixed. -/
theorem completeSpace_iff
    (H : Type u) [NormedAddCommGroup H] :
    let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    CompleteSpace (ScalarRight H) ↔ CompleteSpace H := by
  let : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  exact (WithCStarModule.uniformEquiv (A := ℂᵐᵒᵖ) (E := H)).completeSpace_iff

end ScalarRight
