/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
Square-complement proof adapted from the existing @toskua, Avocado proof in
Module/InternalTensorProduct/MapLeft/Bounded.lean.
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Coefficient-valued bounds for rectangular adjointable operators

A square complement is constructed in the actual complete source End algebra.
The resulting coefficient-valued Gram remainder is nonnegative in the caller's
unchanged opposite coefficient order. Target completeness is not needed.

No scalar direct-sum norm, new order instance or desired positivity/adjoint
field is assumed.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra RightActions

namespace CStarModule.AdjointableOperator

universe uB uE uF

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- An actual rectangular operator has a source square complement, constructed
by positive CFC in the complete source End algebra. -/
theorem exists_norm_square_complement (T : AdjointableOperator B E F) :
    ∃ S : End B E, ∀ x : E,
      T.adjoint (T x) + S.adjoint (S x) = (‖T‖ ^ 2 : ℝ) • x := by
  let : PartialOrder (End B E) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (End B E) := CStarAlgebra.spectralOrderedRing _
  let K : End B E := T.adjointOperator.comp T
  let r : ℝ := ‖T‖ ^ 2
  have hK : IsSelfAdjoint K := by
    change K.adjointOperator = K
    dsimp only [K]
    rw [AdjointableOperator.comp_adjointOperator,
      AdjointableOperator.adjointOperator_adjointOperator]
  have hKnorm : ‖K‖ = r := by
    simpa only [K, r, pow_two] using AdjointableOperator.norm_adjoint_comp_self T
  have hKle : K ≤ algebraMap ℝ (End B E) r := by
    simpa only [hKnorm] using IsSelfAdjoint.le_algebraMap_norm_self K hK
  let d : End B E := algebraMap ℝ (End B E) r - K
  have hd : 0 ≤ d := sub_nonneg.mpr hKle
  let S : End B E := CFC.sqrt d
  have hs : star S * S = d := by
    dsimp only [S]
    rw [(CFC.sqrt_nonneg d).star_eq]
    exact CFC.sqrt_mul_sqrt_self d hd
  have hSquare : K + star S * S = algebraMap ℝ (End B E) r := by
    rw [add_comm K _, hs]
    exact sub_add_cancel _ _
  refine ⟨S, ?_⟩
  intro x
  have h := congrArg (fun Q : End B E => Q x) hSquare
  simpa only [K, r, AdjointableOperator.add_apply,
    AdjointableOperator.comp_apply, AdjointableOperator.adjointOperator_apply,
    AdjointableOperator.mul_apply, AdjointableOperator.star_apply,
    IsScalarTower.algebraMap_apply ℝ ℂ (End B E),
    AdjointableOperator.algebraMap_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ)] using h

/-- The genuine coefficient-valued Gram bound. Only the source module needs
completeness; the rectangular target may be incomplete. -/
theorem inner_apply_self_le_norm_sq_smul
    (T : AdjointableOperator B E F) (x : E) :
    inner Bᵐᵒᵖ (T x) (T x) ≤ (‖T‖ ^ 2 : ℝ) • inner Bᵐᵒᵖ x x := by
  obtain ⟨S, hS⟩ := exists_norm_square_complement T
  have hT : inner Bᵐᵒᵖ (T x) (T x) =
      inner Bᵐᵒᵖ x (T.adjoint (T x)) :=
    MulOpposite.unop_injective (T.adjoint_inner x (T x))
  have hSadj : inner Bᵐᵒᵖ (S x) (S x) =
      inner Bᵐᵒᵖ x (S.adjoint (S x)) :=
    MulOpposite.unop_injective (S.adjoint_inner x (S x))
  have hInner :
      inner Bᵐᵒᵖ (T x) (T x) + inner Bᵐᵒᵖ (S x) (S x) =
        (‖T‖ ^ 2 : ℝ) • inner Bᵐᵒᵖ x x := by
    calc
      _ = inner Bᵐᵒᵖ x (T.adjoint (T x) + S.adjoint (S x)) := by
        rw [CStarModule.inner_add_right, ← hT, ← hSadj]
      _ = inner Bᵐᵒᵖ x ((‖T‖ ^ 2 : ℝ) • x) := by rw [hS x]
      _ = inner Bᵐᵒᵖ x (((‖T‖ ^ 2 : ℝ) : ℂ) • x) :=
        congrArg (fun y : E => inner Bᵐᵒᵖ x y)
          (RCLike.real_smul_eq_coe_smul (K := ℂ) (‖T‖ ^ 2) x)
      _ = ((‖T‖ ^ 2 : ℝ) : ℂ) • inner Bᵐᵒᵖ x x :=
        CStarModule.inner_smul_right_complex (A := Bᵐᵒᵖ) (E := E)
          (z := ((‖T‖ ^ 2 : ℝ) : ℂ)) (x := x) (y := x)
      _ = (‖T‖ ^ 2 : ℝ) • inner Bᵐᵒᵖ x x :=
        (RCLike.real_smul_eq_coe_smul (K := ℂ) (‖T‖ ^ 2)
          (inner Bᵐᵒᵖ x x)).symm
  exact (le_add_of_nonneg_right
    (CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ) (E := E) (x := S x))).trans_eq hInner

end CStarModule.AdjointableOperator
