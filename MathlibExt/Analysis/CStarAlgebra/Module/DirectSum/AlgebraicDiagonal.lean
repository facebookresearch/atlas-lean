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

public import MathlibExt.Analysis.CStarAlgebra.Module.DirectSum.Algebraic
public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable

/-!
# Diagonals on finite-support module sums

For right pre-Hilbert `B`-modules `E_i,F_i` and adjointable maps `T_i : E_i → F_i`, define the
complex-linear diagonal by `(D_T x)_i = T_i x_i` on finite-support vectors. Its support is
contained in the support of `x`.

The diagonal of the adjoints satisfies the finite coefficient pairing `⟨D_T x,y⟩_B = ⟨x,D_(T*)
y⟩_B`. This algebraic construction requires no uniform norm bound and permits incomplete fibers
and arbitrary index types.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarModule.DirectSum

universe uB uI uE uF

variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable {I : Type uI} {E : I → Type uE} {F : I → Type uF}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, SMul Bᵐᵒᵖ (E i)] [∀ i, CStarModule Bᵐᵒᵖ (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
  [∀ i, SMul Bᵐᵒᵖ (F i)] [∀ i, CStarModule Bᵐᵒᵖ (F i)]

/-- **Algebraic diagonal of adjointable components.** For a family `T_i : E_i → F_i`, the
complex-linear map on finite-support sums is determined by `(algebraicDiagonal T x)_i = T_i
x_i`. -/
@[expose]
def algebraicDiagonal (T : ∀ i, AdjointableOperator B (E i) (F i)) :
    Algebraic B E →ₗ[ℂ] Algebraic B F :=
  (toDFinsupp (B := B) (E := F)).symm.toLinearMap.comp
    ((DFinsupp.mapRange.linearMap fun i ↦
        (T i).toContinuousLinearMap.toLinearMap).comp
      (toDFinsupp (B := B) (E := E)).toLinearMap)

private theorem algebraicDiagonal_raw
    (T : ∀ i, AdjointableOperator B (E i) (F i)) (x : Algebraic B E) :
    toDFinsupp (algebraicDiagonal T x) =
      DFinsupp.mapRange.linearMap
        (fun i ↦ (T i).toContinuousLinearMap.toLinearMap) (toDFinsupp x) := by
  let e := toDFinsupp (B := B) (E := F)
  let z : Π₀ i, F i := DFinsupp.mapRange.linearMap
    (fun i ↦ (T i).toContinuousLinearMap.toLinearMap) (toDFinsupp x)
  change e (e.symm z) = z
  exact e.apply_symm_apply z

/-- **Coordinate value of an algebraic diagonal.** `toDFinsupp (algebraicDiagonal T x) i = T i
(toDFinsupp x i)`. -/
theorem algebraicDiagonal_apply
    (T : ∀ i, AdjointableOperator B (E i) (F i)) (x : Algebraic B E) (i : I) :
    toDFinsupp (algebraicDiagonal T x) i = T i (toDFinsupp x i) := by
  rw [algebraicDiagonal_raw]
  rfl

/-- **Diagonal on a one-coordinate vector.** `algebraicDiagonal T (singleLinear i x) =
singleLinear i (T i x)` in the target algebraic sum. -/
theorem algebraicDiagonal_singleLinear
    (T : ∀ i, AdjointableOperator B (E i) (F i)) (i : I) (x : E i) :
    algebraicDiagonal T (singleLinear (B := B) (E := E) i x) =
      singleLinear (B := B) (E := F) i (T i x) := by
  classical
  apply (toDFinsupp (B := B) (E := F)).injective
  rw [algebraicDiagonal_raw, toDFinsupp_singleLinear, toDFinsupp_singleLinear]
  change DFinsupp.mapRange (fun j z ↦ T j z)
    (fun j ↦ (T j).toContinuousLinearMap.map_zero) (DFinsupp.single i x) =
      DFinsupp.single i (T i x)
  exact DFinsupp.mapRange_single

/-- **Support bound for an algebraic diagonal.** `support (algebraicDiagonal T x) ⊆ support x`; a
component kernel can remove a coordinate. -/
theorem support_algebraicDiagonal_subset
    (T : ∀ i, AdjointableOperator B (E i) (F i)) (x : Algebraic B E) :
    support (algebraicDiagonal T x) ⊆ support x := by
  classical
  change (toDFinsupp (algebraicDiagonal T x)).support ⊆ (toDFinsupp x).support
  rw [algebraicDiagonal_raw]
  change (DFinsupp.mapRange (fun i z ↦ T i z)
    (fun i ↦ (T i).toContinuousLinearMap.map_zero) (toDFinsupp x)).support ⊆ _
  exact DFinsupp.support_mapRange

/-- **Pairing with the adjoint diagonal.** The coefficient inner products satisfy `algebraicInner
(D_T x) y = algebraicInner x (D_(T*) y)` for the finite-support sums. -/
theorem algebraicDiagonal_adjoint_inner
    (T : ∀ i, AdjointableOperator B (E i) (F i))
    (x : Algebraic B E) (y : Algebraic B F) :
    algebraicInner (algebraicDiagonal T x) y =
      algebraicInner x (algebraicDiagonal (fun i ↦ (T i).adjointOperator) y) := by
  induction y using CStarModule.DirectSum.induction with
  | h0 =>
      rw [(algebraicDiagonal (fun i ↦ (T i).adjointOperator)).map_zero,
        algebraicInner_zero_right, algebraicInner_zero_right]
  | ha i z y _hi _hz ih =>
      have hCoefficient : inner Bᵐᵒᵖ (T i (toDFinsupp x i)) z =
          inner Bᵐᵒᵖ (toDFinsupp x i) ((T i).adjoint z) := by
        have h := (T i).adjoint_inner (toDFinsupp x i) z
        change MulOpposite.unop (inner Bᵐᵒᵖ (T i (toDFinsupp x i)) z) =
          MulOpposite.unop (inner Bᵐᵒᵖ (toDFinsupp x i) ((T i).adjoint z)) at h
        exact MulOpposite.unop_injective h
      calc
        algebraicInner (algebraicDiagonal T x)
            (singleLinear (B := B) (E := F) i z + y) =
            inner Bᵐᵒᵖ (T i (toDFinsupp x i)) z +
              algebraicInner (algebraicDiagonal T x) y := by
          rw [algebraicInner_add_right, algebraicInner_single_right,
            algebraicDiagonal_apply]
        _ = inner Bᵐᵒᵖ (toDFinsupp x i) ((T i).adjoint z) +
            algebraicInner x
              (algebraicDiagonal (fun i ↦ (T i).adjointOperator) y) := by
          rw [hCoefficient, ih]
        _ = algebraicInner x
            (singleLinear (B := B) (E := E) i ((T i).adjoint z) +
              algebraicDiagonal (fun i ↦ (T i).adjointOperator) y) := by
          rw [algebraicInner_add_right, algebraicInner_single_right]
        _ = algebraicInner x
            (algebraicDiagonal (fun i ↦ (T i).adjointOperator)
              (singleLinear (B := B) (E := F) i z + y)) := by
          rw [(algebraicDiagonal (fun i ↦ (T i).adjointOperator)).map_add,
            algebraicDiagonal_singleLinear,
            AdjointableOperator.adjointOperator_apply]

end CStarModule.DirectSum
