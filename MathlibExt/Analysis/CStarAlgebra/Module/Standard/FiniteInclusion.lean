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

public import MathlibExt.Analysis.CStarAlgebra.Module.Standard.CoordinateAdjoints
public import MathlibExt.Analysis.CStarAlgebra.Module.Standard.FiniteCoordinateAdjoints

/-!
# Finite coordinate inclusions in standard right C-star modules

A genuine injection of a finite index type into an arbitrary index type gives
an adjointable inclusion of the actual finite standard module. The inclusion
is a finite sum of the existing adjointable coordinate maps, and its stored
adjoint is the corresponding coordinate restriction.

The finite-source composite is the operator identity; the reverse composite
is the existing standard truncation on the finite image. The coefficient inner
product and original norms are preserved. Operator bounds are at most one,
including empty indices and zero coefficients. No coefficient unit, new norm,
module model or compactness of the inclusion is assumed.
-/

@[expose] public section

namespace CStarModule.Right.Standard

open CStarModule.AdjointableOperator
open scoped BigOperators

universe uB uI uK

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable {I : Type uI} [Fintype I] {κ : Type uK}

/-- The finite-coordinate inclusion, formed from the actual standard and
finite coordinate adjoints. -/
noncomputable def finiteInclusion (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    AdjointableOperator B (FiniteStandard B I) (Standard B κ) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  classical
  exact ∑ i : I, (singleAdjointable (B := B) (η i)).comp
    (finiteSingleAdjointable (B := B) (I := I) i).adjointOperator

/-- The forward bounded map is the finite sum of the original single and
finite evaluation composites. -/
theorem finiteInclusion_toContinuousLinearMap (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (finiteInclusion (B := B) η).toContinuousLinearMap =
      ∑ i : I, (single (B := B) (η i)).comp
        (finiteCoord (B := B) (ι := I) i) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  classical
  let E := FiniteStandard B I
  let F := Standard B κ
  let f : I → AdjointableOperator B E F := fun i =>
    (singleAdjointable (B := B) (η i)).comp
      (finiteSingleAdjointable (B := B) (I := I) i).adjointOperator
  change (∑ i : I, f i).toContinuousLinearMap = _
  calc
    (∑ i : I, f i).toContinuousLinearMap =
        ∑ i : I, (f i).toContinuousLinearMap :=
      map_sum (forwardAddHom (B := B) (E := E) (F := F)) f Finset.univ
    _ = ∑ i : I, (single (B := B) (η i)).comp
        (finiteCoord (B := B) (ι := I) i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hSingle := singleAdjointable_toContinuousLinearMap (B := B) (η i)
      have hCoord :
          (finiteSingleAdjointable (B := B) (I := I) i).adjoint =
            finiteCoord (B := B) (ι := I) i :=
        finiteSingleAdjointable_adjoint (B := B) (I := I) i
      change (singleAdjointable (B := B) (η i)).toContinuousLinearMap.comp
        (finiteSingleAdjointable (B := B) (I := I) i).adjoint = _
      rw [hSingle, hCoord]

/-- The stored adjoint is the finite sum of the original finite insertion
and standard evaluation composites, in reverse composition order. -/
theorem finiteInclusion_adjoint (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (finiteInclusion (B := B) η).adjoint =
      ∑ i : I, (finiteSingle (B := B) (ι := I) i).comp
        (coord (B := B) (η i)) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  classical
  let E := FiniteStandard B I
  let F := Standard B κ
  let f : I → AdjointableOperator B E F := fun i =>
    (singleAdjointable (B := B) (η i)).comp
      (finiteSingleAdjointable (B := B) (I := I) i).adjointOperator
  let adjProj : AdjointableOperator B E F →+ (F →L[ℂ] E) :=
    { toFun := fun T => T.adjoint
      map_zero' := zero_adjoint (B := B) (E := E) (F := F)
      map_add' := fun T U => add_adjoint T U }
  change (∑ i : I, f i).adjoint = _
  calc
    (∑ i : I, f i).adjoint = ∑ i : I, (f i).adjoint :=
      map_sum adjProj f Finset.univ
    _ = ∑ i : I, (finiteSingle (B := B) (ι := I) i).comp
        (coord (B := B) (η i)) := by
      apply Finset.sum_congr rfl
      intro i _
      change ((singleAdjointable (B := B) (η i)).comp
        (finiteSingleAdjointable (B := B) (I := I) i).adjointOperator).adjoint = _
      rw [comp_adjoint, adjointOperator_adjoint,
        finiteSingleAdjointable_toContinuousLinearMap, singleAdjointable_adjoint]

/-- The inclusion has the literal finite sum of standard coefficient singles
as its value. -/
theorem finiteInclusion_apply (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ∀ x : FiniteStandard B I,
      finiteInclusion (B := B) η x = ∑ i : I, single (η i) (x i) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  intro x
  have h := congrArg (fun L : FiniteStandard B I →L[ℂ] Standard B κ => L x)
    (finiteInclusion_toContinuousLinearMap (B := B) η)
  have hApply : (finiteInclusion (B := B) η).toContinuousLinearMap x =
      finiteInclusion (B := B) η x :=
    congrFun (AdjointableOperator.coe_toContinuousLinearMap
      (finiteInclusion (B := B) η)) x
  calc
    finiteInclusion (B := B) η x =
        (finiteInclusion (B := B) η).toContinuousLinearMap x := hApply.symm
    _ = ∑ i : I, single (η i) (x i) := by
      simpa only [_root_.sum_apply, ContinuousLinearMap.comp_apply,
        finiteCoord_apply] using h

/-- The actual stored adjoint reads exactly the coordinates selected by the
injection. -/
@[simp]
theorem finiteInclusion_adjoint_apply (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ∀ (y : Standard B κ) (i : I),
      (finiteInclusion (B := B) η).adjoint y i = coord (η i) y := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  classical
  intro y i
  have hValue : (finiteInclusion (B := B) η).adjoint y =
      ∑ j : I, finiteSingle (B := B) (ι := I) j (coord (η j) y) := by
    have h := congrArg (fun L : Standard B κ →L[ℂ] FiniteStandard B I => L y)
      (finiteInclusion_adjoint (B := B) η)
    simpa only [_root_.sum_apply, ContinuousLinearMap.comp_apply] using h
  have hCoord : finiteCoord (B := B) (ι := I) i
      ((finiteInclusion (B := B) η).adjoint y) = coord (η i) y := by
    rw [hValue, map_sum]
    calc
      (∑ j : I, finiteCoord (B := B) (ι := I) i
          (finiteSingle (B := B) (ι := I) j (coord (η j) y))) =
          finiteCoord (B := B) (ι := I) i
            (finiteSingle (B := B) (ι := I) i (coord (η i) y)) :=
        Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hji =>
          finiteCoord_single_ne (B := B) (ι := I) (Ne.symm hji) (coord (η j) y)
      _ = coord (η i) y := finiteCoord_single_self (B := B) i (coord (η i) y)
  simpa only [finiteCoord_apply] using hCoord

/-- The image coordinate of an included vector is its original coefficient. -/
@[simp]
theorem coord_finiteInclusion (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ∀ (x : FiniteStandard B I) (i : I),
      coord (η i) (finiteInclusion (B := B) η x) = x i := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  classical
  intro x i
  rw [finiteInclusion_apply, map_sum]
  calc
    (∑ j : I, coord (η i) (single (η j) (x j))) =
        coord (η i) (single (η i) (x i)) :=
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hji => by
        have hη : η i ≠ η j := fun h => hji (η.injective h).symm
        exact coord_single_ne hη (x j)
    _ = x i := coord_single_self (η i) (x i)

/-- Restriction after inclusion is the whole identity operator on the finite
source, without a coefficient-unit hypothesis. -/
@[simp]
theorem finiteInclusion_adjoint_comp_self (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (finiteInclusion (B := B) η).adjointOperator.comp (finiteInclusion (B := B) η) =
      (1 : AdjointableOperator.End B (FiniteStandard B I)) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  apply AdjointableOperator.ext
  intro x
  change (finiteInclusion (B := B) η).adjoint (finiteInclusion (B := B) η x) = x
  apply (WithCStarModule.equiv Bᵐᵒᵖ (I → B)).injective
  funext i
  change (finiteInclusion (B := B) η).adjoint (finiteInclusion (B := B) η x) i = x i
  rw [finiteInclusion_adjoint_apply, coord_finiteInclusion]

/-- The reverse whole composite has the original standard truncation as its
forward CLM, on the literal finite image of the injection. -/
theorem finiteInclusion_comp_adjoint_toContinuousLinearMap (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ((finiteInclusion (B := B) η).comp
      (finiteInclusion (B := B) η).adjointOperator).toContinuousLinearMap =
      truncate (B := B) (Finset.univ.map η) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  classical
  apply ContinuousLinearMap.ext
  intro y
  change finiteInclusion (B := B) η ((finiteInclusion (B := B) η).adjoint y) =
    truncate (B := B) (Finset.univ.map η) y
  rw [finiteInclusion_apply, truncate_eq_sum_single, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (single (B := B) (η i))
    (finiteInclusion_adjoint_apply (B := B) η y i)

/-- The inclusion preserves the coefficient-valued right inner product. -/
theorem rightInner_finiteInclusion (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ∀ x y : FiniteStandard B I,
      CStarModule.rightInner (B := B)
          (finiteInclusion (B := B) η x) (finiteInclusion (B := B) η y) =
        CStarModule.rightInner (B := B) x y := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  intro x y
  have h := congrArg
    (fun T : AdjointableOperator.End B (FiniteStandard B I) => T y)
    (finiteInclusion_adjoint_comp_self (B := B) η)
  have hRound : (finiteInclusion (B := B) η).adjoint
      (finiteInclusion (B := B) η y) = y := by
    simpa only [AdjointableOperator.comp_apply,
      AdjointableOperator.adjointOperator_apply, AdjointableOperator.one_apply] using h
  calc
    CStarModule.rightInner (B := B)
        (finiteInclusion (B := B) η x) (finiteInclusion (B := B) η y) =
        CStarModule.rightInner (B := B) x
          ((finiteInclusion (B := B) η).adjoint (finiteInclusion (B := B) η y)) :=
      (finiteInclusion (B := B) η).adjoint_inner x (finiteInclusion (B := B) η y)
    _ = CStarModule.rightInner (B := B) x y :=
      congrArg (CStarModule.rightInner (B := B) x) hRound

/-- The original finite and standard module norms agree on the inclusion. -/
@[simp]
theorem norm_finiteInclusion_apply (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ∀ x : FiniteStandard B I, ‖finiteInclusion (B := B) η x‖ = ‖x‖ := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  intro x
  exact CStarModule.norm_map_of_map_rightInner
    (B := B) (C := B) (E := FiniteStandard B I) (F := Standard B κ)
    (fun b : B => b) (fun z : FiniteStandard B I => finiteInclusion (B := B) η z)
    (fun _ => rfl) (rightInner_finiteInclusion (B := B) η) x

/-- The finite inclusion is an isometry for the original metrics. -/
theorem finiteInclusion_isometry (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    Isometry (finiteInclusion (B := B) η) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  refine isometry_iff_dist_eq.mpr ?_
  intro x y
  rw [dist_eq_norm, dist_eq_norm,
    ← map_sub (finiteInclusion (B := B) η) x y]
  exact norm_finiteInclusion_apply (B := B) η (x - y)

/-- The inclusion has norm at most one, also for an empty source or zero
coefficient algebra. -/
theorem norm_finiteInclusion_le (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ‖finiteInclusion (B := B) η‖ ≤ 1 := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rw [AdjointableOperator.norm_eq]
  refine (finiteInclusion (B := B) η).toContinuousLinearMap.opNorm_le_bound
    zero_le_one ?_
  intro x
  have hApply : (finiteInclusion (B := B) η).toContinuousLinearMap x =
      finiteInclusion (B := B) η x :=
    congrFun (AdjointableOperator.coe_toContinuousLinearMap
      (finiteInclusion (B := B) η)) x
  calc
    ‖(finiteInclusion (B := B) η).toContinuousLinearMap x‖ =
        ‖finiteInclusion (B := B) η x‖ :=
      congrArg (fun z : Standard B κ => ‖z‖) hApply
    _ = ‖x‖ := norm_finiteInclusion_apply (B := B) η x
    _ ≤ 1 * ‖x‖ := by simp only [one_mul, le_refl]

/-- The actual adjoint operator has the same zero-safe bound. -/
theorem norm_finiteInclusion_adjointOperator_le (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ‖(finiteInclusion (B := B) η).adjointOperator‖ ≤ 1 := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rw [AdjointableOperator.norm_adjointOperator]
  exact norm_finiteInclusion_le (B := B) η

end CStarModule.Right.Standard

end
