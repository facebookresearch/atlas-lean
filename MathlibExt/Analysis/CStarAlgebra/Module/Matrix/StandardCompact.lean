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

public import MathlibExt.Analysis.CStarAlgebra.Module.Standard.FiniteInclusion
public import MathlibExt.Analysis.CStarAlgebra.Module.Matrix.Compact
public import MathlibExt.Analysis.CStarAlgebra.Module.Matrix.Positivity
public import Mathlib.Analysis.CStarAlgebra.Hom
public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.Padding
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Actual finite matrix corners in standard-module compacts

A finite coefficient matrix acts on the standard right module through the
actual finite-coordinate inclusion and its adjoint. Compactness comes from
the middle finite matrix operator, not from compactness of the inclusion.
The finite-source identity proves multiplication and faithful extraction.

The original coefficient-inner norms and the C-star matrix operator norm
are retained. Empty finite indices and zero, possibly nonunital coefficient
algebras are included; no unit-valued coordinate vectors are used.
-/

@[expose] public section

noncomputable section

namespace CStarModule.AdjointableOperator

open CStarModule.Right
open scoped BigOperators

universe uB uI uK

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable {I : Type uI} [Fintype I] {κ : Type uK}

/-- The original finite compact matrix hom, conjugated by the actual
finite-coordinate inclusion into the standard module. -/
noncomputable def rightMatrixStandardCompactHom (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    CStarMatrix I I B →⋆ₙₐ[ℂ]
      compactStarSubalgebra (B := B) (E := Standard B κ) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  let E := FiniteStandard B I
  let F := Standard B κ
  let J : AdjointableOperator B E F := Standard.finiteInclusion (B := B) η
  let Φ : CStarMatrix I I B →⋆ₙₐ[ℂ]
      compactStarSubalgebra (B := B) (E := E) :=
    rightMatrixCompactHom (B := B) (ι := I)
  let ρ : CStarMatrix I I B →⋆ₙₐ[ℂ] End B E :=
    (NonUnitalStarSubalgebraClass.subtype
      (compactStarSubalgebra (B := B) (E := E))).comp Φ
  have hRound (x : E) : J.adjointOperator (J x) = x := by
    have h := congrArg (fun T : End B E => T x)
      (Standard.finiteInclusion_adjoint_comp_self (B := B) η)
    simpa only [comp_apply, one_apply] using h
  let cJ : End B E →⋆ₙₐ[ℂ] End B F :=
    { toFun := fun T => J.comp (T.comp J.adjointOperator)
      map_zero' := by
        apply AdjointableOperator.ext
        intro y
        change J ((0 : End B E) (J.adjointOperator y)) = 0
        rw [zero_apply, map_zero]
      map_add' := by
        intro T U
        apply AdjointableOperator.ext
        intro y
        change J ((T + U) (J.adjointOperator y)) =
          J (T (J.adjointOperator y)) + J (U (J.adjointOperator y))
        rw [add_apply, map_add]
      map_smul' := by
        intro c T
        apply AdjointableOperator.ext
        intro y
        change J ((c • T) (J.adjointOperator y)) =
          c • J (T (J.adjointOperator y))
        rw [smul_apply, map_smul]
      map_mul' := by
        intro T U
        apply AdjointableOperator.ext
        intro y
        change J ((T * U) (J.adjointOperator y)) =
          J (T (J.adjointOperator (J (U (J.adjointOperator y)))))
        simp only [mul_apply, hRound]
      map_star' := by
        intro T
        change J.comp ((star T).comp J.adjointOperator) =
          (J.comp (T.comp J.adjointOperator)).adjointOperator
        apply AdjointableOperator.ext
        intro y
        simp only [comp_adjointOperator, adjointOperator_adjointOperator,
          comp_apply, star_apply, adjointOperator_apply] }
  let θ : CStarMatrix I I B →⋆ₙₐ[ℂ] End B F := cJ.comp ρ
  have hMem (X : CStarMatrix I I B) :
      θ X ∈ compactStarSubalgebra (B := B) (E := F) := by
    have hX : ρ X ∈ compactSubmodule (B := B) (E := E) (F := E) := by
      change (Φ X : End B E) ∈ compactSubmodule (B := B) (E := E) (F := E)
      exact (mem_compactStarSubalgebra (B := B) (E := E) (Φ X)).mp
        (Φ X).property
    have hRight : (ρ X).comp J.adjointOperator ∈
        compactSubmodule (B := B) (E := F) (F := E) :=
      comp_mem_compact_left (B := B) (E := F) (F := E) (G := E)
        hX J.adjointOperator
    change J.comp ((ρ X).comp J.adjointOperator) ∈
      compactSubmodule (B := B) (E := F) (F := F)
    exact comp_mem_compact_right (B := B) (E := F) (F := E) (G := F)
      J hRight
  exact NonUnitalStarAlgHom.codRestrict θ
    (compactStarSubalgebra (B := B) (E := F)) hMem

/-- Including the corner gives the literal inclusion–matrix–adjoint
composite, with the same original finite compact matrix operator. -/
theorem rightMatrixStandardCompactHom_coe (η : I ↪ κ) (X : CStarMatrix I I B) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (rightMatrixStandardCompactHom (B := B) η X : End B (Standard B κ)) =
      (Standard.finiteInclusion (B := B) η).comp
        ((rightMatrixCompactHom (B := B) (ι := I) X :
          End B (FiniteStandard B I)).comp
            (Standard.finiteInclusion (B := B) η).adjointOperator) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rfl

/-- The whole corner action is the literal finite sum of coefficient singles
with the original row-before-column, unconjugated matrix entries. -/
theorem rightMatrixStandardCompactHom_apply (η : I ↪ κ) (X : CStarMatrix I I B) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ∀ y : Standard B κ,
      (rightMatrixStandardCompactHom (B := B) η X : End B (Standard B κ)) y =
        ∑ i : I, Standard.single (η i)
          (∑ j : I, X i j * Standard.coord (η j) y) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  intro y
  let J := Standard.finiteInclusion (B := B) η
  have hCoord (j : I) : (J.adjointOperator y) j = Standard.coord (η j) y := by
    rw [adjointOperator_apply]
    exact Standard.finiteInclusion_adjoint_apply (B := B) η y j
  rw [rightMatrixStandardCompactHom_coe, comp_apply, comp_apply,
    Standard.finiteInclusion_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (Standard.single (η i))
  calc
    (rightMatrixCompactHom (B := B) (ι := I) X : End B (FiniteStandard B I))
        (J.adjointOperator y) i = ∑ j : I, X i j * (J.adjointOperator y) j :=
      rightMatrixCompactHom_apply X (J.adjointOperator y) i
    _ = ∑ j : I, X i j * Standard.coord (η j) y := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun b : B => X i j * b) (hCoord j)

/-- Every selected coordinate of the corner is the original matrix column
action on the selected input coordinates. -/
@[simp]
theorem coord_rightMatrixStandardCompactHom_apply (η : I ↪ κ)
    (X : CStarMatrix I I B) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ∀ (y : Standard B κ) (i : I),
      Standard.coord (η i)
          ((rightMatrixStandardCompactHom (B := B) η X : End B (Standard B κ)) y) =
        ∑ j : I, X i j * Standard.coord (η j) y := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  intro y i
  let J := Standard.finiteInclusion (B := B) η
  have hCoord (j : I) : (J.adjointOperator y) j = Standard.coord (η j) y := by
    rw [adjointOperator_apply]
    exact Standard.finiteInclusion_adjoint_apply (B := B) η y j
  rw [rightMatrixStandardCompactHom_coe, comp_apply, comp_apply,
    Standard.coord_finiteInclusion, rightMatrixCompactHom_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun b : B => X i j * b) (hCoord j)

/-- The original selected coordinate block is left multiplication by Xij,
as a whole operator on supplied coefficients, without a coefficient unit. -/
theorem rightMatrixStandardCompactHom_block (η : I ↪ κ) (X : CStarMatrix I I B) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ∀ i j : I,
      (Standard.singleAdjointable (B := B) (η i)).adjointOperator.comp
          ((rightMatrixStandardCompactHom (B := B) η X : End B (Standard B κ)).comp
            (Standard.singleAdjointable (B := B) (η j))) =
        leftMul (B := B) (X i j) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  classical
  intro i j
  apply AdjointableOperator.ext
  intro b
  rw [comp_apply, comp_apply, Standard.singleAdjointable_adjoint_apply,
    Standard.singleAdjointable_apply, coord_rightMatrixStandardCompactHom_apply]
  calc
    (∑ k : I, X i k * Standard.coord (η k) (Standard.single (η j) b)) =
        X i j * Standard.coord (η j) (Standard.single (η j) b) :=
      Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun k _ hkj => by
        have hη : η k ≠ η j := fun h => hkj (η.injective h)
        rw [Standard.coord_single_ne hη, mul_zero]
    _ = X i j * b := by rw [Standard.coord_single_self]
    _ = leftMul (B := B) (X i j) b := (leftMul_apply _ _).symm

/-- The actual standard compact corner is faithful, by compression back
to the original faithful finite matrix hom. -/
theorem rightMatrixStandardCompactHom_injective (η : I ↪ κ) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    Function.Injective (rightMatrixStandardCompactHom (B := B) η) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  let E := FiniteStandard B I
  let F := Standard B κ
  let J : AdjointableOperator B E F := Standard.finiteInclusion (B := B) η
  let KF := compactStarSubalgebra (B := B) (E := F)
  let f : CStarMatrix I I B →⋆ₙₐ[ℂ] KF := rightMatrixStandardCompactHom (B := B) η
  let ψ : CStarMatrix I I B →⋆ₙₐ[ℂ] End B F :=
    (NonUnitalStarSubalgebraClass.subtype KF).comp f
  have hRound (x : E) : J.adjointOperator (J x) = x := by
    have h := congrArg (fun T : End B E => T x)
      (Standard.finiteInclusion_adjoint_comp_self (B := B) η)
    simpa only [comp_apply, one_apply] using h
  have hPull (X : CStarMatrix I I B) :
      J.adjointOperator.comp ((ψ X).comp J) =
        (rightMatrixCompactHom (B := B) (ι := I) X : End B E) := by
    have hValue : ψ X = J.comp
        ((rightMatrixCompactHom (B := B) (ι := I) X : End B E).comp
          J.adjointOperator) :=
      rightMatrixStandardCompactHom_coe (B := B) η X
    rw [hValue]
    apply AdjointableOperator.ext
    intro x
    change J.adjointOperator
        (J ((rightMatrixCompactHom (B := B) (ι := I) X : End B E)
          (J.adjointOperator (J x)))) = _
    rw [hRound, hRound]
  have hψ : Function.Injective ψ := by
    intro X Y h
    have hPullXY := congrArg
      (fun T : End B F => J.adjointOperator.comp (T.comp J)) h
    rw [hPull, hPull, rightMatrixCompactHom_coe, rightMatrixCompactHom_coe] at hPullXY
    exact rightMatrixHom_injective (B := B) (I := I) hPullXY
  have hMem (X : CStarMatrix I I B) : ψ X ∈ KF := (f X).property
  have hPin : NonUnitalStarAlgHom.codRestrict ψ KF hMem = f := by
    apply NonUnitalStarAlgHom.ext
    intro X
    apply Subtype.ext
    rfl
  change Function.Injective f
  rw [← hPin]
  exact (NonUnitalStarAlgHom.injective_codRestrict ψ KF hMem).mpr hψ

/-- The corner preserves the original C-star matrix norm and inherited
compact-operator norm, including the zero algebra and empty indices. -/
theorem norm_rightMatrixStandardCompactHom_apply (η : I ↪ κ)
    (X : CStarMatrix I I B) :
    letI : PartialOrder B := CStarAlgebra.spectralOrder B;
    letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B;
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ‖rightMatrixStandardCompactHom (B := B) η X‖ = ‖X‖ := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  let F := Standard B κ
  let KF := compactStarSubalgebra (B := B) (E := F)
  let f : CStarMatrix I I B →⋆ₙₐ[ℂ] KF := rightMatrixStandardCompactHom (B := B) η
  let ψ : CStarMatrix I I B →⋆ₙₐ[ℂ] End B F :=
    (NonUnitalStarSubalgebraClass.subtype KF).comp f
  have hψ : Function.Injective ψ := by
    intro M N h
    apply rightMatrixStandardCompactHom_injective (B := B) η
    apply Subtype.ext
    exact h
  calc
    ‖rightMatrixStandardCompactHom (B := B) η X‖ = ‖ψ X‖ := rfl
    _ = ‖X‖ := NonUnitalStarAlgHom.norm_map ψ hψ X

/-- The same computed corner is an isometry for the original metrics. -/
theorem rightMatrixStandardCompactHom_isometry (η : I ↪ κ) :
    letI : PartialOrder B := CStarAlgebra.spectralOrder B;
    letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B;
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    Isometry (rightMatrixStandardCompactHom (B := B) η) := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  let F := Standard B κ
  let KF := compactStarSubalgebra (B := B) (E := F)
  let f : CStarMatrix I I B →⋆ₙₐ[ℂ] KF := rightMatrixStandardCompactHom (B := B) η
  let ψ : CStarMatrix I I B →⋆ₙₐ[ℂ] End B F :=
    (NonUnitalStarSubalgebraClass.subtype KF).comp f
  have hψ : Function.Injective ψ := by
    intro M N h
    apply rightMatrixStandardCompactHom_injective (B := B) η
    apply Subtype.ext
    exact h
  refine isometry_iff_dist_eq.mpr ?_
  intro X Y
  calc
    dist (rightMatrixStandardCompactHom (B := B) η X)
        (rightMatrixStandardCompactHom (B := B) η Y) = dist (ψ X) (ψ Y) := rfl
    _ = dist X Y := (NonUnitalStarAlgHom.isometry ψ hψ).dist_eq X Y

/-- Literal top-left zero padding leaves the actual initial-segment compact
corner unchanged. Ordinary size zero is the empty finite stage. -/
theorem rightMatrixStandardCompactHom_zeroExtend {n m : ℕ} (h : n ≤ m)
    (X : CStarMatrix (Fin n) (Fin n) B) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    rightMatrixStandardCompactHom (B := B)
        (⟨Fin.val, Fin.val_injective⟩ : Fin m ↪ ℕ)
        (CStarMatrix.zeroExtendStarAlgHom h X) =
      rightMatrixStandardCompactHom (B := B)
        (⟨Fin.val, Fin.val_injective⟩ : Fin n ↪ ℕ) X := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  classical
  rcases Nat.exists_eq_add_of_le h with ⟨d, rfl⟩
  let ηn : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let ηm : Fin (n + d) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let Y : CStarMatrix (Fin (n + d)) (Fin (n + d)) B :=
    CStarMatrix.zeroExtendStarAlgHom h X
  have hηn (i : Fin n) : ηn i = i.val :=
    congrFun (Function.Embedding.coeFn_mk
      (Fin.val : Fin n → ℕ) Fin.val_injective) i
  have hηm (i : Fin (n + d)) : ηm i = i.val :=
    congrFun (Function.Embedding.coeFn_mk
      (Fin.val : Fin (n + d) → ℕ) Fin.val_injective) i
  have hRetained (i j : Fin n) : Y (i.castAdd d) (j.castAdd d) = X i j := by
    have hentry := CStarMatrix.zeroExtendStarAlgHom_apply_entry (A := B) h X
      (i.castAdd d) (j.castAdd d)
    calc
      Y (i.castAdd d) (j.castAdd d) =
          CStarMatrix.zeroExtendStarAlgHom h X (i.castAdd d) (j.castAdd d) := rfl
      _ = X i j := by
        simpa only [Fin.val_castAdd, i.isLt, j.isLt, ↓reduceDIte] using hentry
  have hNewRow (i : Fin d) (j : Fin (n + d)) : Y (Fin.natAdd n i) j = 0 := by
    have hge : n ≤ (Fin.natAdd n i).val := by
      rw [Fin.val_natAdd]
      exact Nat.le_add_right n i.val
    have hentry := CStarMatrix.zeroExtendStarAlgHom_apply_entry (A := B) h X
      (Fin.natAdd n i) j
    calc
      Y (Fin.natAdd n i) j =
          CStarMatrix.zeroExtendStarAlgHom h X (Fin.natAdd n i) j := rfl
      _ = 0 := hentry.trans (dite_eq_right (not_lt_of_ge hge))
  have hNewColumn (i : Fin n) (j : Fin d) :
      Y (i.castAdd d) (Fin.natAdd n j) = 0 := by
    have hge : n ≤ (Fin.natAdd n j).val := by
      rw [Fin.val_natAdd]
      exact Nat.le_add_right n j.val
    have hnot : ¬ (Fin.natAdd n j).val < n := not_lt_of_ge hge
    have hentry := CStarMatrix.zeroExtendStarAlgHom_apply_entry (A := B) h X
      (i.castAdd d) (Fin.natAdd n j)
    calc
      Y (i.castAdd d) (Fin.natAdd n j) =
          CStarMatrix.zeroExtendStarAlgHom h X (i.castAdd d) (Fin.natAdd n j) := rfl
      _ = 0 := by
        simpa only [Fin.val_castAdd, i.isLt, hnot, ↓reduceDIte] using hentry
  apply Subtype.ext
  apply AdjointableOperator.ext
  intro y
  change (rightMatrixStandardCompactHom (B := B) ηm Y :
      End B (Standard B ℕ)) y =
    (rightMatrixStandardCompactHom (B := B) ηn X : End B (Standard B ℕ)) y
  rw [rightMatrixStandardCompactHom_apply, rightMatrixStandardCompactHom_apply]
  have hColumns (i : Fin n) :
      (∑ j : Fin (n + d), Y (i.castAdd d) j * Standard.coord (ηm j) y) =
        ∑ j : Fin n, X i j * Standard.coord (ηn j) y := by
    calc
      (∑ j : Fin (n + d), Y (i.castAdd d) j * Standard.coord (ηm j) y) =
          ∑ j : Fin n, Y (i.castAdd d) (j.castAdd d) *
            Standard.coord (ηm (j.castAdd d)) y :=
        Fin.sum_trunc
          (fun j : Fin (n + d) => Y (i.castAdd d) j * Standard.coord (ηm j) y)
          (fun j : Fin d => by rw [hNewColumn, zero_mul])
      _ = ∑ j : Fin n, X i j * Standard.coord (ηn j) y := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [hRetained, hηm, hηn, Fin.val_castAdd]
  calc
    (∑ i : Fin (n + d), Standard.single (ηm i)
        (∑ j : Fin (n + d), Y i j * Standard.coord (ηm j) y)) =
        ∑ i : Fin n, Standard.single (ηm (i.castAdd d))
          (∑ j : Fin (n + d), Y (i.castAdd d) j * Standard.coord (ηm j) y) :=
      Fin.sum_trunc
        (fun i : Fin (n + d) => Standard.single (ηm i)
          (∑ j : Fin (n + d), Y i j * Standard.coord (ηm j) y))
        (fun i : Fin d => by
          have hZero :
              (∑ j : Fin (n + d), Y (Fin.natAdd n i) j *
                Standard.coord (ηm j) y) = 0 :=
            Finset.sum_eq_zero fun j _ => by rw [hNewRow, zero_mul]
          rw [hZero, map_zero])
    _ = ∑ i : Fin n, Standard.single (ηn i)
        (∑ j : Fin n, X i j * Standard.coord (ηn j) y) := by
      apply Finset.sum_congr rfl
      intro i _
      have hIndex : ηm (i.castAdd d) = ηn i := by
        calc
          ηm (i.castAdd d) = (i.castAdd d).val := hηm (i.castAdd d)
          _ = i.val := by rw [Fin.val_castAdd]
          _ = ηn i := (hηn i).symm
      calc
        Standard.single (ηm (i.castAdd d))
            (∑ j : Fin (n + d), Y (i.castAdd d) j * Standard.coord (ηm j) y) =
            Standard.single (ηm (i.castAdd d))
              (∑ j : Fin n, X i j * Standard.coord (ηn j) y) :=
          congrArg (Standard.single (ηm (i.castAdd d))) (hColumns i)
        _ = Standard.single (ηn i)
            (∑ j : Fin n, X i j * Standard.coord (ηn j) y) :=
          congrArg (fun k : ℕ => Standard.single k
            (∑ j : Fin n, X i j * Standard.coord (ηn j) y)) hIndex

end CStarModule.AdjointableOperator

end
