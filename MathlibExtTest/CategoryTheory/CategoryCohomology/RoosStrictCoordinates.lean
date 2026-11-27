/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryCohomology.RoosStrictCoordinates

/-!
# Strict Roos coordinate clients

These clients retain coefficient transport through normalized poset
coordinates and check the repeated-vertex boundary of strict-chain indexing.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology
open CategoryTheory.CategoryCohomology

universe u₁ u₂ v₂

variable {P : Type u₁} [PartialOrder P]
  {A : Type u₂} [Category.{v₂} A] [Abelian A] [HasProducts.{u₁} A]

/-- Actual normalized cochain maps act on strict factors by the terminal coefficient map. -/
example {M N : P ⥤ A} (α : M ⟶ N) (n : ℕ)
    (F : {F : ComposableArrows Pᵒᵖ n // StrictAnti (fun i ↦ (F.obj i).unop)}) :
    ((normalizedRoosComplexFunctor (I := P) (A := A)).map α).f n ≫
        (normalizedRoosStrictProductIso N n).hom ≫
        Pi.π (fun F : {F : ComposableArrows Pᵒᵖ n //
          StrictAnti (fun i ↦ (F.obj i).unop)} ↦ N.obj F.val.left.unop) F =
      (normalizedRoosStrictProductIso M n).hom ≫
        Pi.π (fun F : {F : ComposableArrows Pᵒᵖ n //
          StrictAnti (fun i ↦ (F.obj i).unop)} ↦ M.obj F.val.left.unop) F ≫
        α.app F.val.left.unop := by
  let f : normalizedRoosDegree M n ⟶ normalizedRoosDegree N n :=
    ((normalizedRoosComplexFunctor (I := P) (A := A)).map α).f n
  let r : fullRoosDegree M n ⟶ fullRoosDegree N n :=
    (roosMap α).app (SimplexCategory.mk n)
  let I_M : normalizedRoosDegree M n ⟶ fullRoosDegree M n := roosInclusionAt M n
  let I_N : normalizedRoosDegree N n ⟶ fullRoosDegree N n := roosInclusionAt N n
  let U_M : normalizedRoosDegree M n ⟶ ∏ᶜ (strictRoosFamily M n) :=
    (normalizedRoosStrictProductIso M n).hom
  let U_N : normalizedRoosDegree N n ⟶ ∏ᶜ (strictRoosFamily N n) :=
    (normalizedRoosStrictProductIso N n).hom
  let p_M : (∏ᶜ (strictRoosFamily M n)) ⟶ M.obj F.val.left.unop :=
    Pi.π (strictRoosFamily M n) F
  let p_N : (∏ᶜ (strictRoosFamily N n)) ⟶ N.obj F.val.left.unop :=
    Pi.π (strictRoosFamily N n) F
  let π_M : fullRoosDegree M n ⟶ M.obj F.val.left.unop := roosChainProjection M F.val
  let π_N : fullRoosDegree N n ⟶ N.obj F.val.left.unop := roosChainProjection N F.val
  let c : M.obj F.val.left.unop ⟶ N.obj F.val.left.unop := α.app F.val.left.unop
  have hComp : f ≫ I_N = I_M ≫ r :=
    congrArg (fun φ :
      (normalizedRoosComplexFunctor (I := P) (A := A)).obj M ⟶
        (roosComplexFunctor (I := P) (A := A)).obj N => φ.f n)
      ((inclusionOfNormalizedRoosComplex (I := P) (A := A)).naturality α)
  have hR : r ≫ π_N = π_M ≫ c := roosMap_app_π α F.val
  have hU_M : U_M ≫ p_M = I_M ≫ π_M := normalizedRoosStrictProductIso_hom_π M n F
  have hU_N : U_N ≫ p_N = I_N ≫ π_N := normalizedRoosStrictProductIso_hom_π N n F
  change f ≫ U_N ≫ p_N = U_M ≫ p_M ≫ c
  calc
    f ≫ U_N ≫ p_N = f ≫ (I_N ≫ π_N) := congrArg (fun k => f ≫ k) hU_N
    _ = (f ≫ I_N) ≫ π_N := (Category.assoc f I_N π_N).symm
    _ = (I_M ≫ r) ≫ π_N := congrArg (fun k => k ≫ π_N) hComp
    _ = I_M ≫ (r ≫ π_N) := Category.assoc I_M r π_N
    _ = I_M ≫ (π_M ≫ c) := congrArg (fun k => I_M ≫ k) hR
    _ = (I_M ≫ π_M) ≫ c := (Category.assoc I_M π_M c).symm
    _ = (U_M ≫ p_M) ≫ c := congrArg (fun k => k ≫ c) hU_M.symm
    _ = U_M ≫ p_M ≫ c := Category.assoc U_M p_M c

/-- An actual repeated-vertex poset edge has zero normalized coordinate. -/
example (M : P ⥤ A) (F : ComposableArrows Pᵒᵖ 1)
    (h : (F.obj (0 : Fin 2)).unop = (F.obj (1 : Fin 2)).unop) :
    ((inclusionOfNormalizedRoosComplex (I := P) (A := A)).app M).f 1 ≫ roosπ M F = 0 := by
  let FN : (nerve Pᵒᵖ).obj (op (SimplexCategory.mk 1)) := roosNerveSimplex 1 F
  have hStrict : FN ∈ (nerve Pᵒᵖ).nonDegenerate 1 ↔
      StrictAnti (fun i ↦ (F.obj i).unop) :=
    PartialOrder.nerve_op_nonDegenerate_iff_strictAnti F
  have hNot : FN ∉ (nerve Pᵒᵖ).nonDegenerate 1 := by
    intro hF
    have hh : (F.obj (1 : Fin 2)).unop < (F.obj (0 : Fin 2)).unop :=
      (hStrict.mp hF) (show (0 : Fin 2) < (1 : Fin 2) by decide)
    rw [h] at hh
    exact lt_irrefl _ hh
  have hDeg : FN ∈ (nerve Pᵒᵖ).degenerate 1 :=
    (SSet.mem_degenerate_iff_notMem_nonDegenerate (nerve Pᵒᵖ) FN).mpr hNot
  change roosInclusionAt M 1 ≫ roosChainProjection M F = 0
  exact inclusionOfNormalizedRoosComplex_f_π_degenerate M 1 FN hDeg

end
