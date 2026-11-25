/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHHornTensorAction

set_option autoImplicit false
noncomputable section
namespace MathlibExtTest.PointedCGWHHornTensorAction

open CategoryTheory MonoidalCategory
open scoped Simplicial
universe u v

example (n : ℕ) (i : Fin (n + 2)) :
    PointedCGWH.freePointHornRetraction.{u, v} n i =
      (Under.costar CGWH.point.{u, v}).map
        (CGWH.fullyFaithfulCgwhToTop.preimage
          (X := (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}) : CGWH.{u, v}))
          (Y := (SSet.toCGWHOfFinite
            (SSet.horn.{v} (n + 1) i) : CGWH.{u, v}))
          (TopCat.ofHom (SSet.realizedHornRetract (n + 1) i (Nat.succ_pos n)))) :=
  rfl

example (n : ℕ) (i : Fin (n + 2)) (K : PointedCGWH.{u, v}) :
    PointedCGWH.freePointHornTensorIntervalAction n i K =
      (α_ ((Under.costar CGWH.point.{u, v}).obj CGWH.homotopyInterval)
        ((Under.costar CGWH.point.{u, v}).obj
          (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}))) K).inv ≫
        (PointedCGWH.freePointHornIntervalAction n i ⊗ₘ 𝟙 K) :=
  rfl

example (n : ℕ) (i : Fin (n + 2)) :
    (Under.costar CGWH.point.{u, v}).map (CGWH.realizedHornInclusion.{v, u} n i) ≫
        PointedCGWH.freePointHornRetraction n i = 𝟙 _ :=
  PointedCGWH.freePointHorn_inclusion_ret n i

example (n : ℕ) (i : Fin (n + 2)) (K : PointedCGWH.{u, v}) :
    ((Under.costar CGWH.point.{u, v}).map (CGWH.realizedHornInclusion.{v, u} n i) ⊗ₘ 𝟙 K) ≫
        (PointedCGWH.freePointHornRetraction n i ⊗ₘ 𝟙 K) = 𝟙 _ :=
  PointedCGWH.freePointHornTensor_inclusion_ret n i K

example (n : ℕ) (i : Fin (n + 2)) (K : PointedCGWH.{u, v}) :
    (λ_ (((Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}))) ⊗ K)).inv ≫
        (PointedCGWH.freePointIntervalEndpoint 0 ⊗ₘ 𝟙 _) ≫
        PointedCGWH.freePointHornTensorIntervalAction n i K = 𝟙 _ :=
  PointedCGWH.freePointHornTensorIntervalAction_zero n i K

example (n : ℕ) (i : Fin (n + 2)) (K : PointedCGWH.{u, v}) :
    (λ_ (((Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}))) ⊗ K)).inv ≫
        (PointedCGWH.freePointIntervalEndpoint 1 ⊗ₘ 𝟙 _) ≫
        PointedCGWH.freePointHornTensorIntervalAction n i K =
      (PointedCGWH.freePointHornRetraction n i ⊗ₘ 𝟙 K) ≫
        ((Under.costar CGWH.point.{u, v}).map
          (CGWH.realizedHornInclusion.{v, u} n i) ⊗ₘ 𝟙 K) :=
  PointedCGWH.freePointHornTensorIntervalAction_one n i K

example (n : ℕ) (i : Fin (n + 2)) (K : PointedCGWH.{u, v}) :
    (𝟙 _ ⊗ₘ ((Under.costar CGWH.point.{u, v}).map
      (CGWH.realizedHornInclusion.{v, u} n i) ⊗ₘ 𝟙 K)) ≫
        PointedCGWH.freePointHornTensorIntervalAction n i K =
      (PointedCGWH.freePointIntervalCollapse ⊗ₘ 𝟙 _) ≫
        (λ_ (((Under.costar CGWH.point.{u, v}).obj
          (SSet.toCGWHOfFinite (SSet.horn.{v} (n + 1) i))) ⊗ K)).hom ≫
        ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} n i) ⊗ₘ 𝟙 K) :=
  PointedCGWH.freePointHornTensorIntervalAction_fix n i K

#print axioms PointedCGWH.freePointHornRetraction
#print axioms PointedCGWH.freePointHornIntervalAction
#print axioms PointedCGWH.freePointIntervalEndpoint
#print axioms PointedCGWH.freePointIntervalCollapse
#print axioms PointedCGWH.freePointHorn_inclusion_ret
#print axioms PointedCGWH.freePointHornIntervalAction_zero
#print axioms PointedCGWH.freePointHornIntervalAction_one
#print axioms PointedCGWH.freePointHornIntervalAction_fix
#print axioms PointedCGWH.freePointHornTensorIntervalAction
#print axioms PointedCGWH.freePointHornTensor_inclusion_ret
#print axioms PointedCGWH.freePointHornTensorIntervalAction_zero
#print axioms PointedCGWH.freePointHornTensorIntervalAction_one
#print axioms PointedCGWH.freePointHornTensorIntervalAction_fix

#lint only unusedArguments in
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHHornTensorAction

end MathlibExtTest.PointedCGWHHornTensorAction
