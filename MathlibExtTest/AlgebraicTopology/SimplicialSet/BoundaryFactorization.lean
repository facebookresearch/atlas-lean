/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryFactorization

/-! # Public clients of the intrinsic boundary factorization APIs -/

@[expose] public section

universe u

open CategoryTheory MorphismProperty

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.BoundaryFactorization

theorem exists_diagonal {A B X Y : SSet.{u}} (i : A ⟶ B) [Mono i]
    (p : X ⟶ Y) (hp : (monomorphisms SSet.{u}).rlp p)
    {top : A ⟶ X} {bottom : B ⟶ Y} (sq : CommSq top i p bottom) :
    ∃ l : B ⟶ X, i ≫ l = top ∧ l ≫ p = bottom := by
  have : IsWeakFactorizationSystem (monomorphisms SSet.{u})
      (monomorphisms SSet.{u}).rlp :=
    SSet.isWeakFactorizationSystem_monomorphisms
  have : HasLiftingProperty i p :=
    hasLiftingProperty_of_wfs (W₁ := monomorphisms SSet.{u})
      (W₂ := (monomorphisms SSet.{u}).rlp) i p
      (monomorphisms.infer_property i) hp
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

theorem per_map_contract {X Y : SSet.{u}} (f : X ⟶ Y) :
    let d := SSet.modelCategoryQuillen.monoFactorizationData f
    Mono d.i ∧ (monomorphisms SSet.{u}).rlp d.p ∧ d.i ≫ d.p = f := by
  exact ⟨inferInstance, (SSet.modelCategoryQuillen.monoFactorizationData f).hp,
    (SSet.modelCategoryQuillen.monoFactorizationData f).fac⟩

theorem functorial_squares {X Y X' Y' : SSet.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (φ : Arrow.mk f ⟶ Arrow.mk g) :
    let d := SSet.modelCategoryQuillen.monoFunctorialFactorizationData
    (d.factorizationData f).i ≫ d.mapZ φ = φ.left ≫ (d.factorizationData g).i ∧
      d.mapZ φ ≫ (d.factorizationData g).p = (d.factorizationData f).p ≫ φ.right := by
  exact ⟨SSet.modelCategoryQuillen.monoFunctorialFactorizationData.i_mapZ φ,
    SSet.modelCategoryQuillen.monoFunctorialFactorizationData.mapZ_p φ⟩

end MathlibExtTest.AlgebraicTopology.SimplicialSet.BoundaryFactorization
