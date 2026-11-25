/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
import Mathlib.CategoryTheory.LiftingProperties.Over

/-!
# Native factorization and lifting classes in a slice

The original factorization of an underlying map carries its full target
projection to the fixed base. Both resulting maps are the same original
factors. Native slice lifting transfers the proved original lifting
property, so an actual weak factorization system induces one in every
slice without a new model or functor-category construction.
-/

noncomputable section
universe v u
open CategoryTheory

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (W₁ W₂ : MorphismProperty C) (S : C)

/-- Keep the original intermediate object and both native factors with their whole base maps. -/
def overFactorizationData {X Y : Over S} (f : X ⟶ Y)
    (r : MapFactorizationData W₁ W₂ f.left) :
    MapFactorizationData (W₁.inverseImage (Over.forget S)) (W₂.inverseImage (Over.forget S)) f where
  Z := Over.mk (r.p ≫ Y.hom)
  i := Over.homMk r.i (by
    change r.i ≫ (r.p ≫ Y.hom) = X.hom
    rw [← Category.assoc, r.fac]
    exact Over.w f)
  p := Over.homMk r.p rfl
  fac := Over.OverMorphism.ext r.fac
  hi := r.hi
  hp := r.hp

/-- The actual original weak factorization system induces its native inverse-image classes in every
slice. -/
theorem IsWeakFactorizationSystem.over [IsWeakFactorizationSystem W₁ W₂] :
    IsWeakFactorizationSystem (W₁.inverseImage (Over.forget S)) (W₂.inverseImage (Over.forget S)) :=
      by
  let _ : W₁.IsStableUnderRetracts := by
    rw [← llp_eq_of_wfs W₁ W₂]
    infer_instance
  let _ : W₂.IsStableUnderRetracts := by
    rw [← rlp_eq_of_wfs W₁ W₂]
    infer_instance
  let _ : HasFactorization (W₁.inverseImage (Over.forget S)) (W₂.inverseImage (Over.forget S)) :=
    ⟨fun f => ⟨overFactorizationData W₁ W₂ S f (factorizationData W₁ W₂ f.left)⟩⟩
  apply IsWeakFactorizationSystem.mk' _ _
  intro A D X Y i p hi hp
  let _ : HasLiftingProperty i.left p.left := hasLiftingProperty_of_wfs (W₁ := W₁) (W₂ :=
    W₂) i.left p.left hi hp
  exact HasLiftingProperty.over i p

end CategoryTheory.MorphismProperty
