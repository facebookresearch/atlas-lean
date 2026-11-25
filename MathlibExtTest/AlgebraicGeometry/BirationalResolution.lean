/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.BirationalResolution

@[expose] public section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.BirationalResolution

universe u

-- The identity is birational: it agrees with the identity partial isomorphism.
example (X : Scheme.{u}) : IsBirationalMorphism (𝟙 X) := isBirationalMorphism_id X

-- Birationality of a morphism is Mathlib's birationality over the target.
example {X Y : Scheme.{u}} (f : Y ⟶ X) :
    IsBirationalMorphism f ↔ Scheme.BirationalOver f (𝟙 X) := Iff.rfl

-- A resolution's morphism is birational and an isomorphism over every smooth open.
example {k : Type u} [Field k] (X : Over (Spec (.of k))) (R : ResolutionModel X) :
    IsBirationalMorphism R.morphism.left := R.birational

example {k : Type u} [Field k] (X : Over (Spec (.of k))) (R : ResolutionModel X)
    (U : X.left.Opens) (hU : Smooth (U.ι ≫ X.hom)) :
    IsIso (R.morphism.left.resLE U (R.morphism.left ⁻¹ᵁ U) le_rfl) :=
  R.unchangedSmooth U hU

-- Restricting over a target open keeps the morphism over `k`.
example {k : Type u} [Field k] {Y X : Over (Spec (.of k))} (f : Y ⟶ X) (U : X.left.Opens) :
    (restrictOver f U).left = f.left.resLE U (f.left ⁻¹ᵁ U) le_rfl := rfl
