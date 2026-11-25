/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.Matching
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Relative matching maps of simplicial morphisms

For `f : X ⟶ Y`, the relative matching object in degree `n` is
`Y[n] ×_(MₙY) MₙX`; the canonical map from `X[n]` is the relative matching map.

This file exposes only the primitive pullback construction and its two characteristic equations.
Functoriality, Reedy morphism classes, and model structures belong to later layers.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ)
variable [HasLimitsOfShape (matchingIndex n) C]
variable [HasPullback (matchingMap Y n) ((matchingObjectFunctor n).map f)]

/-- The pullback `Y[n] ×_(MₙY) MₙX` underlying the relative matching map. -/
noncomputable abbrev relativeMatchingObject : C :=
  pullback (matchingMap Y n) ((matchingObjectFunctor n).map f)

/-- The relative matching map `X[n] ⟶ Y[n] ×_(MₙY) MₙX`. -/
noncomputable def relativeMatchingMap :
    X.obj (op ⦋n⦌) ⟶ relativeMatchingObject f n :=
  pullback.lift (f.app (op ⦋n⦌)) (matchingMap X n)
    (matchingMap_naturality n f)

/-- The first projection of the relative matching map is the component of `f`. -/
@[reassoc (attr := simp)]
theorem relativeMatchingMap_fst :
    relativeMatchingMap f n ≫
        pullback.fst (matchingMap Y n) ((matchingObjectFunctor n).map f) =
      f.app (op ⦋n⦌) := by
  apply pullback.lift_fst

/-- The second projection of the relative matching map is the matching map of `X`. -/
@[reassoc (attr := simp)]
theorem relativeMatchingMap_snd :
    relativeMatchingMap f n ≫
        pullback.snd (matchingMap Y n) ((matchingObjectFunctor n).map f) =
      matchingMap X n := by
  apply pullback.lift_snd

end CategoryTheory.SimplicialObject
