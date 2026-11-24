/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.Latching
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Relative latching maps of simplicial morphisms

For `f : X ⟶ Y`, the relative latching object in degree `n` is
`X[n] ⨿_(LₙX) LₙY`; its canonical map to `Y[n]` is the relative latching map.

This file exposes only the primitive pushout construction and its two characteristic equations.
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
variable [HasColimitsOfShape (latchingIndex n) C]
variable [HasPushout (latchingMap X n) ((latchingObjectFunctor n).map f)]

/-- The pushout `X[n] ⨿_(LₙX) LₙY` underlying the relative latching map. -/
noncomputable abbrev relativeLatchingObject : C :=
  pushout (latchingMap X n) ((latchingObjectFunctor n).map f)

/-- The relative latching map `X[n] ⨿_(LₙX) LₙY ⟶ Y[n]`. -/
noncomputable def relativeLatchingMap :
    relativeLatchingObject f n ⟶ Y.obj (op ⦋n⦌) :=
  pushout.desc (f.app (op ⦋n⦌)) (latchingMap Y n)
    (latchingMap_naturality n f).symm

/-- The `X[n]` leg of the relative latching map is the component of `f`. -/
@[reassoc (attr := simp)]
theorem relativeLatchingMap_inl :
    pushout.inl (latchingMap X n) ((latchingObjectFunctor n).map f) ≫
        relativeLatchingMap f n =
      f.app (op ⦋n⦌) := by
  apply pushout.inl_desc

/-- The `LₙY` leg of the relative latching map is the latching map of `Y`. -/
@[reassoc (attr := simp)]
theorem relativeLatchingMap_inr :
    pushout.inr (latchingMap X n) ((latchingObjectFunctor n).map f) ≫
        relativeLatchingMap f n =
      latchingMap Y n := by
  apply pushout.inr_desc

end CategoryTheory.SimplicialObject
