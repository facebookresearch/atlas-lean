/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Strict postcomposition maps on topological loop spaces

A continuous map sends a loop based at `x` to a loop based at the literal
image `f x` by postcomposition.  This file bundles that operation as a
continuous map and records its strict identity and composition laws.

The source and target spaces may live in different universes.  No
change-of-basepoint, singular comparison, degree shift, homotopy-group map,
weak-equivalence, or Q/S comparison is asserted here.
-/

@[expose] public section

set_option autoImplicit false

open scoped Topology

universe u v w

namespace ContinuousMap

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Strict postcomposition from loops at `x` to loops at the literal image
`f x`. -/
def strictLoopMap (f : C(X, Y)) (x : X) :
    C(LoopSpace X x, LoopSpace Y (f x)) where
  toFun gamma := gamma.map f.continuous
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact f.continuous.comp
      (continuous_eval.comp (continuous_fst.prodMk continuous_snd))

/-- The strict loop map is literal postcomposition on every loop. -/
@[simp]
theorem strictLoopMap_apply (f : C(X, Y)) (x : X)
    (gamma : LoopSpace X x) :
    strictLoopMap f x gamma = gamma.map f.continuous :=
  rfl

/-- The strict loop map of the identity is the identity continuous map. -/
@[simp]
theorem strictLoopMap_id (x : X) :
    strictLoopMap (ContinuousMap.id X) x =
      ContinuousMap.id (LoopSpace X x) := by
  apply ContinuousMap.ext
  intro gamma
  apply Path.ext
  rfl

/-- Strict loop postcomposition respects composition as an equality of
continuous maps. -/
@[simp]
theorem strictLoopMap_comp (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    (strictLoopMap g (f x)).comp (strictLoopMap f x) =
      strictLoopMap (g.comp f) x := by
  apply ContinuousMap.ext
  intro gamma
  apply Path.ext
  rfl

/-- A reflexive loop maps to the reflexive loop at the literal image point. -/
@[simp]
theorem strictLoopMap_refl (f : C(X, Y)) (x : X) :
    strictLoopMap f x (Path.refl x) = Path.refl (f x) := by
  apply Path.ext
  rfl

end ContinuousMap
