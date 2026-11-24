/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision

/-!
# Iterated subdivision of simplicial sets

This file iterates Mathlib's categorical subdivision functor.  Iteration
starts at the identity and applies one further subdivision on the right at
each successor.  No realization, mesh, anodyne, chain-level, or `Ex∞` API is
introduced here.
-/

@[expose] public section

universe u

open CategoryTheory

namespace SSet

/-- The `k`-fold iterate of the simplicial subdivision functor. -/
noncomputable def sdIter : ℕ → SSet.{u} ⥤ SSet.{u}
  | 0 => 𝟭 _
  | k + 1 => sdIter k ⋙ sd

@[simp]
theorem sdIter_zero : sdIter.{u} 0 = 𝟭 _ :=
  rfl

@[simp]
theorem sdIter_succ (k : ℕ) : sdIter.{u} (k + 1) = sdIter k ⋙ sd :=
  rfl

@[simp]
theorem sdIter_obj_zero (X : SSet.{u}) : (sdIter 0).obj X = X :=
  rfl

@[simp]
theorem sdIter_obj_succ (k : ℕ) (X : SSet.{u}) :
    (sdIter (k + 1)).obj X = sd.obj ((sdIter k).obj X) :=
  rfl

@[simp]
theorem sdIter_map_zero {X Y : SSet.{u}} (f : X ⟶ Y) :
    (sdIter 0).map f = f :=
  rfl

@[simp]
theorem sdIter_map_succ {X Y : SSet.{u}} (k : ℕ) (f : X ⟶ Y) :
    (sdIter (k + 1)).map f = sd.map ((sdIter k).map f) :=
  rfl

end SSet
