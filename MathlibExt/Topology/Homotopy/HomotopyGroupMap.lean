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

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Maps on cube-based homotopy groups

A continuous map postcomposes generalized loops and preserves homotopies
relative to the cube boundary.  This descends to a map on `HomotopyGroup`,
with strict identity and composition laws.  When the cube has a nonempty
indexing type, the induced map is multiplicative and is bundled as a monoid
homomorphism.

The source and target spaces and the cube index may live in independent
universes.  This file makes no comparison with singular homotopy groups and
introduces no basepoint-change or weak-equivalence API.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped unitInterval Topology Topology.Homotopy

universe u v w z

namespace GenLoop

variable {N : Type w} {X : Type u} {Y : Type v} {Z : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {x : X}

/-- Postcompose a generalized loop by a continuous map. -/
def map (f : C(X, Y)) (p : Ω^ N X x) : Ω^ N Y (f x) :=
  ⟨f.comp p.1, fun y hy => congrArg f (GenLoop.boundary p y hy)⟩

@[simp]
theorem map_apply (f : C(X, Y)) (p : Ω^ N X x) (y : I^N) :
    map f p y = f (p y) :=
  rfl

@[simp]
theorem map_id (p : Ω^ N X x) :
    map (ContinuousMap.id X) p = p := by
  ext y
  rfl

/-- Generalized-loop postcomposition respects source-first composition. -/
theorem map_comp (f : C(X, Y)) (g : C(Y, Z)) (p : Ω^ N X x) :
    map (g.comp f) p = map g (map f p) := by
  ext y
  rfl

@[simp]
theorem map_const (f : C(X, Y)) :
    map f (GenLoop.const : Ω^ N X x) = GenLoop.const := by
  ext y
  rfl

/-- Postcomposition commutes with concatenation in a chosen cube direction. -/
theorem map_transAt [DecidableEq N] (f : C(X, Y)) (i : N)
    (p q : Ω^ N X x) :
    map f (transAt i p q) = transAt i (map f p) (map f q) := by
  ext t
  simp only [map_apply, transAt, coe_copy]
  split_ifs <;> rfl

namespace Homotopic

/-- Postcomposition preserves homotopy relative to the cube boundary. -/
theorem map {p q : Ω^ N X x} (h : Homotopic p q) (f : C(X, Y)) :
    Homotopic (GenLoop.map f p) (GenLoop.map f q) :=
  h.comp_continuousMap f

end Homotopic

end GenLoop

namespace HomotopyGroup

variable {N : Type w} {X : Type u} {Y : Type v} {Z : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {x : X}

/-- The homotopy class of a generalized loop. -/
def mk (p : Ω^ N X x) : HomotopyGroup N X x :=
  Quotient.mk _ p

/-- Every cube-based homotopy class has a generalized-loop representative. -/
theorem mk_surjective :
    Function.Surjective (mk : Ω^ N X x → HomotopyGroup N X x) :=
  Quotient.mk_surjective

/-- The map on cube-based homotopy groups induced by a continuous map. -/
def map (f : C(X, Y)) : HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map (GenLoop.map f) (fun _ _ h => GenLoop.Homotopic.map h f)

@[simp]
theorem map_mk (f : C(X, Y)) (p : Ω^ N X x) :
    map f (mk p) = mk (GenLoop.map f p) :=
  rfl

@[simp]
theorem map_id (a : HomotopyGroup N X x) :
    map (ContinuousMap.id X) a = a := by
  obtain ⟨p, rfl⟩ := mk_surjective a
  rw [map_mk, GenLoop.map_id]
  rfl

/-- Homotopy-group maps respect source-first composition. -/
theorem map_comp (f : C(X, Y)) (g : C(Y, Z))
    (a : HomotopyGroup N X x) :
    map (g.comp f) a = map g (map f a) := by
  obtain ⟨p, rfl⟩ := mk_surjective a
  rw [map_mk, map_mk, map_mk, GenLoop.map_comp]

variable [DecidableEq N] [Nonempty N]

@[simp]
theorem one_eq_mk_const :
    (1 : HomotopyGroup N X x) = mk (GenLoop.const : Ω^ N X x) :=
  rfl

@[simp]
theorem mul_mk (i : N) (p q : Ω^ N X x) :
    mk p * mk q = mk (GenLoop.transAt i q p) :=
  HomotopyGroup.mul_spec

@[simp]
theorem map_one (f : C(X, Y)) :
    map (N := N) f (1 : HomotopyGroup N X x) = 1 := by
  rw [one_eq_mk_const, map_mk, GenLoop.map_const, ← one_eq_mk_const]

/-- The induced map is multiplicative when the cube index is nonempty. -/
theorem map_mul (f : C(X, Y)) (a b : HomotopyGroup N X x) :
    map f (a * b) = map f a * map f b := by
  obtain ⟨p, rfl⟩ := mk_surjective a
  obtain ⟨q, rfl⟩ := mk_surjective b
  rw [mul_mk (Classical.arbitrary N), map_mk, GenLoop.map_transAt,
    map_mk, map_mk, mul_mk (Classical.arbitrary N)]

/-- The multiplicative map on positive cube-based homotopy groups. -/
def mapHom (f : C(X, Y)) :
    HomotopyGroup N X x →* HomotopyGroup N Y (f x) where
  toFun := map f
  map_one' := map_one f
  map_mul' := map_mul f

@[simp]
theorem mapHom_apply (f : C(X, Y)) (a : HomotopyGroup N X x) :
    mapHom f a = map f a :=
  rfl

end HomotopyGroup
