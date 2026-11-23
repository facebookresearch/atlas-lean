/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_MumfordVertexType.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of
the Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Vertex types on a graph

The *type* of a vertex `w` relative to a base vertex `w₀` in a graph `𝒯`
is the parity, in `ZMod 2`, of the graph distance from `w₀` to `w`.
The subgroup of a group acting on the vertices that preserves every
vertex type is the type-preserving subgroup.
-/

@[expose] public section

namespace CerednikDrinfeld
namespace Mumford

variable {W : Type*}

/-- The type of `w` relative to `w₀`: the parity of `𝒯.dist w₀ w`. -/
public noncomputable def vertexType (𝒯 : SimpleGraph W) (w₀ w : W) : ZMod 2 :=
  (𝒯.dist w₀ w : ZMod 2)

public theorem vertexType_apply (𝒯 : SimpleGraph W) (w₀ w : W) :
    vertexType 𝒯 w₀ w = (𝒯.dist w₀ w : ZMod 2) :=
  rfl

@[simp] public theorem vertexType_self (𝒯 : SimpleGraph W) (w₀ : W) :
    vertexType 𝒯 w₀ w₀ = 0 := by
  rw [vertexType, SimpleGraph.dist_self, Nat.cast_zero]

/-- The subgroup of `G` preserving the type of every vertex. -/
public def typePreserving (G : Type*) [Group G] [MulAction G W]
    (𝒯 : SimpleGraph W) (w₀ : W) : Subgroup G where
  carrier := {g | ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w}
  one_mem' := fun w => by rw [one_smul]
  mul_mem' {g h} hg hh := fun w => by rw [mul_smul, hg, hh]
  inv_mem' {g} hg := fun w => by rw [← hg (g⁻¹ • w), smul_inv_smul]

@[simp] public theorem mem_typePreserving_iff {G : Type*} [Group G]
    [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W) (g : G) :
    g ∈ typePreserving G 𝒯 w₀ ↔
      ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w :=
  Iff.rfl

public theorem vertexType_smul_of_mem {G : Type*} [Group G] [MulAction G W]
    {𝒯 : SimpleGraph W} {w₀ : W} {g : G} (hg : g ∈ typePreserving G 𝒯 w₀)
    (w : W) : vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w :=
  hg w

end Mumford
end CerednikDrinfeld
