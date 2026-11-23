/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.VertexType

@[expose] public section

open CerednikDrinfeld.Mumford

universe u

/-- Consumer with the original binders: the type of a vertex is the
parity of its distance from the base vertex. -/
private theorem exactSource {W : Type u} (𝒯 : SimpleGraph W) (w₀ w : W) :
    vertexType 𝒯 w₀ w = (𝒯.dist w₀ w : ZMod 2) :=
  vertexType_apply 𝒯 w₀ w

/-- Higher-universe consumer for the type-preserving subgroup. -/
example {W : Type (u + 1)} {G : Type u} [Group G] [MulAction G W]
    (𝒯 : SimpleGraph W) (w₀ : W) (g : G)
    (hg : ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w) :
    g ∈ typePreserving G 𝒯 w₀ :=
  (mem_typePreserving_iff 𝒯 w₀ g).2 hg

/-- The base vertex has type `0`, and the identity is type-preserving. -/
example {W : Type u} {G : Type u} [Group G] [MulAction G W]
    (𝒯 : SimpleGraph W) (w₀ : W) :
    vertexType 𝒯 w₀ w₀ = 0 ∧ (1 : G) ∈ typePreserving G 𝒯 w₀ :=
  ⟨vertexType_self 𝒯 w₀, Subgroup.one_mem _⟩

/-- On the complete graph on `Bool`, the two distinct vertices have
opposite types relative to `false`: distance `0` versus distance `1`. -/
example : vertexType (⊤ : SimpleGraph Bool) false true = 1 := by
  rw [vertexType_apply, SimpleGraph.dist_top_of_ne (by decide)]
  rfl
