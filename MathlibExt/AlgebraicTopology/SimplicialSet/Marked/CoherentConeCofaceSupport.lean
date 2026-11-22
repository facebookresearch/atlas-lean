/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeSupportedSubcomplex
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCoordinateFaces
import Mathlib.Order.Fin.Basic

/-!
# Actual original cone coface support

The lifted native coface is the original ordinal successor-above
embedding. Its full image excludes precisely the same original omitted
vertex. Consequently the whole cone face nerve is exactly the lower
coordinate-face subcomplex, with all its actual simplex operators and
maximum-preserving marking retained.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original lifted coface is precisely its native successor-above ordinal embedding. -/
def coneCofaceEmbedding {n : ℕ} (j : Fin (n + 2)) : Vertex.{u} n ↪o Vertex.{u} (n + 1) where
  toFun x := ULift.up (j.succAbove x.down)
  inj' := by
    intro x y h
    apply ULift.ext
    exact (Fin.succAboveOrderEmb j).injective (congrArg ULift.down h)
  map_rel_iff' := by
    intro x y
    exact (Fin.succAboveOrderEmb j).map_rel_iff

/-- This entire lifted order map is exactly the original simplex coface's order map, including every original vertex. -/
theorem coneCofaceEmbedding_orderHom {n : ℕ} (j : Fin (n + 2)) :
    (coneCofaceEmbedding.{u} j).toOrderHom = (SimplexCategory.δ j).toOrderHom.uliftMap := rfl

/-- The full original lifted coface image contains exactly the vertices different from its same omitted
  original vertex. -/
theorem mem_coneCofaceEmbedding_range {n : ℕ} (j : Fin (n + 2)) (x : Vertex.{u} (n + 1)) :
    x ∈ Set.range (coneCofaceEmbedding j) ↔ x ≠ ULift.up j := by
  constructor
  · rintro ⟨y, rfl⟩ h
    exact Fin.succAbove_ne j y.down (congrArg ULift.down h)
  · intro hx
    have hx' : x.down ≠ j := fun h => hx (ULift.ext h)
    obtain ⟨y, hy⟩ := Fin.exists_succAbove_eq hx'
    exact ⟨ULift.up y, ULift.ext hy⟩

/-- The actual whole supported coface image is precisely the original lower coordinate face, not merely its
  zero vertices. -/
theorem coneCofaceSupportedSubcomplex {n : ℕ} (j : Fin (n + 2)) (i : Vertex.{u} n) :
    coneSupportedSubcomplex (coneCofaceEmbedding j) i =
      coneCoordinateFace (coneCofaceEmbedding j i) (ULift.up j) false := by
  ext q x
  change (∀ t, ∀ k ∈ (x.obj t).vertices, k ∈ Set.range (coneCofaceEmbedding j)) ↔
    ∀ t, (ULift.up j ∈ (x.obj t).vertices) ↔ false = true
  simp only [mem_coneCofaceEmbedding_range, Bool.false_eq_true, iff_false]
  apply forall_congr'
  intro t
  constructor
  · intro h hj
    exact h _ hj rfl
  · intro h k hk he
    exact h (he ▸ hk)

/-- Every original cone coface has its genuine entire marked lower-coordinate-face isomorphism, with the
  actual omitted vertex and all original marks. -/
def coneCofaceMarkedIso {n : ℕ} (j : Fin (n + 2)) (i : Vertex.{u} n) :
    coneWeight i ≅ comap (coneWeight (coneCofaceEmbedding j i))
      (coneCoordinateFace (coneCofaceEmbedding j i) (ULift.up j) false).ι :=
  coneEmbeddingSupportedIso (coneCofaceEmbedding j) i ≪≫
    eqToIso (congrArg (fun A : (nerve (ConeSubset (coneCofaceEmbedding j i))).Subcomplex =>
      comap (coneWeight (coneCofaceEmbedding j i)) A.ι) (coneCofaceSupportedSubcomplex j i))

end SSet.Marked.CoherentWeight
