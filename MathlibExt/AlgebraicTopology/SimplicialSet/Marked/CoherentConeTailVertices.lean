/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCofaceSupport
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterUpperCover

/-!
# Original tail vertices of the zeroth cone coface

The original zeroth coface identifies the original smaller ordinal
with precisely the vertices strictly beyond the new root. This uses
the actual coface embedding, including its original lifted vertices
in every value universe and in the zero-dimensional case.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The actual original zeroth coface embedding of the whole lifted vertex ordinal. -/
def coneTailEmbedding (n : ℕ) : Vertex.{u} n ↪o Vertex.{u} (n + 1) :=
  coneCofaceEmbedding (0 : Fin (n + 2))

/-- The tail embedding is exactly the original zeroth simplex coface order map. -/
theorem coneTailEmbedding_orderHom (n : ℕ) :
    (coneTailEmbedding.{u} n).toOrderHom =
      (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom.uliftMap :=
  coneCofaceEmbedding_orderHom _

/-- Every original tail vertex is strictly beyond the same new original root. -/
theorem coneTailEmbedding_positive {n : ℕ} (i : Vertex.{u} n) :
    (⊥ : Vertex.{u} (n + 1)) < coneTailEmbedding n i := by
  change (0 : Fin (n + 2)) < (0 : Fin (n + 2)).succAbove i.down
  rw [Fin.succAbove_zero]
  change 0 < i.down.val + 1
  exact Nat.succ_pos _

/-- The original zeroth coface is the order isomorphism onto precisely the original positive tail vertices. -/
def coneTailVertexOrderIso (n : ℕ) : Vertex.{u} n ≃o AfterVertex (⊥ : Vertex.{u} (n + 1)) where
  toEquiv := Equiv.ofBijective (fun i => ⟨coneTailEmbedding n i, coneTailEmbedding_positive i⟩) (by
    constructor
    · intro i j h
      exact (coneTailEmbedding n).injective (congrArg Subtype.val h)
    · intro j
      have hj : j.val ≠ ULift.up (0 : Fin (n + 2)) := ne_of_gt j.property
      obtain ⟨i, hi⟩ := (mem_coneCofaceEmbedding_range (0 : Fin (n + 2)) j.val).mpr hj
      exact ⟨i, Subtype.ext hi⟩)
  map_rel_iff' := by
    intro i j
    change coneTailEmbedding n i ≤ coneTailEmbedding n j ↔ i ≤ j
    exact (coneTailEmbedding n).le_iff_le

/-- The tail vertex isomorphism keeps exactly the original coface image vertex. -/
theorem coneTailVertexOrderIso_apply (n : ℕ) (i : Vertex.{u} n) :
    (coneTailVertexOrderIso n i).val = coneTailEmbedding n i := rfl

end SSet.Marked.CoherentWeight
