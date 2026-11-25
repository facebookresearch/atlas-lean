/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

module

public import MathlibExt.GroupTheory.Perm.EmbeddingExtension
public import Mathlib.Data.Fin.Embedding
import Lean.Elab.Tactic.Omega

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace MathlibExtTest.EmbeddingExtension

/-- Grow the ambient finite degree at the first position, retaining the free block at the end. -/
def degreeGrowth (q n : ℕ) : Fin (q + n) ↪ Fin ((q + 1) + n) :=
  (Fin.succEmb (q + n)).trans (Fin.castLEEmb (by omega))

/-- The actual last-block inclusion is retained by the degree growth with its exact cardinal casts. -/
theorem degreeGrowth_freeBlock (q n : ℕ) :
    (Fin.natAddEmb q : Fin n ↪ Fin (q + n)).trans (degreeGrowth q n) =
      Fin.natAddEmb (q + 1) := by
  apply Function.Embedding.ext
  intro j
  apply Fin.ext
  change (q + j.val) + 1 = (q + 1) + j.val
  omega

/-- The complete selected free-block representative grows through the same ambient embedding. -/
theorem alignedRepresentative_degreeGrowth (q n : ℕ) (b : Fin n ↪ Fin (q + n)) :
    (Equiv.Perm.alignFiniteEmbeddings (Fin.natAddEmb q) b).viaEmbedding (degreeGrowth q n) =
      Equiv.Perm.alignFiniteEmbeddings (Fin.natAddEmb (q + 1)) (b.trans (degreeGrowth q n)) := by
  rw [Equiv.Perm.alignFiniteEmbeddings_viaEmbedding, degreeGrowth_freeBlock]

/-- Every original free-block label is carried to its chosen image in the grown degree. -/
theorem alignedRepresentative_degreeGrowth_apply (q n : ℕ) (b : Fin n ↪ Fin (q + n))
    (j : Fin n) :
    ((Equiv.Perm.alignFiniteEmbeddings (Fin.natAddEmb q) b).viaEmbedding (degreeGrowth q n))
        (degreeGrowth q n ((Fin.natAddEmb q) j)) = degreeGrowth q n (b j) := by
  rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.alignFiniteEmbeddings_apply]

/-- The zero free block uses the genuine identity permutation in every ambient type. -/
theorem emptyBlock_identity {α : Type*} [DecidableEq α] (a b : Fin 0 ↪ α) :
    Equiv.Perm.alignFiniteEmbeddings a b = 1 := Equiv.Perm.alignFiniteEmbeddings_zero a b

end MathlibExtTest.EmbeddingExtension
