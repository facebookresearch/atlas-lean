/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceConcatenationPushout
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadInterval

/-!
# The complete actual bead intervals of an original necklace

A bead is an interval between consecutive original joints. Its entire
native standard simplex maps into the original necklace by the SAME
original interval embedding, with both original vertex equations.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open CategoryTheory.CoherentRealization.OriginalBeadInterval

/-- An actual full positive bead between consecutive original necklace joints. -/
structure IsBead (T : Data) (a b : Fin (T.dimension + 1)) : Prop where
  /-- The actual source of the bead is an original joint. -/
  source : a ∈ T.joints
  /-- The actual target of the bead is an original joint. -/
  target : b ∈ T.joints
  /-- The full original bead is positive-dimensional. -/
  positive : a < b
  /-- There is no actual necklace joint in the strict original interval. -/
  consecutive : ∀ j ∈ T.joints, j ≤ a ∨ b ≤ j

variable {T : Data} {a b : Fin (T.dimension + 1)}

/-- Every complete original interval simplex belongs to its SAME original necklace. -/
theorem bead_interval_mem (h : IsBead T a b) {d : ℕ}
    (s : (Δ[length a b] : SSet.{u}) _⦋d⦌) :
    (SSet.stdSimplex.map (operator a b h.positive.le)).app (op ⦋d⦌) s ∈
      (complex T.joints).obj (op ⦋d⦌) := by
  apply (mem_complex_iff _ _).mpr
  intro j hj
  rcases h.consecutive j hj with hj | hj
  · apply Or.inr
    intro i
    apply hj.trans
    have hi := (embedding a b h.positive.le).monotone (Fin.zero_le (s i))
    rw [embedding_zero] at hi
    exact hi
  · apply Or.inl
    intro i
    apply le_trans _ hj
    have hi := (embedding a b h.positive.le).monotone (Fin.le_last (s i))
    rw [embedding_last] at hi
    exact hi

/-- The whole actual original interval bead map into its SAME native necklace. -/
def beadMap (h : IsBead T a b) : (Δ[length a b] : SSet.{u}) ⟶ T.object :=
  SSet.Subcomplex.lift (SSet.stdSimplex.map (operator a b h.positive.le)) (by
    rintro ⟨⟨d⟩⟩ s ⟨c, rfl⟩
    exact bead_interval_mem h c)

/-- The full actual original bead map has precisely its native interval readback. -/
@[reassoc]
theorem beadMap_ι (h : IsBead T a b) :
    beadMap.{u} h ≫ (complex T.joints).ι =
      SSet.stdSimplex.map (operator a b h.positive.le) := rfl

/-- The SAME original initial bead vertex maps to the actual original source joint. -/
theorem beadMap_source (h : IsBead T a b) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋length a b⦌ 0) ≫ beadMap.{u} h =
      vertexMap T.joints a := by
  apply (cancel_mono (complex.{u} T.joints).ι).1
  rw [Category.assoc, beadMap_ι, vertexMap_ι, ← SSet.stdSimplex.map_comp]
  congr 1

/-- The SAME original terminal bead vertex maps to the actual original target joint. -/
theorem beadMap_target (h : IsBead T a b) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋length a b⦌ (Fin.last (length a b))) ≫
      beadMap.{u} h = vertexMap T.joints b := by
  apply (cancel_mono (complex.{u} T.joints).ι).1
  rw [Category.assoc, beadMap_ι, vertexMap_ι, ← SSet.stdSimplex.map_comp]
  congr 1
  ext i : 3
  exact embedding_last a b h.positive.le

/-- The full native simplex of an actual original necklace bead. -/
def beadSimplex (h : IsBead T a b) : T.object.{u} _⦋length a b⦌ :=
  SSet.yonedaEquiv (beadMap h)

/-- The full original source bead simplex is genuinely nondegenerate in the native necklace. -/
theorem beadSimplex_nondegenerate (h : IsBead T a b) :
    beadSimplex.{u} h ∈ T.object.nonDegenerate (length a b) := by
  apply (SSet.Subcomplex.mem_nonDegenerate_iff _ _).mpr
  apply (SSet.stdSimplex.mem_nonDegenerate_iff_strictMono _).mpr
  exact (embedding a b h.positive.le).strictMono

end SSet.OriginalNecklace
