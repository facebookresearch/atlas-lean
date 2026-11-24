/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBead
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOrderEmbeddingFace
import Mathlib.Data.Finset.Sort

/-!
# The actual terminal support of an original coherent coefficient

Every original flag lies in its same terminal flag. The native increasing
finite-set enumeration selects precisely these original vertices and
retains both original endpoints, including zero-dimensional beads.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.TerminalFlag

variable {n : ℕ} {q : SimplexCategoryᵒᵖ}

/-- The full original zero-to-last coefficient object. -/
abbrev coefficientObject (n : ℕ) : SSet.{u} :=
  nerve (SimplicialThickening.Path
    (ULift.up.{u} (0 : Fin (n + 1))) (ULift.up.{u} (Fin.last n)))

/-- The actual original vertices in the last supplied coefficient flag. -/
def support (p : (coefficientObject.{u} n).obj q) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (fun i => ULift.up i ∈ (p.obj (Fin.last q.unop.len)).I)

/-- Membership is literally membership in the same original final flag. -/
theorem mem_support (p : (coefficientObject.{u} n).obj q) (i : Fin (n + 1)) :
    i ∈ support p ↔ ULift.up.{u} i ∈ (p.obj (Fin.last q.unop.len)).I := by
  classical
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every whole original coefficient flag lies in its actual last flag. -/
theorem flag_subset_last (p : (coefficientObject.{u} n).obj q)
    (t : Fin (q.unop.len + 1)) :
    (p.obj t).I ⊆ (p.obj (Fin.last q.unop.len)).I :=
  (p.map (homOfLE (Fin.le_last t))).hom.down.down

/-- The original initial vertex belongs to the selected actual support. -/
theorem zero_mem (p : (coefficientObject.{u} n).obj q) :
    (0 : Fin (n + 1)) ∈ support p :=
  (mem_support p 0).mpr (p.obj (Fin.last q.unop.len)).left

/-- The original terminal vertex belongs to the selected actual support. -/
theorem last_mem (p : (coefficientObject.{u} n).obj q) :
    Fin.last n ∈ support p :=
  (mem_support p (Fin.last n)).mpr (p.obj (Fin.last q.unop.len)).right

/-- The actual selected bead dimension. -/
def dimension (p : (coefficientObject.{u} n).obj q) : ℕ := (support p).card - 1

/-- The support has precisely one more vertex than its actual selected dimension. -/
theorem card_support (p : (coefficientObject.{u} n).obj q) :
    (support p).card = dimension p + 1 := by
  have h := Finset.card_pos.mpr (show (support p).Nonempty from ⟨0, zero_mem p⟩)
  dsimp [dimension]
  omega

/-- The native increasing enumeration of the complete original final flag. -/
def embedding (p : (coefficientObject.{u} n).obj q) :
    Fin (dimension p + 1) ↪o Fin (n + 1) :=
  (support p).orderEmbOfFin (card_support p)

/-- The actual enumeration has exactly the original terminal-flag range. -/
theorem range_embedding (p : (coefficientObject.{u} n).obj q) :
    Set.range (embedding p) = (support p : Set (Fin (n + 1))) :=
  Finset.range_orderEmbOfFin (support p) (card_support p)

/-- The selected first vertex is the same original initial vertex. -/
theorem embedding_zero (p : (coefficientObject.{u} n).obj q) :
    embedding p 0 = 0 := by
  have hz : (0 : Fin (n + 1)) ∈ Set.range (embedding p) := by
    rw [range_embedding]
    exact zero_mem p
  obtain ⟨i, hi⟩ := hz
  apply le_antisymm
  · exact ((embedding p).monotone (Fin.zero_le i)).trans (le_of_eq hi)
  · exact Fin.zero_le _

/-- The selected last vertex is the same original terminal vertex. -/
theorem embedding_last (p : (coefficientObject.{u} n).obj q) :
    embedding p (Fin.last (dimension p)) = Fin.last n := by
  have hz : Fin.last n ∈ Set.range (embedding p) := by
    rw [range_embedding]
    exact last_mem p
  obtain ⟨i, hi⟩ := hz
  apply le_antisymm
  · exact Fin.le_last _
  · exact (le_of_eq hi.symm).trans ((embedding p).monotone (Fin.le_last i))

/-- The same selected original vertices at the full coefficient universe. -/
def liftedEmbedding (p : (coefficientObject.{u} n).obj q) :
    ULift.{u} (Fin (dimension p + 1)) ↪o ULift.{u} (Fin (n + 1)) where
  toFun i := ULift.up (embedding p i.down)
  inj' _ _ h := ULift.ext ((embedding p).injective (congrArg ULift.down h))
  map_rel_iff' := by
    intro i j
    exact (embedding p).map_rel_iff

/-- The literal original coefficient source equation. -/
theorem lifted_zero (p : (coefficientObject.{u} n).obj q) :
    liftedEmbedding p (ULift.up.{u} 0) = ULift.up.{u} (0 : Fin (n + 1)) :=
  ULift.ext (embedding_zero p)

/-- The literal original coefficient target equation. -/
theorem lifted_last (p : (coefficientObject.{u} n).obj q) :
    liftedEmbedding p (ULift.up.{u} (Fin.last (dimension p))) =
      ULift.up.{u} (Fin.last n) :=
  ULift.ext (embedding_last p)

/-- Every original flag vertex has its actual selected full-face preimage. -/
theorem flag_supported (p : (coefficientObject.{u} n).obj q)
    (t : Fin (q.unop.len + 1)) :
    (p.obj t).I ⊆ Set.range (liftedEmbedding p) := by
  intro x hx
  have hs : x.down ∈ support p :=
    (mem_support p x.down).mpr (flag_subset_last p t hx)
  have hr : x.down ∈ Set.range (embedding p) := by
    rw [range_embedding]
    exact hs
  obtain ⟨i, hi⟩ := hr
  exact ⟨ULift.up i, ULift.ext hi⟩

end CategoryTheory.CoherentRealization.OriginalBead.TerminalFlag
