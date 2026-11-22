/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceConstructors

/-!
# Whole original reduced paths as native flagged necklaces

Every original reduced path is realized by its complete native necklace,
whole input map and all original coefficient flags. The construction
retains the same original empty and concatenated paths, with flanking
proved from their actual flags.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBead OriginalBead.TerminalFlag
open SSet.OriginalNecklace SSet.OriginalTwoBead.OrdinalCharts

/-- A whole original normal bead has precisely the actual native flanking flags. -/
theorem ofNormalBead_isFlanked {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (b : NormalForms.NormalBead K x y q) : IsFlanked (ofBead b.bead) := by
  constructor
  · intro j
    have h : ∀ i : Fin (b.bead.dimension + 1),
        ULift.up.{u} i ∈ ((NormalForms.coefficient b.bead).obj 0).I ↔
          i ∈ ({0, Fin.last b.bead.dimension} : Finset (Fin (b.bead.dimension + 1))) := by
      intro i
      rw [b.first]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert,
        Finset.mem_singleton, ULift.up_inj]
    exact h j
  · exact b.last

/-- The whole original zero necklace has its same singleton/full flanking flags. -/
theorem unit_isFlanked (K : SSet.{u}) (q : SimplexCategoryᵒᵖ) (x : K _⦋0⦌) :
    IsFlanked (unit K q x) := by
  constructor
  · intro j
    have hj : j = 0 := @Subsingleton.elim (Fin 1) inferInstance j 0
    subst j
    exact iff_of_true ((Point.pointCoefficient q).obj 0).left (Finset.mem_singleton_self _)
  · ext j
    have hj : j = ULift.up.{u} (0 : Fin 1) :=
      @Subsingleton.elim (ULift.{u} (Fin 1)) inferInstance j _
    subst j
    exact iff_of_true ((Point.pointCoefficient q).obj (Fin.last q.unop.len)).left (Set.mem_univ _)

/-- Concatenation retains exactly both whole original flanking flags. -/
theorem concat_isFlanked {K : SSet.{u}} {x y z : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (T : Object K x y q) (U : Object K y z q) (hT : IsFlanked T) (hU : IsFlanked U) :
    IsFlanked (concat T U) := by
  constructor
  · intro j
    change ULift.up.{u} j ∈
      (ConcatFlags.prefixLift T.necklace.dimension U.necklace.dimension '' (T.coefficient.obj 0).I ∪
        ConcatFlags.suffixLift T.necklace.dimension U.necklace.dimension '' (U.coefficient.obj 0).I) ↔
      j ∈ (T.necklace.joints.map (prefixEmbedding T.necklace.dimension U.necklace.dimension).toEmbedding ∪
        U.necklace.joints.map (suffix T.necklace.dimension U.necklace.dimension).toEmbedding)
    constructor
    · rintro (⟨i, hi, hij⟩ | ⟨i, hi, hij⟩)
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr
          ⟨i.down, (hT.1 i.down).mp hi, congrArg ULift.down hij⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_map.mpr
          ⟨i.down, (hU.1 i.down).mp hi, congrArg ULift.down hij⟩))
    · intro hj
      rcases Finset.mem_union.mp hj with hj | hj
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
        exact Or.inl ⟨ULift.up.{u} i, (hT.1 i).mpr hi, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
        exact Or.inr ⟨ULift.up.{u} i, (hU.1 i).mpr hi, rfl⟩
  · exact ConcatFlags.final_full T.coefficient U.coefficient hT.2 hU.2

/-- The SAME entire original normal path as a complete native flagged necklace. -/
def ofNormalPath {K : SSet.{u}} {q : SimplexCategoryᵒᵖ} {x y : K _⦋0⦌}
    (p : NormalForms.Path K q x y) : Object K x y q := by
  induction p with
  | nil => exact unit K q x
  | @cons y z p b ih => exact concat ih (ofBead b.bead)

/-- Every same original normal path has its actual whole native flanked realization. -/
theorem ofNormalPath_isFlanked {K : SSet.{u}} {q : SimplexCategoryᵒᵖ} {x y : K _⦋0⦌}
    (p : NormalForms.Path K q x y) : IsFlanked (ofNormalPath p) := by
  induction p with
  | nil => exact unit_isFlanked K q x
  | @cons y z p b ih =>
    exact concat_isFlanked (ofNormalPath p) (ofBead b.bead) ih (ofNormalBead_isFlanked b)

/-- The actual original empty path is realized by the same original zero necklace. -/
theorem ofNormalPath_empty (K : SSet.{u}) (q : SimplexCategoryᵒᵖ) (x : K _⦋0⦌) :
    ofNormalPath (NormalForms.empty K q x) = unit K q x := rfl

/-- The entire original final bead is glued by the actual original native concatenation. -/
theorem ofNormalPath_cons {K : SSet.{u}} {q : SimplexCategoryᵒᵖ} {x y z : K _⦋0⦌}
    (p : NormalForms.Path K q x y) (b : NormalForms.NormalBead K y z q) :
    ofNormalPath (@Quiver.Path.cons (K _⦋0⦌) (NormalForms.quiver K q) x y z p b) =
      concat (ofNormalPath p) (ofBead b.bead) := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
