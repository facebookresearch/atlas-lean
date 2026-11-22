/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceBeadNormalization

/-!
# The SAME full flags of an original nondegenerate bead

The actual native nondegenerate epi retains the original endpoint-only
first flag and whole final flag. Its complete original target is flanked
and totally nondegenerate, including dimension-zero normalizations.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBead OriginalBead.TerminalFlag
open SSet.OriginalNecklace

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- Both SAME full original endpoint and terminal flags give the actual whole-bead flanking property. -/
theorem ofBead_isFlanked_of_flags (b : Bead K x y q)
    (hfirst : ((NormalForms.coefficient b).obj 0).I =
      {ULift.up.{u} (0 : Fin (b.dimension + 1)), ULift.up.{u} (Fin.last b.dimension)})
    (hlast : ((NormalForms.coefficient b).obj (Fin.last q.unop.len)).I = Set.univ) :
    IsFlanked (ofBead b) := by
  constructor
  · intro i
    have h : ∀ i : Fin (b.dimension + 1),
        ULift.up.{u} i ∈ ((NormalForms.coefficient b).obj 0).I ↔
          i ∈ ({0, Fin.last b.dimension} : Finset (Fin (b.dimension + 1))) := by
      intro j
      rw [hfirst]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert,
        Finset.mem_singleton, ULift.up_inj]
    exact h i
  · exact hlast

/-- The SAME whole-bead normalization is flanked by its actual original full flag images. -/
theorem beadNormalization_target_isFlanked (b : Bead K x y q)
    (hfirst : ((NormalForms.coefficient b).obj 0).I =
      {ULift.up.{u} (0 : Fin (b.dimension + 1)), ULift.up.{u} (Fin.last b.dimension)})
    (hlast : ((NormalForms.coefficient b).obj (Fin.last q.unop.len)).I = Set.univ) :
    IsFlanked (ofBead (Nondegenerate.normalize b)) := by
  apply ofBead_isFlanked_of_flags
  · exact OriginalBead.OuterOperator.map_first_endpoints (Nondegenerate.operator b) b.coefficient hfirst
  · exact OriginalBead.OuterOperator.map_last_full (Nondegenerate.operator b) b.coefficient hlast

/-- The SAME actual original normalized full bead retains the complete first and last flag properties. -/
theorem exists_normalized_bead (b : Bead K x y q)
    (hfirst : ((NormalForms.coefficient b).obj 0).I =
      {ULift.up.{u} (0 : Fin (b.dimension + 1)), ULift.up.{u} (Fin.last b.dimension)})
    (hlast : ((NormalForms.coefficient b).obj (Fin.last q.unop.len)).I = Set.univ) :
    ∃ T : Object K x y q, IsFlanked T ∧ TotallyNondegenerate T ∧ Nonempty (ofBead b ⟶ T) :=
  ⟨ofBead (Nondegenerate.normalize b), beadNormalization_target_isFlanked b hfirst hlast,
    beadNormalization_target_totallyNondegenerate b, ⟨beadNormalization b⟩⟩

/-- The whole original zero necklace is genuinely totally nondegenerate, retaining its actual empty bead family. -/
theorem unit_totallyNondegenerate (K : SSet.{u}) (q : SimplexCategoryᵒᵖ) (x : K _⦋0⦌) :
    TotallyNondegenerate (unit K q x) := by
  intro a b h
  have ha : a.val < 1 := a.isLt
  have hb : b.val < 1 := b.isLt
  have hp := h.positive
  change a.val < b.val at hp
  omega

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
