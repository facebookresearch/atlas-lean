/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceWholeBead

/-!
# Genuine original normalization of an endpoint-joint object

The SAME full original bead is normalized through its native actual epi.
The original object maps to a genuinely flanked totally nondegenerate
object, retaining the full original coefficient and input maps. This
includes every original dimension-zero object.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBead
open OriginalBead.TerminalFlag (coefficientObject)

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME whole original first flag of a flanked endpoint-joint object is exactly its two original endpoints. -/
theorem wholeBead_first (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) (hT : IsFlanked T) :
    ((NormalForms.coefficient (wholeBead T hJ)).obj 0).I =
      {ULift.up.{u} (0 : Fin (T.necklace.dimension + 1)), ULift.up.{u} (Fin.last T.necklace.dimension)} := by
  have h : ∀ j : Fin (T.necklace.dimension + 1), ULift.up.{u} j ∈ (T.coefficient.obj 0).I ↔
      ULift.up.{u} j ∈ ({ULift.up.{u} (0 : Fin (T.necklace.dimension + 1)),
        ULift.up.{u} (Fin.last T.necklace.dimension)} : Set (ULift.{u} (Fin (T.necklace.dimension + 1)))) := by
    intro j
    rw [hT.1 j, hJ]
    simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, ULift.up_inj]
  ext i
  exact h i.down

/-- The SAME whole original final flag of the full bead remains exactly the entire original vertex set. -/
theorem wholeBead_last (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) (hT : IsFlanked T) :
    ((NormalForms.coefficient (wholeBead T hJ)).obj (Fin.last q.unop.len)).I = Set.univ := hT.2

/-- The SAME actual original endpoint-joint object has a genuine flanked nondegenerate target and original map. -/
theorem exists_normalized_wholeBead (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) (hT : IsFlanked T) :
    ∃ N : Object K x y q, IsFlanked N ∧ TotallyNondegenerate N ∧ Nonempty (T ⟶ N) := by
  let b := wholeBead T hJ
  refine ⟨ofBead (Nondegenerate.normalize b), ?_, beadNormalization_target_totallyNondegenerate b,
    ⟨(wholeBeadIso T hJ).hom ≫ beadNormalization b⟩⟩
  exact beadNormalization_target_isFlanked b (wholeBead_first T hJ hT) (wholeBead_last T hJ hT)

/-- A SAME original dimension-zero necklace retains precisely its original endpoint joint set. -/
theorem zero_necklace_joints (T : SSet.OriginalNecklace.Data) (h0 : T.dimension = 0) :
    T.joints = {0, Fin.last T.dimension} := by
  ext i
  have hi : i = 0 := by
    apply Fin.ext
    change i.val = 0
    have hb := i.isLt
    omega
  subst i
  exact iff_of_true T.source_joint (Finset.mem_insert_self _ _)

/-- Every SAME original zero-dimensional flagged object has its genuine original nondegenerate target. -/
theorem exists_normalized_zero (T : Object K x y q) (h0 : T.necklace.dimension = 0) (hT : IsFlanked T) :
    ∃ N : Object K x y q, IsFlanked N ∧ TotallyNondegenerate N ∧ Nonempty (T ⟶ N) :=
  exists_normalized_wholeBead T (zero_necklace_joints T.necklace h0) hT

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
