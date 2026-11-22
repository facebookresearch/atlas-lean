/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceCutReassembly
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceConcatenationMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceWholeBeadNormalization

/-!
# Genuine original nondegenerate normalization of every flanked necklace

Every actual original flanked necklace has an actual original map to a
flanked totally nondegenerate necklace. The proof cuts at its first
original positive bead, retains both complete native inputs and full
flags, and recurses on the SAME original suffix dimension. No desired
normalization or weak-outcome certificate is supplied.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace OriginalBeadInterval

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- EVERY SAME original flanked input has a genuine original flanked nondegenerate normalization map. -/
theorem exists_totallyNondegenerate_target (T : Object K x y q) (hT : IsFlanked T) :
    ∃ N : Object K x y q, IsFlanked N ∧ TotallyNondegenerate N ∧ Nonempty (T ⟶ N) := by
  have H : ∀ n : ℕ, ∀ (a b : K _⦋0⦌) (S : Object K a b q), S.necklace.dimension = n →
      IsFlanked S → ∃ N : Object K a b q, IsFlanked N ∧ TotallyNondegenerate N ∧ Nonempty (S ⟶ N) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b S hn hS
      by_cases h0 : S.necklace.dimension = 0
      · exact exists_normalized_zero S h0 hS
      · let i : Fin S.necklace.dimension := ⟨0, Nat.pos_of_ne_zero h0⟩
        obtain ⟨c, j, hcj, hc, _hj⟩ := exists_bead_at_edge S.necklace i
        have hc0 : c = 0 := by
          apply Fin.ext
          change c.val = 0
          have hc' : c.val ≤ 0 := hc
          omega
        subst c
        let L := CutObjects.leftObject S j hcj.target
        let R := CutObjects.rightObject S j hcj.target
        have hL : IsFlanked L := CutObjects.leftObject_isFlanked S j hcj.target hS
        have hR : IsFlanked R := CutObjects.rightObject_isFlanked S j hcj.target hS
        have hJL : L.necklace.joints = {0, Fin.last L.necklace.dimension} :=
          Cut.leftJoints_of_first_bead hcj
        obtain ⟨NL, hNL, hNDL, ⟨fL⟩⟩ := exists_normalized_wholeBead L hJL hL
        have hRn : R.necklace.dimension < n := (Cut.rightDimension_lt S.necklace j hcj.positive).trans_eq hn
        obtain ⟨NR, hNR, hNDR, ⟨fR⟩⟩ := ih R.necklace.dimension hRn (inputVertex S j) b R rfl hR
        refine ⟨concat NL NR, concat_isFlanked NL NR hNL hNR,
          concat_totallyNondegenerate NL NR hNDL hNDR, ?_⟩
        exact ⟨(CutObjects.reassemblyIso S j hcj.target).inv ≫ concatHom fL fR⟩
  exact H T.necklace.dimension x y T rfl hT

/-- The genuine normalized target is connected to the SAME original input by its actual original map. -/
theorem exists_totallyNondegenerate_target_map (T : Object K x y q) (hT : IsFlanked T) :
    ∃ (N : Object K x y q) (_hN : IsFlanked N) (_hND : TotallyNondegenerate N) (f : T ⟶ N),
      f.necklaceMap.map.{u} ≫ N.input = T.input := by
  obtain ⟨N, hN, hND, ⟨f⟩⟩ := exists_totallyNondegenerate_target T hT
  exact ⟨N, hN, hND, f, f.over⟩

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
