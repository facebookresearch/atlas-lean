/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceCutCoefficientReassembly

/-!
# Genuine SAME original flagged cut reassembly

Both whole original cut objects concatenate to an object isomorphic to
the SAME original flagged necklace. The maps retain the full native
inverse operators, entire original input map and EVERY original flag.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.CutObjects

open SSet.OriginalNecklace

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- Both complete SAME original cut objects in their actual native concatenation. -/
abbrev reassembled (T : Object K x y q) (j : Fin (T.necklace.dimension + 1)) (hj : j ∈ T.necklace.joints) :
    Object K x y q := concat (leftObject T j hj) (rightObject T j hj)

/-- The whole SAME original input map commutes with the actual native cut reassembly. -/
theorem reassembly_over (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) :
    (Cut.reassemblyMorphism T.necklace j hj).map.{u} ≫ T.input = (reassembled T j hj).input := by
  apply (concat_isPushout (Cut.leftData T.necklace j hj) (Cut.rightData T.necklace j hj)).hom_ext
  · change concatLeft (Cut.leftData T.necklace j hj) (Cut.rightData T.necklace j hj) ≫
      (Cut.nativeReassemblyIso T.necklace j hj).hom ≫ T.input =
        concatLeft _ _ ≫ (reassembled T j hj).input
    rw [← Category.assoc, Cut.reassembly_left, concatLeft_input]
  · change concatRight (Cut.leftData T.necklace j hj) (Cut.rightData T.necklace j hj) ≫
      (Cut.nativeReassemblyIso T.necklace j hj).hom ≫ T.input =
        concatRight _ _ ≫ (reassembled T j hj).input
    rw [← Category.assoc, Cut.reassembly_right, concatRight_input]

/-- The SAME whole native original cut reassembly as its actual full flagged map. -/
def reassembly (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) : reassembled T j hj ⟶ T where
  necklaceMap := Cut.reassemblyMorphism T.necklace j hj
  over := reassembly_over T j hj
  flags := reassembly_coefficient T j hj

/-- The entire SAME original input map commutes with the actual native inverse cut separation. -/
theorem separation_over (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) :
    (Cut.separationMorphism T.necklace j hj).map.{u} ≫ (reassembled T j hj).input = T.input := by
  rw [← reassembly_over T j hj, ← Category.assoc]
  change (Cut.nativeReassemblyIso T.necklace j hj).inv ≫
    (Cut.nativeReassemblyIso T.necklace j hj).hom ≫ T.input = T.input
  rw [Iso.inv_hom_id_assoc]

/-- EVERY original coefficient flag is retained by the SAME full inverse native separation. -/
theorem separation_coefficient (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) :
    (coefficientFunctor.{u}.map (Cut.separationMorphism T.necklace j hj)).app q T.coefficient =
      (reassembled T j hj).coefficient := by
  have h := ConcreteCategory.congr_hom
    (congr_app (coefficientIso.{u} (Cut.reassemblyIso T.necklace j hj)).hom_inv_id q)
      (reassembled T j hj).coefficient
  change (coefficientFunctor.{u}.map (Cut.separationMorphism T.necklace j hj)).app q
    ((coefficientFunctor.{u}.map (Cut.reassemblyMorphism T.necklace j hj)).app q
      (reassembled T j hj).coefficient) = (reassembled T j hj).coefficient at h
  rw [reassembly_coefficient] at h
  exact h

/-- The SAME complete original inverse cut separation as its actual original flagged map. -/
def separation (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) : T ⟶ reassembled T j hj where
  necklaceMap := Cut.separationMorphism T.necklace j hj
  over := separation_over T j hj
  flags := separation_coefficient T j hj

/-- The SAME actual cut reassembly is a genuine original flagged-necklace isomorphism. -/
def reassemblyIso (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) : reassembled T j hj ≅ T where
  hom := reassembly T j hj
  inv := separation T j hj
  hom_inv_id := Hom.ext (Cut.reassemblyIso T.necklace j hj).hom_inv_id
  inv_hom_id := Hom.ext (Cut.reassemblyIso T.necklace j hj).inv_hom_id

/-- The SAME actual first original cut map reads the full original input after reassembly. -/
theorem reassembly_first_input (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) :
    concatLeft (leftObject T j hj).necklace (rightObject T j hj).necklace ≫
      (reassembly T j hj).necklaceMap.map.{u} ≫ T.input = (leftObject T j hj).input := by
  change concatLeft _ _ ≫ (Cut.nativeReassemblyIso T.necklace j hj).hom ≫ T.input = _
  rw [← Category.assoc, Cut.reassembly_left]

/-- The SAME actual second original cut map reads the full original input after reassembly. -/
theorem reassembly_second_input (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) :
    concatRight (leftObject T j hj).necklace (rightObject T j hj).necklace ≫
      (reassembly T j hj).necklaceMap.map.{u} ≫ T.input = (rightObject T j hj).input := by
  change concatRight _ _ ≫ (Cut.nativeReassemblyIso T.necklace j hj).hom ≫ T.input = _
  rw [← Category.assoc, Cut.reassembly_right]

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.CutObjects
