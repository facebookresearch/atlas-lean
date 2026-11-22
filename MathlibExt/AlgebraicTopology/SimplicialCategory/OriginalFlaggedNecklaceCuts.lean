/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceCutPushout
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceBeadInputs

/-!
# Entire original flags on actual native necklace cuts

Both cut coefficients retain precisely the original full flag preimages
under the SAME native interval embeddings. The cut input maps retain
both original endpoints and the same original intermediate input
vertex. Every genuinely flanked input gives genuinely flanked cuts.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.CutObjects

open SSet.OriginalNecklace OriginalBeadInterval
open OriginalBead.TerminalFlag (coefficientObject)

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The entire original prefix flag is its SAME native interval preimage. -/
def leftCoefficient (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) : (coefficientObject.{u} (length 0 j)).obj q where
  obj t :=
    { I := liftedEmbedding 0 j (Fin.zero_le j) ⁻¹' (T.coefficient.obj t).I
      left := (congrArg (fun k : ULift.{u} (Fin (T.necklace.dimension + 1)) =>
        k ∈ (T.coefficient.obj t).I) (lifted_zero.{u} 0 j (Fin.zero_le j))).mpr
          (T.coefficient.obj t).left
      right := (congrArg (fun k : ULift.{u} (Fin (T.necklace.dimension + 1)) =>
        k ∈ (T.coefficient.obj t).I) (lifted_last.{u} 0 j (Fin.zero_le j))).mpr
          (joints_all_flags T t j hj)
      left_le i _ := Fin.zero_le i.down
      le_right i _ := Fin.le_last i.down }
  map f := ⟨homOfLE (fun i hi => (T.coefficient.map f).hom.down.down hi)⟩

/-- The entire original suffix flag is its SAME native interval preimage. -/
def rightCoefficient (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) : (coefficientObject.{u} (length j (Fin.last T.necklace.dimension))).obj q where
  obj t :=
    { I := liftedEmbedding j (Fin.last T.necklace.dimension) (Fin.le_last j) ⁻¹' (T.coefficient.obj t).I
      left := (congrArg (fun k : ULift.{u} (Fin (T.necklace.dimension + 1)) =>
        k ∈ (T.coefficient.obj t).I)
        (lifted_zero.{u} j (Fin.last T.necklace.dimension) (Fin.le_last j))).mpr
          (joints_all_flags T t j hj)
      right := (congrArg (fun k : ULift.{u} (Fin (T.necklace.dimension + 1)) =>
        k ∈ (T.coefficient.obj t).I)
        (lifted_last.{u} j (Fin.last T.necklace.dimension) (Fin.le_last j))).mpr
          (T.coefficient.obj t).right
      left_le i _ := Fin.zero_le i.down
      le_right i _ := Fin.le_last i.down }
  map f := ⟨homOfLE (fun i hi => (T.coefficient.map f).hom.down.down hi)⟩

/-- Every whole original prefix flag has its literal complete preimage formula. -/
theorem leftCoefficient_flags (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) (t : Fin (q.unop.len + 1)) :
    ((leftCoefficient T j hj).obj t).I =
      liftedEmbedding 0 j (Fin.zero_le j) ⁻¹' (T.coefficient.obj t).I := rfl

/-- Every whole original suffix flag has its literal complete preimage formula. -/
theorem rightCoefficient_flags (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) (t : Fin (q.unop.len + 1)) :
    ((rightCoefficient T j hj).obj t).I =
      liftedEmbedding j (Fin.last T.necklace.dimension) (Fin.le_last j) ⁻¹' (T.coefficient.obj t).I := rfl

/-- The entire original prefix cut with its SAME complete input and intermediate original label. -/
abbrev leftObject (T : Object K x y q) (j : Fin (T.necklace.dimension + 1)) (hj : j ∈ T.necklace.joints) :
    Object K x (inputVertex T j) q where
  necklace := Cut.leftData T.necklace j hj
  input := Cut.leftMap T.necklace j hj ≫ T.input
  source_eq := by
    rw [← Category.assoc, Cut.leftMap_source]
    exact T.source_eq
  target_eq := by
    rw [← Category.assoc, Cut.leftMap_target]
    rfl
  coefficient := leftCoefficient T j hj
  joints i hi := T.joints (Cut.leftEmbedding T.necklace j i)
    ((Cut.mem_leftJoints T.necklace j i).mp hi)

/-- The entire original suffix cut with that SAME original intermediate label and complete input. -/
abbrev rightObject (T : Object K x y q) (j : Fin (T.necklace.dimension + 1)) (hj : j ∈ T.necklace.joints) :
    Object K (inputVertex T j) y q where
  necklace := Cut.rightData T.necklace j hj
  input := Cut.rightMap T.necklace j hj ≫ T.input
  source_eq := by
    rw [← Category.assoc, Cut.rightMap_source]
    rfl
  target_eq := by
    rw [← Category.assoc, Cut.rightMap_target]
    exact T.target_eq
  coefficient := rightCoefficient T j hj
  joints i hi := T.joints (Cut.rightEmbedding T.necklace j i)
    ((Cut.mem_rightJoints T.necklace j i).mp hi)

/-- Every genuinely flanked original input retains the SAME genuine full prefix flanking. -/
theorem leftObject_isFlanked (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) (hT : IsFlanked T) : IsFlanked (leftObject T j hj) := by
  constructor
  · intro i
    exact (hT.1 (Cut.leftEmbedding T.necklace j i)).trans (Cut.mem_leftJoints T.necklace j i).symm
  · change ((leftCoefficient T j hj).obj (Fin.last q.unop.len)).I = Set.univ
    rw [leftCoefficient_flags, hT.2, Set.preimage_univ]

/-- Every genuinely flanked original input retains the SAME genuine full suffix flanking. -/
theorem rightObject_isFlanked (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) (hT : IsFlanked T) : IsFlanked (rightObject T j hj) := by
  constructor
  · intro i
    exact (hT.1 (Cut.rightEmbedding T.necklace j i)).trans (Cut.mem_rightJoints T.necklace j i).symm
  · change ((rightCoefficient T j hj).obj (Fin.last q.unop.len)).I = Set.univ
    rw [rightCoefficient_flags, hT.2, Set.preimage_univ]

/-- Both SAME whole original cut input maps are literal restrictions of the original input. -/
theorem leftObject_input (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) :
    (leftObject T j hj).input = Cut.leftMap T.necklace j hj ≫ T.input := rfl

/-- The same entire original suffix input is its literal native restriction. -/
theorem rightObject_input (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) :
    (rightObject T j hj).input = Cut.rightMap T.necklace j hj ≫ T.input := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.CutObjects
