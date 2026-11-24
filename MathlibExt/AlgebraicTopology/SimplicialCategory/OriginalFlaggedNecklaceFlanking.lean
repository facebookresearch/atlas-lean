/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceCategory

/-!
# Actual original flagged-necklace flanking

The same original last flag gives the full selected vertices, and the
same first flag gives precisely the selected joints. The native selected
necklace includes into the original necklace over the entire same input.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Flanking

open OriginalBead.TerminalFlag
open SSet.OriginalNecklace

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The actual selected joints are exactly the original first-flag preimages. -/
def joints (T : Object K x y q) : Finset (Fin (dimension T.coefficient + 1)) := by
  classical
  exact Finset.univ.filter
    (fun i => ULift.up.{u} (embedding T.coefficient i) ∈ (T.coefficient.obj 0).I)

/-- Selected joint membership retains the whole same original first flag. -/
theorem mem_joints (T : Object K x y q) (i : Fin (dimension T.coefficient + 1)) :
    i ∈ joints T ↔
      ULift.up.{u} (embedding T.coefficient i) ∈ (T.coefficient.obj 0).I := by
  classical
  simp only [joints, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The same original initial vertex remains a selected joint. -/
theorem zero_joint (T : Object K x y q) : (0 : Fin (dimension T.coefficient + 1)) ∈ joints T := by
  apply (mem_joints T 0).mpr
  rw [embedding_zero]
  exact (T.coefficient.obj 0).left

/-- The same original terminal vertex remains a selected joint. -/
theorem last_joint (T : Object K x y q) : Fin.last (dimension T.coefficient) ∈ joints T := by
  apply (mem_joints T _).mpr
  rw [embedding_last]
  exact (T.coefficient.obj 0).right

/-- The actual original necklace with exactly the supplied first-flag joints and last-flag vertices. -/
def data (T : Object K x y q) : Data where
  dimension := dimension T.coefficient
  joints := joints T
  source_joint := zero_joint T
  target_joint := last_joint T

/-- Every original necklace joint has its actual selected first-flag preimage. -/
theorem original_joint_preimage (T : Object K x y q)
    (j : Fin (T.necklace.dimension + 1)) (hj : j ∈ T.necklace.joints) :
    ∃ i ∈ joints T, embedding T.coefficient i = j := by
  have hf := T.joints j hj
  have hs : j ∈ support T.coefficient :=
    (mem_support T.coefficient j).mpr (flag_subset_last T.coefficient 0 hf)
  have hr : j ∈ Set.range (embedding T.coefficient) := by
    rw [range_embedding]
    exact hs
  obtain ⟨i, hi⟩ := hr
  refine ⟨i, (mem_joints T i).mpr ?_, hi⟩
  exact congrArg (fun k => ULift.up.{u} k ∈ (T.coefficient.obj 0).I) hi ▸ hf

/-- The literal native inclusion of the actual selected necklace into the same original necklace. -/
def necklaceInclusion (T : Object K x y q) : Morphism (data T) T.necklace where
  operator := operator T.coefficient
  source := embedding_zero T.coefficient
  target := embedding_last T.coefficient
  lands := by
    rintro ⟨⟨d⟩⟩ s hs
    exact map_mem_of_joints (operator T.coefficient) (joints T) T.necklace.joints
      (original_joint_preimage T) s hs

/-- The complete same original input restricted along its actual selected native necklace. -/
def object (T : Object K x y q) : Object K x y q where
  necklace := data T
  input := (necklaceInclusion T).map.{u} ≫ T.input
  source_eq := by
    have h : (data T).source.{u} ≫ ((necklaceInclusion T).map ≫ T.input) =
        T.necklace.source ≫ T.input :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ T.input) (source_map (necklaceInclusion T)))
    exact (congrArg SSet.yonedaEquiv h).trans T.source_eq
  target_eq := by
    have h : (data T).target.{u} ≫ ((necklaceInclusion T).map ≫ T.input) =
        T.necklace.target ≫ T.input :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ T.input) (target_map (necklaceInclusion T)))
    exact (congrArg SSet.yonedaEquiv h).trans T.target_eq
  coefficient := coefficient T.coefficient
  joints := fun i hi => (mem_joints T i).mp hi

/-- The actual selected necklace is flanked by its exact original first and last flags. -/
theorem object_isFlanked (T : Object K x y q) : IsFlanked (object T) :=
  ⟨fun i => (mem_joints T i).symm, coefficient_last_full T.coefficient⟩

/-- The same whole original selected coefficient image is its native endpoint-preserving outer map. -/
theorem inclusion_coefficientMap (T : Object K x y q) :
    OriginalBead.OuterOperator.map.{u} (necklaceInclusion T).operator
      (necklaceInclusion T).source (necklaceInclusion T).target =
      imageMap T.coefficient := rfl

/-- The complete original flanking inclusion is an actual flagged map over the same entire input. -/
def inclusion (T : Object K x y q) : object T ⟶ T where
  necklaceMap := necklaceInclusion T
  over := rfl
  flags := by
    have h := ConcreteCategory.congr_hom (congr_app (inclusion_coefficientMap T) q)
      (coefficient T.coefficient)
    exact h.trans (image_coefficient T.coefficient)

/-- The full original flanking inclusion retains its same native ordinal operator. -/
theorem inclusion_operator (T : Object K x y q) :
    (inclusion T).necklaceMap.operator = operator T.coefficient := rfl

/-- The full original selected input map is literally the original input restricted along this inclusion. -/
theorem object_input (T : Object K x y q) :
    (object T).input = (necklaceInclusion T).map.{u} ≫ T.input := rfl

/-- Every actual selected flag is the entire original supplied flag preimage. -/
theorem object_flags (T : Object K x y q) (t : Fin (q.unop.len + 1)) :
    ((object T).coefficient.obj t).I =
      (liftedEmbedding T.coefficient) ⁻¹' (T.coefficient.obj t).I :=
  coefficient_flags T.coefficient t

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Flanking
