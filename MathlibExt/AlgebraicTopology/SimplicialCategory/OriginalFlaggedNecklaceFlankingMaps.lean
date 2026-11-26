/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceFlanking
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentFlagSupportOperators

/-!
# Actual original flanking maps

Every original flagged-necklace map restricts to the same computed first
and last flags. The whole native inclusion square, original input square,
and every complete coefficient flag commute.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Flanking

open OriginalBead.TerminalFlag
open SSet.OriginalNecklace

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
variable {T U : Object K x y q}

/-- The same original operator restricted to its actual selected original supports. -/
def selectedOperator (f : T ⟶ U) : ⦋(data T).dimension⦌ ⟶ ⦋(data U).dimension⦌ :=
  Operators.operator f.necklaceMap.operator f.necklaceMap.source f.necklaceMap.target
    T.coefficient U.coefficient f.flags

/-- The actual selected source equation of the same original map. -/
theorem selected_source (f : T ⟶ U) : (selectedOperator f).toOrderHom 0 = 0 :=
  Operators.vertexMap_zero f.necklaceMap.operator f.necklaceMap.source f.necklaceMap.target
    T.coefficient U.coefficient f.flags

/-- The actual selected target equation of the same original map. -/
theorem selected_target (f : T ⟶ U) :
    (selectedOperator f).toOrderHom (Fin.last (data T).dimension) = Fin.last (data U).dimension :=
  Operators.vertexMap_last f.necklaceMap.operator f.necklaceMap.source f.necklaceMap.target
    T.coefficient U.coefficient f.flags

/-- Every actual selected target joint is an image of an actual selected source joint. -/
theorem selected_joint_preimage (f : T ⟶ U) (j : Fin ((data U).dimension + 1))
    (hj : j ∈ (data U).joints) :
    ∃ i ∈ (data T).joints, (selectedOperator f).toOrderHom i = j := by
  have hr : ULift.up.{u} j ∈ ((object U).coefficient.obj 0).I :=
    (object_isFlanked U).1 j |>.mpr hj
  have hmem : ULift.up.{u} j ∈
      (selectedOperator f).toOrderHom.uliftMap '' ((object T).coefficient.obj 0).I := by
    have he := Operators.selected_flags_image f.necklaceMap.operator
      f.necklaceMap.source f.necklaceMap.target T.coefficient U.coefficient f.flags 0
    exact Eq.mpr (congrArg (fun S => ULift.up.{u} j ∈ S) he) hr
  obtain ⟨i, hi, he⟩ := hmem
  exact ⟨i.down, (object_isFlanked T).1 i.down |>.mp hi, congrArg ULift.down he⟩

/-- The whole original map restricts to an actual map of the selected native necklaces. -/
def selectedMorphism (f : T ⟶ U) : Morphism (data T) (data U) where
  operator := selectedOperator f
  source := selected_source f
  target := selected_target f
  lands := by
    rintro ⟨⟨d⟩⟩ s hs
    exact map_mem_of_joints (selectedOperator f) (data T).joints (data U).joints
      (selected_joint_preimage f) s hs

/-- The entire native inclusion square retains the same original ordinal map. -/
theorem necklace_naturality (f : T ⟶ U) :
    selectedMorphism f ≫ necklaceInclusion U = necklaceInclusion T ≫ f.necklaceMap :=
  SSet.OriginalNecklace.Morphism.ext
    (Operators.operator_embedding f.necklaceMap.operator
      f.necklaceMap.source f.necklaceMap.target T.coefficient U.coefficient f.flags).symm

/-- The whole original native simplicial inclusion square commutes. -/
theorem inclusion_map_naturality (f : T ⟶ U) :
    (selectedMorphism f).map.{u} ≫ (necklaceInclusion U).map =
      (necklaceInclusion T).map ≫ f.necklaceMap.map := by
  have h := congrArg (fun a : Morphism (data T) U.necklace => a.map.{u})
    (necklace_naturality f)
  exact (SSet.OriginalNecklace.Morphism.map_comp (selectedMorphism f)
    (necklaceInclusion U)).symm.trans
      (h.trans (SSet.OriginalNecklace.Morphism.map_comp (necklaceInclusion T) f.necklaceMap))

/-- The same entire original input is retained by the selected actual native map. -/
theorem input_naturality (f : T ⟶ U) :
    (selectedMorphism f).map.{u} ≫ (object U).input = (object T).input := by
  change (selectedMorphism f).map.{u} ≫ ((necklaceInclusion U).map ≫ U.input) =
    (necklaceInclusion T).map ≫ T.input
  exact (Category.assoc (selectedMorphism f).map (necklaceInclusion U).map U.input).symm.trans
    ((congrArg (fun a => a ≫ U.input) (inclusion_map_naturality f)).trans
      ((Category.assoc (necklaceInclusion T).map f.necklaceMap.map U.input).trans
        (congrArg (fun a => (necklaceInclusion T).map ≫ a) f.over)))

/-- The same original flanking map over the full original input and all complete coefficient flags. -/
def map (f : T ⟶ U) : object T ⟶ object U where
  necklaceMap := selectedMorphism f
  over := input_naturality f
  flags := Operators.coefficient_map f.necklaceMap.operator
    f.necklaceMap.source f.necklaceMap.target T.coefficient U.coefficient f.flags

/-- The full original flagged inclusion square commutes, retaining all original input and flag data. -/
theorem inclusion_naturality (f : T ⟶ U) :
    map f ≫ inclusion U = inclusion T ≫ f :=
  Hom.ext (necklace_naturality f)

/-- The whole original selected coefficient map retains every actual original scalar flag image. -/
theorem map_flags (f : T ⟶ U) (t : Fin (q.unop.len + 1)) :
    (selectedOperator f).toOrderHom.uliftMap '' ((object T).coefficient.obj t).I =
      ((object U).coefficient.obj t).I :=
  Operators.selected_flags_image f.necklaceMap.operator f.necklaceMap.source
    f.necklaceMap.target T.coefficient U.coefficient f.flags t

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Flanking
