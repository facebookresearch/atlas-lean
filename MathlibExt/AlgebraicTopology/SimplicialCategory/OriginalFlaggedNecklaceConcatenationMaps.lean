/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceConcatenationMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceConcatenationNondegenerate

/-!
# Actual original concatenation of full flagged maps

Both original flagged maps concatenate through the SAME native pushout.
The whole original input square and every complete original flag image
are retained, with both literal native map readbacks.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace
open OriginalBead.TerminalFlag (coefficientObject)

private instance {n : ℕ} (a b : SimplicialThickening.Path
    (ULift.up.{u} (0 : Fin (n + 1))) (ULift.up.{u} (Fin.last n))) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

private theorem concat_coefficient_maps {T T' U U' : Data} (f : T ⟶ T') (g : U ⟶ U')
    {q : SimplexCategoryᵒᵖ} (p : (coefficientObject.{u} T.dimension).obj q)
    (r : (coefficientObject.{u} U.dimension).obj q)
    (p' : (coefficientObject.{u} T'.dimension).obj q) (r' : (coefficientObject.{u} U'.dimension).obj q)
    (hp : (OriginalBead.OuterOperator.map f.operator f.source f.target).app q p = p')
    (hr : (OriginalBead.OuterOperator.map g.operator g.source g.target).app q r = r') :
    (OriginalBead.OuterOperator.map (concatMapMorphism.{u} f g).operator
      (concatMapMorphism.{u} f g).source (concatMapMorphism.{u} f g).target).app q
      (ConcatFlags.coefficient p r) = ConcatFlags.coefficient p' r' := by
  refine CategoryTheory.Functor.ext (fun t => ?_) ?_
  · apply SimplicialThickening.Path.ext
    have hP := congrArg (fun p : (coefficientObject.{u} T'.dimension).obj q => (p.obj t).I) hp
    have hR := congrArg (fun p : (coefficientObject.{u} U'.dimension).obj q => (p.obj t).I) hr
    change f.operator.toOrderHom.uliftMap '' (p.obj t).I = (p'.obj t).I at hP
    change g.operator.toOrderHom.uliftMap '' (r.obj t).I = (r'.obj t).I at hR
    have hleft : (concatMapMorphism.{u} f g).operator.toOrderHom.uliftMap ''
        (ConcatFlags.prefixLift T.dimension U.dimension '' (p.obj t).I) =
      ConcatFlags.prefixLift T'.dimension U'.dimension '' (p'.obj t).I := by
      rw [Set.image_image, ← hP, Set.image_image]
      congr 1
      funext i
      apply ULift.ext
      exact concatMapMorphism_prefix.{u} f g i.down
    have hright : (concatMapMorphism.{u} f g).operator.toOrderHom.uliftMap ''
        (ConcatFlags.suffixLift T.dimension U.dimension '' (r.obj t).I) =
      ConcatFlags.suffixLift T'.dimension U'.dimension '' (r'.obj t).I := by
      rw [Set.image_image, ← hR, Set.image_image]
      congr 1
      funext i
      apply ULift.ext
      exact concatMapMorphism_suffix.{u} f g i.down
    change (concatMapMorphism.{u} f g).operator.toOrderHom.uliftMap ''
      (ConcatFlags.prefixLift T.dimension U.dimension '' (p.obj t).I ∪
        ConcatFlags.suffixLift T.dimension U.dimension '' (r.obj t).I) =
      ConcatFlags.prefixLift T'.dimension U'.dimension '' (p'.obj t).I ∪
        ConcatFlags.suffixLift T'.dimension U'.dimension '' (r'.obj t).I
    rw [Set.image_union, hleft, hright]
  · intro i j h
    exact Subsingleton.elim _ _

variable {K : SSet.{u}} {x y z : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- Both complete original input maps commute under their SAME actual native concatenation. -/
theorem concatHom_over {T T' : Object K x y q} {U U' : Object K y z q}
    (f : T ⟶ T') (g : U ⟶ U') :
    concatMap f.necklaceMap g.necklaceMap ≫ (concat T' U').input = (concat T U).input := by
  apply (concat_isPushout T.necklace U.necklace).hom_ext
  · rw [← Category.assoc, concatLeft_map, Category.assoc, concatLeft_input,
      f.over, concatLeft_input]
  · rw [← Category.assoc, concatRight_map, Category.assoc, concatRight_input,
      g.over, concatRight_input]

/-- The SAME actual concatenation of both whole original flagged morphisms. -/
def concatHom {T T' : Object K x y q} {U U' : Object K y z q}
    (f : T ⟶ T') (g : U ⟶ U') : concat T U ⟶ concat T' U' where
  necklaceMap := concatMapMorphism.{u} f.necklaceMap g.necklaceMap
  over := (congrArg (fun m => m ≫ (concat T' U').input)
    (concatMapMorphism_map f.necklaceMap g.necklaceMap)).trans (concatHom_over f g)
  flags := concat_coefficient_maps f.necklaceMap g.necklaceMap T.coefficient U.coefficient
    T'.coefficient U'.coefficient f.flags g.flags

/-- The original full flagged map reads precisely its SAME native concatenation. -/
theorem concatHom_map {T T' : Object K x y q} {U U' : Object K y z q}
    (f : T ⟶ T') (g : U ⟶ U') :
    (concatHom f g).necklaceMap.map.{u} = concatMap f.necklaceMap g.necklaceMap :=
  concatMapMorphism_map _ _

/-- The whole original first source map is retained by the actual flagged concatenation. -/
theorem concatHom_prefix_map {T T' : Object K x y q} {U U' : Object K y z q}
    (f : T ⟶ T') (g : U ⟶ U') :
    concatLeft T.necklace U.necklace ≫ (concatHom f g).necklaceMap.map.{u} =
      f.necklaceMap.map ≫ concatLeft T'.necklace U'.necklace := by
  rw [concatHom_map, concatLeft_map]

/-- The whole original second source map is retained by the actual flagged concatenation. -/
theorem concatHom_suffix_map {T T' : Object K x y q} {U U' : Object K y z q}
    (f : T ⟶ T') (g : U ⟶ U') :
    concatRight T.necklace U.necklace ≫ (concatHom f g).necklaceMap.map.{u} =
      g.necklaceMap.map ≫ concatRight T'.necklace U'.necklace := by
  rw [concatHom_map, concatRight_map]

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
