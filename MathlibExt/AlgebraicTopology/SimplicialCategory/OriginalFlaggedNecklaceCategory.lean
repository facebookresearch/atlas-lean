/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceCategory
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadOuterOperator

/-!
# The actual original fixed-scalar flagged-necklace category

Objects retain their whole native necklace map into the original input,
both original vertices, and every supplied coefficient flag. Morphisms
retain the same native necklace map over that input and the literal full
coefficient image equation.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBead.TerminalFlag
open SSet.OriginalNecklace

/-- A complete original necklace, its actual input map, and its whole scalar flag. -/
structure Object (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) where
  /-- The original complete native necklace. -/
  necklace : Data
  /-- The same original map of the whole necklace into the input. -/
  input : necklace.object.{u} ⟶ K
  /-- The source is the same original input vertex. -/
  source_eq : SSet.yonedaEquiv (necklace.source ≫ input) = x
  /-- The target is the same original input vertex. -/
  target_eq : SSet.yonedaEquiv (necklace.target ≫ input) = y
  /-- The complete original coefficient flag. -/
  coefficient : (coefficientObject.{u} necklace.dimension).obj q
  /-- Every original necklace joint belongs to the actual first flag. -/
  joints : ∀ j ∈ necklace.joints, ULift.up.{u} j ∈ (coefficient.obj 0).I

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- A genuine original flagged-necklace map over the same original input. -/
structure Hom (T U : Object K x y q) where
  /-- The same native original necklace map. -/
  necklaceMap : T.necklace ⟶ U.necklace
  /-- The entire original input maps commute. -/
  over : necklaceMap.map.{u} ≫ U.input = T.input
  /-- Every original coefficient flag has its exact original direct image. -/
  flags : (OriginalBead.OuterOperator.map necklaceMap.operator
    necklaceMap.source necklaceMap.target).app q T.coefficient = U.coefficient

namespace Hom

/-- The whole original flagged map is determined by the same native necklace map. -/
@[ext]
theorem ext {T U : Object K x y q} {f g : Hom T U}
    (h : f.necklaceMap = g.necklaceMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The actual original identity on the whole flagged necklace. -/
def id (T : Object K x y q) : Hom T T where
  necklaceMap := 𝟙 T.necklace
  over := by
    change (SSet.OriginalNecklace.Morphism.id T.necklace).map.{u} ≫ T.input = T.input
    rw [SSet.OriginalNecklace.Morphism.map_id, Category.id_comp]
  flags := by
    have h := ConcreteCategory.congr_hom
      (congr_app (OriginalBead.OuterOperator.map_id.{u} T.necklace.dimension) q)
      T.coefficient
    exact h

/-- Composition retains both whole original input maps and every original flag. -/
def comp {T U V : Object K x y q} (f : Hom T U) (g : Hom U V) : Hom T V where
  necklaceMap := f.necklaceMap ≫ g.necklaceMap
  over := by
    change (SSet.OriginalNecklace.Morphism.comp f.necklaceMap g.necklaceMap).map.{u} ≫
      V.input = T.input
    rw [SSet.OriginalNecklace.Morphism.map_comp, Category.assoc, g.over, f.over]
  flags := by
    have h := ConcreteCategory.congr_hom
      (congr_app (OriginalBead.OuterOperator.map_comp f.necklaceMap.operator
        g.necklaceMap.operator f.necklaceMap.source f.necklaceMap.target
        g.necklaceMap.source g.necklaceMap.target) q) T.coefficient
    exact h.trans ((congrArg
      ((OriginalBead.OuterOperator.map g.necklaceMap.operator
        g.necklaceMap.source g.necklaceMap.target).app q) f.flags).trans g.flags)

end Hom

/-- The genuine complete category of original flagged necklaces at one scalar degree. -/
instance : Category (Object K x y q) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (Category.id_comp f.necklaceMap)
  comp_id f := Hom.ext (Category.comp_id f.necklaceMap)
  assoc f g h := Hom.ext (Category.assoc f.necklaceMap g.necklaceMap h.necklaceMap)

/-- Forget only the supplied input map and flag, retaining the same native necklace. -/
def forget (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Object K x y q ⥤ Data where
  obj := Object.necklace
  map := Hom.necklaceMap

/-- The complete original native necklace diagram at the supplied scalar degree. -/
def diagram (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Object K x y q ⥤ SSet.{u} :=
  forget K x y q ⋙ SSet.OriginalNecklace.functor

/-- The entire original input maps form an actual natural transformation on the complete diagram. -/
def inputTransformation (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    diagram K x y q ⟶ (CategoryTheory.Functor.const (Object K x y q)).obj K where
  app := Object.input
  naturality T U f := by
    change f.necklaceMap.map.{u} ≫ U.input = T.input ≫ 𝟙 K
    exact f.over.trans (Category.comp_id T.input).symm

/-- The same entire native input map is the component at the original flagged object. -/
theorem inputTransformation_app (T : Object K x y q) :
    (inputTransformation K x y q).app T = T.input := rfl

/-- The actual first flag contains every joint in every later original flag. -/
theorem joints_all_flags (T : Object K x y q) (t : Fin (q.unop.len + 1))
    (j : Fin (T.necklace.dimension + 1)) (hj : j ∈ T.necklace.joints) :
    ULift.up.{u} j ∈ (T.coefficient.obj t).I :=
  (T.coefficient.map (homOfLE (Fin.zero_le t))).hom.down.down (T.joints j hj)

/-- A flanked original flag has exactly its actual joints first and all its actual vertices last. -/
def IsFlanked (T : Object K x y q) : Prop :=
  (∀ j : Fin (T.necklace.dimension + 1),
    ULift.up.{u} j ∈ (T.coefficient.obj 0).I ↔ j ∈ T.necklace.joints) ∧
      (T.coefficient.obj (Fin.last q.unop.len)).I = Set.univ

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
