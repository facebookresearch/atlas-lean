/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceAllMaps
import Mathlib.CategoryTheory.Category.Cat

/-!
# The whole original scalar flagged-necklace diagram

Every original face and degeneracy acts on the complete original flags.
The original necklace, entire input map and endpoints are retained.
Actual identities and compositions give the full simplicial category
diagram and its original bisimplicial nerve.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBead.TerminalFlag

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q r s : SimplexCategoryᵒᵖ}

/-- The entire original flag under the same original scalar operator. -/
def scalarObject (θ : q ⟶ r) (T : Object K x y q) : Object K x y r where
  necklace := T.necklace
  input := T.input
  source_eq := T.source_eq
  target_eq := T.target_eq
  coefficient := (coefficientObject T.necklace.dimension).map θ T.coefficient
  joints j hj :=
    (T.coefficient.map
      (homOfLE (Fin.zero_le (θ.unop.toOrderHom (0 : Fin (r.unop.len + 1)))))).hom.down.down
        (T.joints j hj)

/-- The same entire native flagged map follows every original face and degeneracy. -/
def scalarHom (θ : q ⟶ r) {T U : Object K x y q} (f : T ⟶ U) :
    scalarObject θ T ⟶ scalarObject θ U where
  necklaceMap := f.necklaceMap
  over := f.over
  flags :=
    (OriginalBead.OuterOperator.map_inner f.necklaceMap.operator f.necklaceMap.source
      f.necklaceMap.target θ T.coefficient).symm.trans
        (congrArg ((coefficientObject U.necklace.dimension).map θ) f.flags)

/-- The actual whole scalar functor on original flagged necklaces. -/
def scalarFunctor (K : SSet.{u}) (x y : K _⦋0⦌) {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    Object K x y q ⥤ Object K x y r where
  obj := scalarObject θ
  map := scalarHom θ
  map_id _T := Hom.ext rfl
  map_comp _f _g := Hom.ext rfl

/-- The actual original scalar identity retains the complete original category. -/
theorem scalarFunctor_id (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    scalarFunctor K x y (𝟙 q) = 𝟭 (Object K x y q) := rfl

/-- The actual original scalar composition retains every complete original flag. -/
theorem scalarFunctor_comp (K : SSet.{u}) (x y : K _⦋0⦌)
    {q r s : SimplexCategoryᵒᵖ} (θ : q ⟶ r) (ψ : r ⟶ s) :
    scalarFunctor K x y (θ ≫ ψ) = scalarFunctor K x y θ ⋙ scalarFunctor K x y ψ := rfl

/-- The complete original simplicial diagram of flagged-necklace categories. -/
def scalarCategoryDiagram (K : SSet.{u}) (x y : K _⦋0⦌) :
    SimplicialObject Cat.{0, u} where
  obj q := Cat.of (Object K x y q)
  map θ := (scalarFunctor K x y θ).toCatHom
  map_id q := Cat.ext (scalarFunctor_id K x y q)
  map_comp θ ψ := Cat.ext (scalarFunctor_comp K x y θ ψ)

/-- The actual complete bisimplicial nerve of the whole original flagged diagram. -/
def scalarNerveDiagram (K : SSet.{u}) (x y : K _⦋0⦌) :
    SimplicialObject SSet.{u} :=
  scalarCategoryDiagram K x y ⋙ CategoryTheory.nerveFunctor

/-- The scalar diagram retains the same complete native necklace. -/
theorem scalarFunctor_obj_necklace (θ : q ⟶ r) (T : Object K x y q) :
    ((scalarFunctor K x y θ).obj T).necklace = T.necklace := rfl

/-- The scalar diagram retains the entire same original input map. -/
theorem scalarFunctor_obj_input (θ : q ⟶ r) (T : Object K x y q) :
    ((scalarFunctor K x y θ).obj T).input = T.input := rfl

/-- The scalar diagram acts on the complete original coefficient by the same original operator. -/
theorem scalarFunctor_obj_coefficient (θ : q ⟶ r) (T : Object K x y q) :
    ((scalarFunctor K x y θ).obj T).coefficient =
      (coefficientObject T.necklace.dimension).map θ T.coefficient := rfl

/-- The scalar diagram retains the same original whole native morphism. -/
theorem scalarFunctor_map_necklace (θ : q ⟶ r) {T U : Object K x y q} (f : T ⟶ U) :
    ((scalarFunctor K x y θ).map f).necklaceMap = f.necklaceMap := rfl

/-- The original nerve diagram object is the full original flagged-category nerve. -/
theorem scalarNerveDiagram_obj (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    (scalarNerveDiagram K x y).obj q = nerve (Object K x y q) := rfl

/-- The original nerve diagram map is the nerve of the same complete original scalar functor. -/
theorem scalarNerveDiagram_map (θ : q ⟶ r) :
    (scalarNerveDiagram K x y).map θ = nerveMap (scalarFunctor K x y θ) := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
