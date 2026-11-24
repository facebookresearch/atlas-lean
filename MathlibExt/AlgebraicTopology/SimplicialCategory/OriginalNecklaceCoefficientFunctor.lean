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
# The SAME whole original necklace coefficient functor

The complete original zero-to-last coherent coefficient follows every
native necklace operator by its SAME direct-image map. Actual identity
and composition laws give the original functor, retaining all ordinal
operators and both endpoint equations.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace
open OriginalBead.TerminalFlag (coefficientObject)

/-- The actual entire original coefficient functor on native original necklaces. -/
def coefficientFunctor : Data ⥤ SSet.{u} where
  obj T := coefficientObject T.dimension
  map f := OriginalBead.OuterOperator.map f.operator f.source f.target
  map_id T := by
    change OriginalBead.OuterOperator.map (𝟙 ⦋T.dimension⦌) rfl rfl = _
    exact OriginalBead.OuterOperator.map_id T.dimension
  map_comp f g := by
    change OriginalBead.OuterOperator.map (f.operator ≫ g.operator)
      ((congrArg g.operator.toOrderHom f.source).trans g.source)
      ((congrArg g.operator.toOrderHom f.target).trans g.target) = _
    exact OriginalBead.OuterOperator.map_comp f.operator g.operator f.source f.target g.source g.target

/-- Every actual original coefficient is the SAME complete zero-to-last original cube. -/
theorem coefficientFunctor_obj (T : Data) :
    coefficientFunctor.{u}.obj T = coefficientObject T.dimension := rfl

/-- Every actual original coefficient map is its SAME native direct image with both original endpoints. -/
theorem coefficientFunctor_map {T U : Data} (f : T ⟶ U) :
    coefficientFunctor.{u}.map f = OriginalBead.OuterOperator.map f.operator f.source f.target := rfl

/-- Every actual original coefficient flag reads back the SAME original vertex image. -/
theorem coefficientFunctor_flags {T U : Data} (f : T ⟶ U) {q : SimplexCategoryᵒᵖ}
    (p : (coefficientFunctor.{u}.obj T).obj q) (t : Fin (q.unop.len + 1)) :
    (((coefficientFunctor.{u}.map f).app q p).obj t).I =
      f.operator.toOrderHom.uliftMap '' (p.obj t).I := rfl

/-- The full original native necklace isomorphism induces its SAME entire coefficient isomorphism. -/
def coefficientIso {T U : Data} (e : T ≅ U) : coefficientObject.{u} T.dimension ≅ coefficientObject U.dimension :=
  coefficientFunctor.mapIso e

/-- Both SAME original full coefficient inverse maps retain the exact native forward morphism. -/
theorem coefficientIso_hom {T U : Data} (e : T ≅ U) :
    (coefficientIso.{u} e).hom = coefficientFunctor.map e.hom := rfl

/-- Both SAME original full coefficient inverse maps retain the exact native reverse morphism. -/
theorem coefficientIso_inv {T U : Data} (e : T ≅ U) :
    (coefficientIso.{u} e).inv = coefficientFunctor.map e.inv := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
