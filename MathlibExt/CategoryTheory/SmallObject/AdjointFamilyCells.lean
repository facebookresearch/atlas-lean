/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w t s uC vC uD vD

open CategoryTheory

namespace HomotopicalAlgebra.RelativeCellComplex

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {S : Type s} (L : S → C ⥤ D) (P : MorphismProperty C)
  {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  {X Y : D} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w}
    (fun (_ : T) => (MorphismProperty.adjointFamilyGenerators L P).homFamily) f)

/-- Replace only the cell-family labels by their actual free-image preimages. -/
def adjointFamilyCellTypes :
    RelativeCellComplex.{w}
      (fun (_ : T) (q : S × P.toSet) => (L q.1).map q.2.1.hom) f := by
  let witness (p : (MorphismProperty.adjointFamilyGenerators L P).toSet) :
      ∃ q : S × P.toSet, Arrow.mk p.1.hom = Arrow.mk ((L q.1).map q.2.1.hom) :=
    (MorphismProperty.adjointFamilyGenerators_iff L P p.1.hom).mp p.2
  let q (p : (MorphismProperty.adjointFamilyGenerators L P).toSet) : S × P.toSet :=
    (witness p).choose
  let e (p : (MorphismProperty.adjointFamilyGenerators L P).toSet) :
      Arrow.mk p.1.hom ≅ Arrow.mk ((L (q p).1).map (q p).2.1.hom) :=
    eqToIso (witness p).choose_spec
  exact
    { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
      attachCells := fun j hj =>
        (c.attachCells j hj).reindexCellTypes
          (fun q : S × P.toSet => (L q.1).map q.2.1.hom) q e }

/-- Actual free-image normalization retains the entire original chain. -/
theorem adjointFamilyCellTypes_F : (adjointFamilyCellTypes L P c).F = c.F := rfl

/-- Actual free-image normalization retains the original endpoint inclusions. -/
theorem adjointFamilyCellTypes_incl (j : T) :
    (adjointFamilyCellTypes L P c).incl.app j = c.incl.app j := rfl

end HomotopicalAlgebra.RelativeCellComplex
