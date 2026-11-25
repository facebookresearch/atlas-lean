/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.OriginalSliceFilteredUnion

set_option autoImplicit false
noncomputable section

universe w t uD vD uC vC uI vI

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open CategoryTheory.SmallObject.DiagramSliceExhaustion
open CategoryTheory.SmallObject.DiagramActionCapture
open CategoryTheory.SmallObject.OriginalSliceFilteredUnion

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  {theta : PointwiseCellTreePresentation (s := s) f P}
  {L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram}

-- Arbitrary roots and label carriers: no compactness or ambient colimit assumptions.
example : IsInitial (Under.mk (empty (theta := theta) (L := L)).root) :=
  emptyIsInitial

example : (empty (theta := theta) (L := L)).toFunctor ≅ F := emptyFunctorIso

example : (empty (theta := theta) (L := L)).root ≫
    (empty (theta := theta) (L := L)).target = f := OriginalSlice.factor _

variable {I : Type uI} [Category.{vI} I] [IsFiltered I]
  (A : I → OriginalSlice theta L)
  (hA : ∀ {i j : I}, (i ⟶ j) → OriginalSlice.Inclusion (A i) (A j))

-- The same original chosen object and every original action are exposed.
example (d : D) : (union A hA).toFunctor.obj d =
    ((L d).obj (⨆ i, (A i).supports d)).right := rfl

example : IsColimit (cocone A hA) := isColimit A hA

example (d : D) : IsColimit (componentCocone A hA d) := componentIsColimit A hA d

example {d e : D} (g : d ⟶ e) (i : I) :
    ((L d).map ((inclusion A hA i).le d)).right ≫ (union A hA).map g =
      (A i).map g ≫ ((L e).map ((inclusion A hA i).le e)).right :=
  (inclusion A hA i).naturality g

example (i : I) : (A i).root ≫ (inclusion A hA i).toNatTrans = (union A hA).root :=
  inclusion_root (inclusion A hA i)

example (i : I) : (inclusion A hA i).toNatTrans ≫ (union A hA).target = (A i).target :=
  inclusion_target (inclusion A hA i)

example : (union A hA).root ≫ (union A hA).target = f := factor A hA

variable {J : Type uI} [LinearOrder J] (B : J → OriginalSlice theta L) (hB : Compatible B)

-- BEFORE is proved colimiting from the actual component lower UPs, including empty J.
example : IsColimit (familyBeforeCocone B hB) := familyBeforeIsColimit B hB

example (d : D) : IsColimit (familyComponentCocone B hB d) :=
  familyComponentIsColimit B hB d

example (d : D) : (familyBefore B).supports d = ⨆ j, (B j).supports d :=
  familyBefore_support B hB d

example [IsEmpty J] (d : D) : (familyBefore B).supports d = ⊥ := by
  rw [familyBefore_support B hB d]
  exact iSup_of_empty _

example (j : J) : (B j).root ≫ (familyBeforeInclusion B hB j).toNatTrans =
    (familyBefore B).root := inclusion_root (familyBeforeInclusion B hB j)
