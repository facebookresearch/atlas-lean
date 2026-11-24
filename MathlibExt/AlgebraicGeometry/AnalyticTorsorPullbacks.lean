/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticGroupTorsorSites
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Actual restriction of analytic torsor actions and their fibres

The underlying sheaf and every action component are native restriction
along Over.map f. The group presheaf is definitionally unchanged on
each actual test space. Torsor preservation is a conclusion about this
computed action functor; it is not built into the definition of a
torsor. Its groupoid pullback is the native full-subcategory lift/core.
The fibre is the native costructured-arrow groupoid, retaining the
actual pullback isomorphism to the specified target torsor.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.1 and VI.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticTorsorPullbacks

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open AnalyticGroupTorsorSites
open MathlibExt.CategoryTheory.SheafTorsorGroupoids

variable (p : ℕ) [Fact p.Prime] (E : Type) [CommRing E]
  (G : Over (Spec (.of E))) [GrpObj G]
  {X Y : ESpace p E} (f : Y ⟶ X)
  (HX : GroupDescent p E G X) (HY : GroupDescent p E G Y)

def pullbackSetSheaves : Sheaf (topology p E X) (Type 0) ⥤
    Sheaf (topology p E Y) (Type 0) :=
  (ambientTopology p E).overMapPullback (Type 0) f

def actionPullback : Action (topology p E X) (groupSheaf p E G X HX) ⥤
    Action (topology p E Y) (groupSheaf p E G Y HY) where
  obj P :=
    { sheaf := (pullbackSetSheaves p E f).obj P.sheaf
      action := Functor.whiskerLeft (pullbackSite p E f).op P.action
      unit := fun T z ↦ P.unit ((pullbackSite p E f).op.obj T) z
      associative := fun T z a b ↦ P.associative ((pullbackSite p E f).op.obj T) z a b }
  map {_P _Q} e :=
    ⟨(pullbackSetSheaves p E f).map e.val, fun T z a ↦
      e.property ((pullbackSite p E f).op.obj T) z a⟩
  map_id P := Subtype.ext ((pullbackSetSheaves p E f).map_id P.sheaf)
  map_comp e h := Subtype.ext ((pullbackSetSheaves p E f).map_comp e.val h.val)

def PreservesTorsors : Prop :=
  ∀ P : Action (topology p E X) (groupSheaf p E G X HX),
    IsTorsor (topology p E X) (groupSheaf p E G X HX) P →
      IsTorsor (topology p E Y) (groupSheaf p E G Y HY)
        ((actionPullback p E G f HX HY).obj P)

/-- The groupoid functor is computed from actual restriction and the native core. -/
def torsorPullback (H : PreservesTorsors p E G f HX HY) :
    Torsors p E G X HX ⥤ Torsors p E G Y HY :=
  (ObjectProperty.lift
    (show ObjectProperty (Action (topology p E Y) (groupSheaf p E G Y HY)) from
      IsTorsor (topology p E Y) (groupSheaf p E G Y HY))
    ((show ObjectProperty (Action (topology p E X) (groupSheaf p E G X HX)) from
        IsTorsor (topology p E X) (groupSheaf p E G X HX)).ι ⋙
      actionPullback p E G f HX HY)
    (fun P ↦ H P.obj P.property)).core

/-- Objects are actual source torsors with an isomorphism of their actual pullback to P. -/
abbrev Fibre (H : PreservesTorsors p E G f HX HY) (P : Torsors p E G Y HY) :=
  CostructuredArrow (torsorPullback p E G f HX HY H) P

end MathlibExt.AlgebraicGeometry.AnalyticTorsorPullbacks
