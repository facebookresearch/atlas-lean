/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogStructures

/-!
# Actual log characteristic maps and site-point generizations

Fixed-ring log arrows preserve the forced unit inclusion, so their
characteristic map is the actual map of the defining pushouts. Geometric
generization is induced from a natural map of the native point fibre
functors via the actual colimit cocone. Neither map is a ghost oracle.
These completed operations support basic log-map comparisons.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RingedSiteLogMorphisms
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.LogStructures
universe u v w
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {O : RingSheaf J}

abbrev monoidMap {L M : LogStructure J O} (f : L ⟶ M) : monoid J L ⟶ monoid J M :=
  f.hom.left

lemma unit_naturality {L M : LogStructure J O} (f : L ⟶ M) :
    unitMap J L ≫ monoidMap J f = unitMap J M := by
  apply factorThroughUnits J M (unitMap J L ≫ monoidMap J f) (𝟙 _)
  rw [Category.assoc]
  change unitMap J L ≫ (f.hom.left ≫ M.obj.hom) = _
  rw [Over.w, unitMap_alpha]
  simp

/-- The actual map on characteristic pushouts. -/
def characteristicMap {L M : LogStructure J O} (f : L ⟶ M) :
    characteristic J L ⟶ characteristic J M :=
  pushout.map (unitMap J L) (terminal.from (units J O))
    (unitMap J M) (terminal.from (units J O))
    (monoidMap J f) (𝟙 _) (𝟙 _)
    (by simpa using unit_naturality J f)
    (by apply terminal.hom_ext)

/-- A natural map of actual point fibre functors induces the literal
colimit map on a presheaf fibre. -/
def pointGenerization {D : Type*} [Category D] [HasColimitsOfSize.{w,w} D]
    (p q : J.Point.{w}) (a : p.fiber ⟶ q.fiber) (P : Cᵒᵖ ⥤ D) :
    p.presheafFiber.obj P ⟶ q.presheafFiber.obj P :=
  p.presheafFiberDesc (fun U x => q.toPresheafFiber U (a.app U x) P)
    (by
      intro U V f x
      rw [q.toPresheafFiber_w]
      congr 1
      exact (NatTrans.naturality_apply a f x).symm)

end MathlibExt.AlgebraicGeometry.RingedSiteLogMorphisms
