/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeLatchingMono
import Mathlib.CategoryTheory.Limits.Opposites

/-!
# Actual opposite matching arrows of the original right-cube resolution

The pinned limit/colimit duality identifies the actual opposite matching
object with the genuine original latching colimit. Its whole arrow is
the same latching map, retaining every original proper-face projection.
The opposite matching maps are therefore monomorphisms without a model
or fibrancy outcome hypothesis.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CoherentRealization.RightCubeOppositeMatching
open RightCubeLatchingMono

/-- The genuine whole original latching-to-opposite-matching limit isomorphism. -/
def matchingIso (n : ℕ) : colimit (RightCubeLatchingDiagram.diagram.{u} n) ≅
    unop (SimplicialObject.matchingObject RightCubeCosimplicial.diagram.{u}.op n) :=
  colimitLeftOpIsoUnopLimit (SimplicialObject.matchingDiagram RightCubeCosimplicial.diagram.{u}.op n)

/-- The actual opposite matching arrow is exactly the original latching arrow after the genuine
  limit/colimit identification. -/
theorem matching_factor (n : ℕ) : (matchingIso.{u} n).hom ≫
    (SimplicialObject.matchingMap RightCubeCosimplicial.diagram.{u}.op n).unop = latchingMap n := by
  apply colimit.hom_ext
  intro a
  let F := SimplicialObject.matchingDiagram RightCubeCosimplicial.diagram.{u}.op n
  have he := ι_comp_colimitLeftOpIsoUnopLimit_hom F a
  have hm : (SimplicialObject.matchingπ RightCubeCosimplicial.diagram.{u}.op n a.unop).unop ≫
      (SimplicialObject.matchingMap RightCubeCosimplicial.diagram.{u}.op n).unop =
        RightCubeCosimplicialMaps.map a.unop.obj.hom.unop :=
    congrArg Quiver.Hom.unop (SimplicialObject.matchingMap_π RightCubeCosimplicial.diagram.{u}.op n a.unop)
  exact (Category.assoc (colimit.ι (RightCubeLatchingDiagram.diagram.{u} n) a) (matchingIso.{u} n).hom
    (SimplicialObject.matchingMap RightCubeCosimplicial.diagram.{u}.op n).unop).symm.trans
      ((congrArg (fun f => f ≫ (SimplicialObject.matchingMap RightCubeCosimplicial.diagram.{u}.op n).unop) he).trans
        (hm.trans (colimit.ι_desc (ambient.{u} n) a).symm))

/-- Every actual opposite matching arrow of the same original right-cube diagram is a whole simplicial
  monomorphism, including degree zero. -/
theorem matching_unop_mono (n : ℕ) : Mono
    (SimplicialObject.matchingMap RightCubeCosimplicial.diagram.{u}.op n).unop := by
  let e := matchingIso.{u} n
  let m := (SimplicialObject.matchingMap RightCubeCosimplicial.diagram.{u}.op n).unop
  have he : e.inv ≫ latchingMap n = m :=
    (congrArg (fun f => e.inv ≫ f) (matching_factor.{u} n).symm).trans
      ((Category.assoc e.inv e.hom m).symm.trans
        ((congrArg (fun f => f ≫ m) e.inv_hom_id).trans (Category.id_comp m)))
  let : Mono (latchingMap.{u} n) := latchingMap_mono n
  have h : Mono (e.inv ≫ latchingMap.{u} n) := inferInstance
  change Mono m
  exact he ▸ h

end CategoryTheory.CoherentRealization.RightCubeOppositeMatching
