/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ProperFaceBoundary
import Mathlib.CategoryTheory.Limits.Opposites

/-!
# Opposite matching maps of the actual standard simplex diagram

The full proper-face boundary colimit identifies each matching map of
the opposite standard simplex diagram with the original boundary
inclusion. The construction includes the empty boundary in degree zero.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.StandardSimplexOppositeMatching
open SSet.ProperFaceBoundary

/-- The actual full proper-face boundary is canonically isomorphic to the unopposite matching object of the
  standard simplex diagram. -/
def boundaryIso (n : ℕ) : (boundary.{u} n : SSet.{u}) ≅
    unop (SimplicialObject.matchingObject stdSimplex.{u}.op n) :=
  (properFaceBoundaryIsColimit.{u} n).coconePointUniqueUpToIso
    (colimit.isColimit (SimplicialObject.matchingDiagram stdSimplex.{u}.op n).leftOp) ≪≫
      colimitLeftOpIsoUnopLimit (SimplicialObject.matchingDiagram stdSimplex.{u}.op n)

/-- The comparison carries the actual opposite matching arrow to the same original boundary inclusion. -/
theorem matching_factor (n : ℕ) : (boundaryIso.{u} n).hom ≫
    (SimplicialObject.matchingMap stdSimplex.{u}.op n).unop = (boundary.{u} n).ι := by
  apply (properFaceBoundaryIsColimit.{u} n).hom_ext
  intro a
  let F := SimplicialObject.matchingDiagram stdSimplex.{u}.op n
  have hc := (properFaceBoundaryIsColimit.{u} n).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit F.leftOp) a
  have he := ι_comp_colimitLeftOpIsoUnopLimit_hom F a
  let e : (boundary.{u} n : SSet.{u}) ≅ colimit F.leftOp :=
    (properFaceBoundaryIsColimit.{u} n).coconePointUniqueUpToIso (colimit.isColimit F.leftOp)
  let t := colimitLeftOpIsoUnopLimit F
  let m := (SimplicialObject.matchingMap stdSimplex.{u}.op n).unop
  have hi : (boundaryIso.{u} n).hom = e.hom ≫ t.hom := rfl
  have hm : (SimplicialObject.matchingπ stdSimplex.{u}.op n a.unop).unop ≫ m =
      stdSimplex.map a.unop.obj.hom.unop :=
    congrArg Quiver.Hom.unop (SimplicialObject.matchingMap_π stdSimplex.{u}.op n a.unop)
  change properFaceBoundaryInclusion.{u} a.unop ≫
      ((boundaryIso.{u} n).hom ≫ (SimplicialObject.matchingMap stdSimplex.{u}.op n).unop) =
    properFaceBoundaryInclusion.{u} a.unop ≫ (boundary.{u} n).ι
  exact (congrArg (fun f => properFaceBoundaryInclusion.{u} a.unop ≫ (f ≫ m)) hi).trans
    ((Category.assoc (properFaceBoundaryInclusion.{u} a.unop) e.hom (t.hom ≫ m)).symm.trans
      ((congrArg (fun f => f ≫ (t.hom ≫ m)) hc).trans
        ((Category.assoc (colimit.ι F.leftOp a) t.hom m).symm.trans
          ((congrArg (fun f => f ≫ m) he).trans
            (hm.trans (properFaceBoundaryInclusion_ι a.unop).symm)))))

/-- Every actual unopposite matching map of the original standard simplex diagram is a simplicial monomorphism. -/
theorem matching_unop_mono (n : ℕ) :
    Mono (SimplicialObject.matchingMap stdSimplex.{u}.op n).unop := by
  let e := boundaryIso.{u} n
  let m := (SimplicialObject.matchingMap stdSimplex.{u}.op n).unop
  have he : e.inv ≫ (boundary.{u} n).ι = m :=
    (congrArg (fun f => e.inv ≫ f) (matching_factor.{u} n).symm).trans
      ((Category.assoc e.inv e.hom m).symm.trans
        ((congrArg (fun f => f ≫ m) e.inv_hom_id).trans (Category.id_comp m)))
  have h : Mono (e.inv ≫ (boundary.{u} n).ι) := inferInstance
  change Mono m
  exact he ▸ h

end SSet.StandardSimplexOppositeMatching
