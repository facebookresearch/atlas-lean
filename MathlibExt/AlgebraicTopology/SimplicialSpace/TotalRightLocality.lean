/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.TotalComparisonBoxDivision
import MathlibExt.AlgebraicTopology.SimplicialSpace.SpineInnerAnodyne
import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FilteredColimitsGeneral
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FunctionRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPSimplicialHomotopyEquiv
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Original localizing tests of the total right adjoint

For an original quasicategory, restriction along every original Segal spine
and the full walking-isomorphism endpoint has scalar boundary RLP. The proof
uses the accepted left-division comparison and the actual k adjunction:
k-left monicity suffices to preserve boundary RLP on k-right.

This is the locality step of Joyal–Tierney, *Quasi-categories vs Segal spaces*,
Theorems 3.3 and 4.12, using the natural comparisons of Lemma 2.11. The total
right image's Reedy fibrancy is a separate theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Opposite MonoidalCategory MonoidalClosed
open scoped Simplicial

namespace SimplicialSpace.TotalSpace

private theorem kRight_boundaryRLP {X Y : SSet.{u}} (q : X ⟶ Y)
    (hq : SSet.modelCategoryQuillen.I.rlp q) :
    SSet.modelCategoryQuillen.I.rlp (SSet.FreeGroupoidSimplex.kRightFunctor.map q) := by
  rw [← SSet.rlp_monomorphisms] at hq ⊢
  intro A B j hj
  let : Mono j := hj
  have h : HasLiftingProperty (SSet.FreeGroupoidSimplex.kFunctor.map j) q :=
    hq _ inferInstance
  exact (SSet.FreeGroupoidSimplex.kAdjunction.hasLiftingProperty_iff j q).mp h

set_option backward.isDefEq.respectTransparency false in
private def leftDivision_restrictionIso {A B : SSet.{u}} (i : A ⟶ B)
    (Q : JoyalSSet.{u}) :
    Arrow.mk ((boxLeftDivisionFunctor.map i.op).app (right.obj Q)) ≅
      Arrow.mk (SSet.FreeGroupoidSimplex.kRightFunctor.map ((pre i).app Q.toSSet)) :=
  Arrow.isoMk ((leftDivisionIso.app (op B)).app Q)
    ((leftDivisionIso.app (op A)).app Q)
    (by
      have hr : (totalLeftDivision.map i.op).app Q =
          (boxLeftDivisionFunctor.map i.op).app (right.obj Q) := rfl
      have hk : (totalLeftFunction.map i.op).app Q =
          SSet.FreeGroupoidSimplex.kRightFunctor.map ((pre i).app Q.toSSet) := rfl
      have h := congr_app (leftDivisionIso.hom.naturality i.op) Q
      simpa only [NatTrans.comp_app, hr, hk, Iso.app_hom, Arrow.mk_hom,
        Arrow.mk_left, Arrow.mk_right] using h.symm)

private theorem leftDivision_restriction_boundaryRLP {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (hi : SSet.categoricalEquivalences i)
    (Q : JoyalSSet.{u}) [SSet.Quasicategory Q.toSSet] :
    SSet.modelCategoryQuillen.I.rlp
      ((boxLeftDivisionFunctor.map i.op).app (right.obj Q)) := by
  have hq : SSet.modelCategoryQuillen.I.rlp ((pre i).app Q.toSSet) :=
    (SSet.categoricalFibrations_and_categoricalEquivalences_iff _).mp
      (SSet.categoricalFibrations_and_categoricalEquivalences_pre_app_of_mono
        i hi Q.toSSet)
  exact (SSet.modelCategoryQuillen.I.rlp.arrow_mk_iso_iff
    (leftDivision_restrictionIso i Q)).mpr (kRight_boundaryRLP _ hq)

/-- Every original Segal and full walking-isomorphism restriction of the actual
total right image of a quasicategory lifts against all scalar boundaries. -/
theorem right_localizingMap_boundaryRLP (Q : JoyalSSet.{u})
    [SSet.Quasicategory Q.toSSet] (a : SSet.Rezk.LocalizingIndex) :
    SSet.modelCategoryQuillen.I.rlp
      ((innerHomFunctor.map
        (ofSimplicialObject.map (SSet.Rezk.localizingMap.{u} a).hom).op).app
        (right.obj Q)) := by
  rcases a with n | c
  · have hi := SSet.Rezk.monomorphisms_inf_categoricalEquivalences_spineSubcomplex_ι
      n.val n.property
    let : Mono (SSet.Rezk.spineSubcomplex.{u} n.val).ι := hi.1
    change SSet.modelCategoryQuillen.I.rlp
      ((boxLeftDivisionFunctor.map (SSet.Rezk.spineSubcomplex.{u} n.val).ι.op).app
        (right.obj Q))
    exact leftDivision_restriction_boundaryRLP _ hi.2 Q
  · have hi := SSet.coherentIso_endpointInclusion_mem.{u}
    let : Mono SSet.coherentIso.endpointInclusion.{u} := hi.1
    change SSet.modelCategoryQuillen.I.rlp
      ((boxLeftDivisionFunctor.map SSet.coherentIso.endpointInclusion.op).app
        (right.obj Q))
    exact leftDivision_restriction_boundaryRLP _ hi.2 Q

/-- The same original localizing restrictions are full realization weak
equivalences, without an additional Kan hypothesis on either mapping object. -/
theorem right_localizingMap_realizationWeak (Q : JoyalSSet.{u})
    [SSet.Quasicategory Q.toSSet] (a : SSet.Rezk.LocalizingIndex) :
    SSet.realizationWeakEquivalences
      ((innerHomFunctor.map
        (ofSimplicialObject.map (SSet.Rezk.localizingMap.{u} a).hom).op).app
        (right.obj Q)) :=
  SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
    (right_localizingMap_boundaryRLP Q a)

end SimplicialSpace.TotalSpace
