/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalInnerCotensorMatching
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalNamedCSSCotensorCorner
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyModelCategory
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# The literal inner-coend adjunction is Quillen for the named CSS Reedy model

The actual INNER boundary matching comparison supplies the relative
matching pullback. Its two legs are mapped by the designation equivalence
to the native supplied coefficient cotensor corner. Native pullback-corner
uniqueness gives the genuine Arrow Iso. Existing global scalar cotensor
fibration and trivial-fibration proofs then give both right-adjoint
preservation clauses in every Reedy degree, including zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

namespace SimplicialSpace.OriginalInnerRealization
open OriginalNamedCSSCotensor

/-- Forget the actual relative matching square, retaining its two characteristic cotensor legs. -/
def coefficientRelativeMatchingPullbackObjObj (n : ℕ)
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    (coefficientCotensorParallel (SSet.boundary.{u} n).ι).PullbackObjObj
        WalkingParallelPairHom.left p.hom where
  pt := (SimplicialObject.relativeMatchingObject (innerRealizationRightFunctor.map p) n).diagram
  fst := (innerBoundaryRelativeMatchingPullbackObjObj n p).fst.hom
  snd := (innerBoundaryRelativeMatchingPullbackObjObj n p).snd.hom
  isPullback := (innerBoundaryRelativeMatchingPullbackObjObj n p).isPullback.map forget
  π := (SimplicialObject.relativeMatchingMap (innerRealizationRightFunctor.map p) n).hom
  π_fst := by
    let s := innerBoundaryRelativeMatchingPullbackObjObj n p
    exact (forget.map_comp s.π s.fst).symm.trans (congrArg forget.map s.π_fst)
  π_snd := by
    let s := innerBoundaryRelativeMatchingPullbackObjObj n p
    exact (forget.map_comp s.π s.snd).symm.trans (congrArg forget.map s.π_snd)

/-- The whole relative matching arrow is genuinely isomorphic to the same designated native
corner. -/
def innerBoundaryRelativeMatchingCotensorArrowIso (n : ℕ)
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    Arrow.mk (SimplicialObject.relativeMatchingMap (innerRealizationRightFunctor.map p) n) ≅
      designatedCotensorCornerArrow (SSet.boundary.{u} n).ι p := by
  let a := coefficientRelativeMatchingPullbackObjObj n p
  let b := coefficientCotensorPullback (SSet.boundary.{u} n).ι p
  let e : Arrow.mk a.π ≅ Arrow.mk b.π :=
    Functor.PullbackObjObj.π_iso_of_iso_left
      (G := coefficientCotensorParallel (SSet.boundary.{u} n).ι)
      (f₁ := Arrow.mk WalkingParallelPairHom.left)
      (f₁' := Arrow.mk WalkingParallelPairHom.left) (f₃ := Arrow.mk p.hom)
      a b (Iso.refl _)
  change Arrow.mk (ofSimplicialObject.map a.π) ≅ Arrow.mk (ofSimplicialObject.map b.π)
  exact ofSimplicialObject.mapArrow.mapIso e

/-- Every actual relative matching arrow is globally CSS fibrational for an input CSS fibration. -/
theorem innerBoundaryRelativeMatching_fibration (n : ℕ)
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    fibrations SimplicialSpace.{u} p →
      fibrations SimplicialSpace.{u}
        (SimplicialObject.relativeMatchingMap (innerRealizationRightFunctor.map p) n) := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  intro hp
  have hb : Cofibration (SSet.boundary.{u} n).ι :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  have hc := (HomotopicalAlgebra.cofibration_iff _).mp hb
  have hq := designatedCotensorCorner_fibration (SSet.boundary.{u} n).ι p hc hp
  exact ((fibrations SimplicialSpace.{u}).arrow_mk_iso_iff
    (innerBoundaryRelativeMatchingCotensorArrowIso n p)).mpr hq

/-- Global input CSS triviality gives triviality of the exact same relative matching corner. -/
theorem innerBoundaryRelativeMatching_trivialFibration (n : ℕ)
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    trivialFibrations SimplicialSpace.{u} p →
      trivialFibrations SimplicialSpace.{u}
        (SimplicialObject.relativeMatchingMap (innerRealizationRightFunctor.map p) n) := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  intro hp
  have hb : Cofibration (SSet.boundary.{u} n).ι :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  have hc := (HomotopicalAlgebra.cofibration_iff _).mp hb
  have hq := designatedCotensorCorner_trivialFibration (SSet.boundary.{u} n).ι p hc hp
  exact ((trivialFibrations SimplicialSpace.{u}).arrow_mk_iso_iff
    (innerBoundaryRelativeMatchingCotensorArrowIso n p)).mpr hq

/-- The actual right adjoint preserves every fibration into the genuine CSS-valued Reedy model. -/
theorem innerRealizationRight_preservesFibrations :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    letI : ModelCategory (SimplicialObject SimplicialSpace.{u}) :=
      SimplicialObject.reedyModelCategory
    PreservesFibrations innerRealizationRightFunctor.{u} := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let : ModelCategory (SimplicialObject SimplicialSpace.{u}) :=
    SimplicialObject.reedyModelCategory
  intro X Y p hp
  change ∀ n : ℕ, fibrations SimplicialSpace.{u}
    (SimplicialObject.relativeMatchingMap (innerRealizationRightFunctor.map p) n)
  exact fun n => innerBoundaryRelativeMatching_fibration n p hp

/-- The same actual right adjoint preserves global trivial fibrations in every Reedy degree. -/
theorem innerRealizationRight_preservesTrivialFibrations :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    letI : ModelCategory (SimplicialObject SimplicialSpace.{u}) :=
      SimplicialObject.reedyModelCategory
    PreservesTrivialFibrations innerRealizationRightFunctor.{u} := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let : ModelCategory (SimplicialObject SimplicialSpace.{u}) :=
    SimplicialObject.reedyModelCategory
  intro X Y p hp
  change (SimplicialObject.reedyRight (fibrations SimplicialSpace.{u}) ⊓
    (weakEquivalences SimplicialSpace.{u}).functorCategory SimplexCategoryᵒᵖ)
      (innerRealizationRightFunctor.map p)
  rw [← SimplicialObject.reedyRight_trivialFibrations_eq]
  exact fun n => innerBoundaryRelativeMatching_trivialFibration n p hp

/-- The actual coend/cotensor adjunction is Quillen for the literal named CSS base and Reedy
model. -/
theorem innerRealizationAdjunction_isQuillen :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    letI : ModelCategory (SimplicialObject SimplicialSpace.{u}) :=
      SimplicialObject.reedyModelCategory
    Adjunction.IsQuillenAdjunction innerRealizationAdjunction.{u} := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let : ModelCategory (SimplicialObject SimplicialSpace.{u}) :=
    SimplicialObject.reedyModelCategory
  exact Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (adj := innerRealizationAdjunction) innerRealizationRight_preservesFibrations
      innerRealizationRight_preservesTrivialFibrations

end SimplicialSpace.OriginalInnerRealization
