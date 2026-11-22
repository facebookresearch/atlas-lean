/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCubeHomFamily
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontFamilyRecognition
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontFamilyStrictMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontFamilyTransport

/-!
# Actual whole original right-mapping simplex and cube-Hom equivalence

The actual distinguished insertion, original evaluation functor and
proved front-compatible family recognition recover every supplied whole
right-mapping simplex. Together with the original cube-map readback,
this gives both genuine inverse equations at each degree without a Kan,
strict nerve or comparison outcome hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.CubeMappingEquivalence
open SimplicialEnrichment FixedFrontCubeMap HomFrontFamilyStrictMaps HomFrontFamilyTransport
variable {C : Carrier.{u}} {n : ℕ} (x y : C)

/-- The actual distinguished interval family postcomposed by the original evaluation and retargeted to the
  same individual endpoints. -/
def evaluatedFamily
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    HomFrontFamily.Family x y n :=
  retarget (FixedFrontEvaluation.functor_source x y σ) (FixedFrontEvaluation.functor_target x y σ)
    (postFamily (FixedFrontEvaluation.functor x y σ) (FixedFrontCollapse.source n) (FixedFrontCollapse.target n)
      (FixedFrontFamilyRecognition.family n))

/-- Each whole original post-evaluation interval is exactly the same interval constructed from the actual
  cube Hom evaluation. -/
theorem evaluatedFamily_eq
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    evaluatedFamily x y σ = CubeHomFamily.family x y (FixedFrontMappingEvaluation.evaluate x y σ) := by
  apply family_ext
  intro i
  let F := FixedFrontEvaluation.functor x y σ
  let E := EqualityTransport.hom (FixedFrontEvaluation.functor_source x y σ) (FixedFrontEvaluation.functor_target x y σ)
  let L := FixedFrontEvaluation.homMap x y σ
  let A := nerveMap (RightCubeRelations.prependFunctor.{u} i)
  let B := RightCubeRelations.projection.{u} n
  let V := cubeMap.{u} n
  have hLeft : (evaluatedFamily x y σ).map i = intervalMap n i ≫ L := Category.assoc (intervalMap n i) (F.map _ _) E
  have hPre : A ≫ intervalMap n 0 = intervalMap n i := by
    ext q p
    exact interval_prepend n i q p
  have hRight : (CubeHomFamily.family x y (FixedFrontMappingEvaluation.evaluate x y σ)).map i = intervalMap n i ≫ L :=
    (congrArg (fun f => A ≫ f) (Category.assoc B V L).symm).trans
      ((Category.assoc A (B ≫ V) L).symm.trans
        ((congrArg (fun f => (A ≫ f) ≫ L) (cubeMap_projection n)).trans
          (congrArg (fun f => f ≫ L) hPre)))
  exact hLeft.trans hRight.symm

/-- Construction after actual original cube evaluation recovers the entire supplied right-mapping simplex
  and all its original Hom maps. -/
theorem construct_evaluate
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    CubeHomFamily.construct x y (FixedFrontMappingEvaluation.evaluate x y σ) = σ := by
  let F := FixedFrontEvaluation.functor x y σ
  have h : FixedFrontInsertion.functor n ≫ F =
      HomFrontFamily.simplex x y (CubeHomFamily.family x y (FixedFrontMappingEvaluation.evaluate x y σ)) :=
    (congrArg (fun S => S ≫ F) (FixedFrontFamilyRecognition.functor_eq n)).trans
      ((simplex_postcompose F (FixedFrontCollapse.source n) (FixedFrontCollapse.target n)
        (FixedFrontFamilyRecognition.family n)).trans
        ((simplex_retarget (FixedFrontEvaluation.functor_source x y σ) (FixedFrontEvaluation.functor_target
          x y σ) _).trans
          (congrArg (HomFrontFamily.simplex x y) (evaluatedFamily_eq x y σ))))
  apply (SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n).injective
  apply Subtype.ext
  apply SSet.yonedaEquiv.injective
  exact (CubeHomFamily.enriched_construct x y (FixedFrontMappingEvaluation.evaluate x y σ)).trans
    (h.symm.trans (FixedFrontEvaluationInsertion.insertion x y σ))

/-- The actual original right-mapping simplices are precisely the whole original cube-to-Hom maps, with both
  inverses proved. -/
def equiv :
    (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌ ≃
      (RightCubeRelations.object.{u} n ⟶ (x ⟶[SSet.{u}] y)) where
  toFun := FixedFrontMappingEvaluation.evaluate x y
  invFun := CubeHomFamily.construct x y
  left_inv := construct_evaluate x y
  right_inv := CubeHomFamily.evaluate_construct x y

end CategoryTheory.CoherentRealization.CubeMappingEquivalence
