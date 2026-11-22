/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentInverse
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentRawEvaluationFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentExt

/-!
# The SAME original raw Hom and full flagged components are isomorphic

The original raw presentation and the full original flagged component
enrichment have inverse enriched functors with literal identity object
maps. Both full Hom inverse identities retain the original raw quotient,
every native input map, all flags and every scalar operator.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

open OriginalBead SimplicialQuiver

/-- The SAME full original component interpretation followed by evaluation is the whole original identity. -/
theorem realizationMap_evaluationFunctor (K : SSet.{u}) :
    realizationMap K ≫ evaluationFunctor K = 𝟙 (CoherentRealization.realization K) := by
  refine CoherentRealization.hom_ext rfl ?_
  intro x y
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro a
  cases a with
  | mk n σ i j hx hy p =>
    change rawEvaluation K x y q
      ((rawHomMap K x y).app q
        (_root_.Quotient.mk (congruence (relations K) q x y) (arrowPath K σ i j hx hy p))) =
      _root_.Quotient.mk (congruence (relations K) q x y) (arrowPath K σ i j hx hy p)
    have hA := rawHomMap_arrow (Arrow.mk n σ i j hx hy p)
    exact (congrArg (rawEvaluation K x y q) hA).trans
      ((evaluation_ofBead (trim (Arrow.mk n σ i j hx hy p))).trans
        (evaluation_trim (Arrow.mk n σ i j hx hy p)))

/-- The SAME original raw quotient followed by full component evaluation is the raw identity. -/
theorem rawHomMap_rawEvaluationMap (K : SSet.{u}) (x y : K _⦋0⦌) :
    rawHomMap K x y ≫ rawEvaluationMap K x y = 𝟙 (hom K x y) := by
  have h := EnrichedFunctor.homMap_eq (realizationMap_evaluationFunctor K)
    (rfl : (realizationMap K ≫ evaluationFunctor K).obj x = x)
    (rfl : (realizationMap K ≫ evaluationFunctor K).obj y = y)
    (rfl : (show CoherentRealization.realization K ⟶ CoherentRealization.realization K from 𝟙 _).obj x = x)
    (rfl : (show CoherentRealization.realization K ⟶ CoherentRealization.realization K from 𝟙 _).obj y = y)
  change (rawHomMap K x y ≫ rawEvaluationMap K x y) ≫ 𝟙 _ =
    (𝟙 (hom K x y)) ≫ 𝟙 _ at h
  exact (Category.comp_id _).symm.trans (h.trans (Category.comp_id _))

/-- Both actual full inverse maps on the SAME original raw Hom and flagged component simplicial set. -/
def rawHomIso (K : SSet.{u}) (x y : K _⦋0⦌) : hom K x y ≅ simplicialSet K x y where
  hom := rawHomMap K x y
  inv := rawEvaluationMap K x y
  hom_inv_id := rawHomMap_rawEvaluationMap K x y
  inv_hom_id := rawEvaluationMap_rawHomMap K x y

/-- The genuine original raw Hom isomorphism retains the SAME full presentation map. -/
theorem rawHomIso_hom (K : SSet.{u}) (x y : K _⦋0⦌) : (rawHomIso K x y).hom = rawHomMap K x y := rfl

/-- The genuine original raw Hom isomorphism retains the SAME full native evaluation map. -/
theorem rawHomIso_inv (K : SSet.{u}) (x y : K _⦋0⦌) :
    (rawHomIso K x y).inv = rawEvaluationMap K x y := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
