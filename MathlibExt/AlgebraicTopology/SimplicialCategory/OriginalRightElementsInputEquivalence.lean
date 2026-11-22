/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightElementsInputDiagram

/-!
# Both SAME original right-mapping element/input category directions

The canonical full elements equivalence, original pointed Hom-space
isomorphism and full cosimplicial input equivalence give both entire
inverse input functors. The forward functor is the SAME literal
original quotient-map input functor, on every original object and arrow.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction

variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- Both full original right-mapping element and fixed-front input directions retain the canonical original Hom and
simplex dictionaries. -/
def rightElementsInputEquivalence :
    (SSet.mappingSpaceRight K a b).Elementsᵒᵖ ≌ CostructuredArrow plainFixedFrontDiagram (pointedInput a b) :=
  (Functor.Elements.costructuredArrowULiftYonedaEquivalence.{u,0,0} (SSet.mappingSpaceRight K a b)).trans
    ((CostructuredArrow.mapIso (pointedHomSpaceIso a b)).trans
      (CosimplicialObject.homInputEquivalence plainFixedFrontDiagram (pointedInput a b)))

/-- The SAME full original forward element/input dictionary is naturally isomorphic to the literal complete original
quotient-map functor. -/
def rightElementsInputEquivalenceReadback :
    (rightElementsInputEquivalence a b).functor ≅ rightElementsInputFunctor a b :=
  NatIso.ofComponents (fun e => CostructuredArrow.isoMk (Iso.refl e.unop.obj.unop) (by
    change plainFixedFrontDiagram.map (𝟙 e.unop.obj.unop) ≫ toPointedMap a b e.unop.val =
      SSet.yonedaEquiv ((SSet.yonedaEquiv (X := SSet.mappingSpaceRight K a b)).symm e.unop.val ≫
        (pointedHomSpaceIso a b).hom)
    have h := SSet.yonedaEquiv_comp
      ((SSet.yonedaEquiv (X := SSet.mappingSpaceRight K a b)).symm e.unop.val)
      (pointedHomSpaceIso a b).hom
    exact (congrArg (fun f => f ≫ toPointedMap a b e.unop.val)
      (plainFixedFrontDiagram.map_id e.unop.obj.unop)).trans
        ((Category.id_comp _).trans (h.trans
          (congrArg (fun σ => (pointedHomSpaceIso a b).hom.app e.unop.obj σ)
            (Equiv.apply_symm_apply (SSet.yonedaEquiv (X := SSet.mappingSpaceRight K a b)) e.unop.val))).symm)))
    (by intro e d f; apply CostructuredArrow.hom_ext; exact (Category.comp_id _).trans (Category.id_comp _).symm)

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
