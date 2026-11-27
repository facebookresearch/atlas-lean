/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Actual coherent realization of the standard simplices

The proved adjunction identifies the realization of each standard
simplex with Mathlib's original coherent simplex. This is a strict
enriched isomorphism, with both whole inverses, original vertex readback,
and every simplex-operator comparison.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment

/-- The actual coherent-nerve simplex evaluation functor in the supplied scalar degree. -/
def simplexEvaluation (n : SimplexCategory) : Carrier.{u} ⥤ Type u :=
  coherentNerveFunctor ⋙ SSet.evaluation.obj (op n)

/-- The original coherent simplex genuinely corepresents its actual enriched simplex functors. -/
def corepresentedBySimplex (n : SimplexCategory) :
    (simplexEvaluation.{u} n).CorepresentableBy (coherentSimplex n) where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/-- The actual realization corepresentation derived from the proved adjunction and ordinary
simplicial Yoneda. -/
def corepresentedByRealization (n : SimplexCategory) :
    (simplexEvaluation.{u} n).CorepresentableBy (realization (SSet.stdSimplex.obj n)) where
  homEquiv := (realizationAdjunction.homEquiv (SSet.stdSimplex.obj n) _).trans SSet.yonedaEquiv
  homEquiv_comp g f := by
    change SSet.yonedaEquiv (realizationAdjunction.homEquiv _ _ (f ≫ g)) =
      (coherentNerveFunctor.map g).app (op n) (SSet.yonedaEquiv
        (realizationAdjunction.homEquiv _ _ f))
    exact (congrArg SSet.yonedaEquiv (realizationAdjunction.homEquiv_naturality_right f g)).trans
      (SSet.yonedaEquiv_comp _ _)

/-- The genuine strict enriched isomorphism from realization of the standard simplex to the original
  coherent simplex. -/
def simplexIso (n : SimplexCategory) : realization (SSet.stdSimplex.{u}.obj n) ≅
  coherentSimplex.{u} n :=
  (corepresentedByRealization n).uniqueUpToIso (corepresentedBySimplex n)

/-- The actual forward simplex isomorphism is the adjunction transpose of the original
identity coherent simplex. -/
theorem simplexIso_hom_eq (n : SimplexCategory) :
    (simplexIso.{u} n).hom = (realizationAdjunction.homEquiv (SSet.stdSimplex.obj n)
      (coherentSimplex n)).symm
      (SSet.yonedaEquiv.symm (𝟙 (coherentSimplex n))) := rfl

/-- The complete inverse is the original enriched insertion of the identity standard simplex. -/
theorem simplexIso_inv_eq (n : SimplexCategory) :
    (simplexIso.{u} n).inv =
      simplexInto (SSet.stdSimplex.{u}.obj n) (SSet.yonedaEquiv (𝟙
        (SSet.stdSimplex.{u}.obj n))) := by
  change SSet.yonedaEquiv
    (realizationAdjunction.homEquiv (SSet.stdSimplex.{u}.obj n) _ (𝟙 _)) = _
  rw [realizationAdjunction.homEquiv_id]
  rfl

/-- Its actual forward map reads every individual original standard-simplex vertex as the
corresponding
  coherent vertex. -/
theorem simplexIso_hom_obj (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (simplexIso.{u} n).hom.obj (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ n i)) =
      SimplicialThickening.mk (ULift.up i) := rfl

/-- The whole standard-simplex comparison has the literal identity coherent simplex as its
adjunction readback. -/
theorem simplexIso_hom_adjunction (n : SimplexCategory) :
    realizationAdjunction.homEquiv (SSet.stdSimplex.{u}.obj n) (coherentSimplex n)
      (simplexIso n).hom =
      SSet.yonedaEquiv.symm (𝟙 (coherentSimplex n)) := by
  rw [simplexIso_hom_eq]
  exact (realizationAdjunction.homEquiv _ _).apply_symm_apply _

/-- All original simplex operators commute with the whole enriched standard-simplex comparison. -/
theorem simplexIso_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    realizationMap (SSet.stdSimplex.{u}.map f) ≫ (simplexIso m).hom =
      (simplexIso n).hom ≫ coherentSimplexMap f := by
  apply (realizationAdjunction.homEquiv (SSet.stdSimplex.obj n) (coherentSimplex m)).injective
  have hl := realizationAdjunction.homEquiv_naturality_left (SSet.stdSimplex.map f)
    (simplexIso m).hom
  have hr := realizationAdjunction.homEquiv_naturality_right (simplexIso n).hom
    (coherentSimplexMap f)
  have hleft := SSet.yonedaEquiv_symm_naturality_left
    (X := coherentNerveFunctor.obj (coherentSimplex.{u} m)) f (𝟙 (coherentSimplex m))
  have hright := SSet.yonedaEquiv_symm_comp
    (X := coherentNerveFunctor.obj (coherentSimplex.{u} n)) (n := n) (𝟙 (coherentSimplex n))
    (coherentNerveFunctor.map (coherentSimplexMap f))
  change SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm (𝟙 (coherentSimplex.{u} m)) =
    (SSet.yonedaEquiv.symm (coherentSimplexMap f ≫ 𝟙 (coherentSimplex m)) :
      SSet.stdSimplex.obj n ⟶ coherentNerveFunctor.obj (coherentSimplex m)) at hleft
  change SSet.yonedaEquiv.symm (𝟙 (coherentSimplex.{u} n)) ≫
    coherentNerveFunctor.map (coherentSimplexMap f) =
      (SSet.yonedaEquiv.symm (𝟙 (coherentSimplex n) ≫ coherentSimplexMap f) :
        SSet.stdSimplex.obj n ⟶ coherentNerveFunctor.obj (coherentSimplex m)) at hright
  let E : (SSet.stdSimplex.{u}.obj n ⟶ coherentNerveFunctor.obj (coherentSimplex m)) ≃
      (coherentSimplex n ⟶ coherentSimplex m) := SSet.yonedaEquiv
  have hm := hleft.trans (congrArg E.symm (Category.comp_id (coherentSimplexMap f)))
  have hn := hright.trans (congrArg E.symm (Category.id_comp (coherentSimplexMap f)))
  exact (hl.trans (congrArg (fun t => SSet.stdSimplex.map f ≫
    t) (simplexIso_hom_adjunction m))).trans
    ((hm.trans hn.symm).trans
      (hr.trans (congrArg (fun t => t ≫ coherentNerveFunctor.map (coherentSimplexMap f))
        (simplexIso_hom_adjunction n))).symm)

end CategoryTheory.CoherentRealization
