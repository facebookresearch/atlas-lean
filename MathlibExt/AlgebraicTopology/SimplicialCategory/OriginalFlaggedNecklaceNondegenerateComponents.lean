/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceNormalizationNerveWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceComponentTerminal
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveIndependentHomEquivalenceWeak

/-!
# Genuine discreteness of original nondegenerate components

The SAME original component-label functor on the full nondegenerate
subcategory is an actual categorical equivalence with the discrete
original connected-component category. Essential surjectivity follows
from the PROVED whole original normalization map; full faithfulness
uses actual original paired-surjection lifting and uniqueness.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Normalization

open Flanking

/-- The SAME actual original component-label functor on all flanked inputs. -/
def componentProjectionFunctor (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Flanked K x y q ⥤ Discrete (ConnectedComponents (Flanked K x y q)) :=
  ConnectedComponents.functorToDiscrete _ id

/-- The SAME actual original component labels on full original nondegenerate inputs. -/
def componentFunctor (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Normalized K x y q ⥤ Discrete (ConnectedComponents (Flanked K x y q)) :=
  inclusion K x y q ⋙ componentProjectionFunctor K x y q

/-- Every original component equality gives an actual original nondegenerate-input map. -/
instance componentFunctorFull (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    (componentFunctor K x y q).Full where
  map_surjective := by
    intro T U f
    have h : ConnectedComponents.mk T.obj = ConnectedComponents.mk U.obj := Discrete.eq_of_hom f
    obtain ⟨m⟩ := totallyNondegenerate_hom_of_zigzag U.obj T.obj U.property (Quotient.exact' h)
    exact ⟨ObjectProperty.homMk m, Subsingleton.elim _ _⟩

/-- The SAME original component functor is faithful by genuinely proved full original map uniqueness. -/
instance componentFunctorFaithful (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    (componentFunctor K x y q).Faithful where
  map_injective := by
    intro T U f g _h
    let := hom_subsingleton T U
    exact Subsingleton.elim _ _

/-- Every actual original flanked component has its PROVED nondegenerate representative. -/
instance componentFunctorEssSurj (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    (componentFunctor K x y q).EssSurj where
  mem_essImage c := by
    obtain ⟨T, hT⟩ := Quotient.exists_rep c.as
    refine ⟨target T, ⟨eqToIso ?_⟩⟩
    apply Discrete.ext
    change ConnectedComponents.mk (target T).obj = c.as
    exact (Quotient.sound' (Zigzag.of_hom (unitMap T))).symm.trans hT

/-- The SAME component-label functor is a genuine equivalence of the actual original categories. -/
instance componentFunctorIsEquivalence (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    (componentFunctor K x y q).IsEquivalence where

/-- The genuine whole original categorical equivalence with the SAME discrete component labels. -/
def componentEquivalence (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Normalized K x y q ≌ Discrete (ConnectedComponents (Flanked K x y q)) :=
  (componentFunctor K x y q).asEquivalence

/-- The SAME complete original nondegenerate component nerve map. -/
def componentNerveMap (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    nerve (Normalized K x y q) ⟶ nerve (Discrete (ConnectedComponents (Flanked K x y q))) :=
  CategoryTheory.nerveMapHomDown.{u, 0, u} (componentFunctor K x y q)

/-- The SAME actual original nondegenerate component nerve map is genuinely weak in every scalar degree. -/
theorem componentNerveMap_weak (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences (componentNerveMap K x y q) :=
  CategoryTheory.nerveMapHomDown_mem_realizationWeakEquivalences_of_isEquivalence.{u, 0, u}
    (componentFunctor K x y q)

/-- The original normalization retains precisely the SAME connected-component labels. -/
theorem normalization_componentFunctor (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    functor K x y q ⋙ componentFunctor K x y q = componentProjectionFunctor K x y q := by
  refine CategoryTheory.Functor.ext (fun T => ?_) ?_
  · apply Discrete.ext
    exact (Quotient.sound' (Zigzag.of_hom (unitMap T))).symm
  · intro T U f
    exact Subsingleton.elim _ _

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Normalization
