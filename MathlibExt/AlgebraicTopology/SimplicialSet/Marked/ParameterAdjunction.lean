/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalCurrying
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingNaturality
import Mathlib.CategoryTheory.Adjunction.Parametrized
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The native maximal-parameter tensor and mapping adjunction

The actual product of the maximally marked original parameter and the
original marked source is left adjoint to the maximal marked mapping
complex. Both adjunction directions are the existing literal currying and
uncurrying maps. Source naturality retains every original product map,
giving a genuine parametrized adjunction for the native pushout-product
and mapping pullback comparison. No marked-model assumption is made.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original maximal mapping complex is covariant on actual marked target maps. -/
def maxMappingFunctor (X : Marked.{u}) : Marked.{u} ⥤ SSet.{u} where
  obj Y := mappingComplex .maximal X Y
  map p := mappingComplexPost .maximal X p
  map_id Y := mappingComplexPost_id .maximal X Y
  map_comp f g := mappingComplexPost_comp .maximal X f g

/-- The actual original simplicial parameter is maximally marked and multiplied with the supplied source. -/
def maxTensorFunctor (X : Marked.{u}) : SSet.{u} ⥤ Marked.{u} := maximal ⋙ prodRight X

/-- Uncurrying retains the whole original marked target composition. -/
theorem maxUncurry_post {K : SSet.{u}} {X Y Y' : Marked.{u}}
    (g : K ⟶ mappingComplex .maximal X Y) (p : Y ⟶ Y') :
    maxUncurry (g ≫ mappingComplexPost .maximal X p) = maxUncurry g ≫ p := by
  apply (maxFamilyHomEquiv K X Y').injective
  change maxCurry (maxUncurry (g ≫ mappingComplexPost .maximal X p)) = maxCurry (maxUncurry g ≫ p)
  rw [maxCurry_maxUncurry, maxCurry_post, maxCurry_maxUncurry]

/-- The same original source-product map is retained by maximal currying. -/
theorem maxCurry_source {K : SSet.{u}} {X X' Y : Marked.{u}}
    (f : X ⟶ X') (g : prod (max K) X' ⟶ Y) :
    maxCurry (prodMap (𝟙 (max K)) f ≫ g) = maxCurry g ≫ mappingComplexPre .maximal f Y := by
  ext n a
  apply Hom.ext
  rfl

/-- The existing whole-prism currying maps form the actual maximal tensor/mapping adjunction. -/
def maxTensorAdjunction (X : Marked.{u}) : maxTensorFunctor X ⊣ maxMappingFunctor X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun K Y => maxFamilyHomEquiv K X Y
      homEquiv_naturality_left_symm := by
        intro K' K Y f g
        exact maxUncurry_pre f g
      homEquiv_naturality_right := by
        intro K Y Y' f g
        exact maxCurry_post f g }

/-- The original marked source acts on the native maximal parameter tensor. -/
def maxTensorBifunctor : Marked.{u} ⥤ SSet.{u} ⥤ Marked.{u} where
  obj X := maxTensorFunctor X
  map f := Functor.whiskerLeft maximal (prodRightMap f)
  map_id X := by
    apply NatTrans.ext
    funext K
    exact prodMap_id (max K) X
  map_comp f g := by
    apply NatTrans.ext
    funext K
    change prodMap (𝟙 (max K)) (f ≫ g) = prodMap (𝟙 (max K)) f ≫ prodMap (𝟙 (max K)) g
    exact (congrArg (fun t => prodMap t (f ≫ g)) (Category.id_comp (𝟙 (max K)))).symm.trans
      (prodMap_comp (𝟙 (max K)) (𝟙 (max K)) f g)

/-- Native maximal mapping complexes form the contravariant-source, covariant-target bifunctor. -/
def maxMappingBifunctor : Marked.{u}ᵒᵖ ⥤ Marked.{u} ⥤ SSet.{u} where
  obj X := maxMappingFunctor X.unop
  map f :=
    { app Y := mappingComplexPre .maximal f.unop Y
      naturality Y Y' p := mappingComplexPre_post .maximal f.unop p }
  map_id X := by
    apply NatTrans.ext
    funext Y
    exact mappingComplexPre_id .maximal X.unop Y
  map_comp f g := by
    apply NatTrans.ext
    funext Y
    exact mappingComplexPre_comp .maximal g.unop f.unop Y

/-- The actual product/mapping adjunction is natural in the supplied original marked source. -/
def maxTensorAdjunction₂ : maxTensorBifunctor.{u} ⊣₂ maxMappingBifunctor.{u} :=
  ParametrizedAdjunction.mk' maxTensorAdjunction (by
    intro X X' f K Y g
    exact maxCurry_source f g)

/-- The actual parameter tensor preserves original colimits by its genuine native adjunction. -/
theorem maxTensor_preservesColimits (X : Marked.{u}) :
    PreservesColimitsOfSize.{u, u} (maxTensorFunctor X) :=
  (maxTensorAdjunction X).leftAdjoint_preservesColimits

end SSet.Marked
