/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeMappingPost
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterAdjunction

/-!
# Actual marked parameter families over the original base

The maximally marked parameter product is an object over the same supplied
base through the original source projection. Its actual marked maps over
that base are represented by the original relative mapping complex.
Currying, uncurrying and evaluation retain every whole prism and the
literal base equation. This is the native tensor/mapping adjunction in
the original slice, without any base-fibrancy premise.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original parameter product lies over the supplied base through the original source projection. -/
def overParameter (Z : Marked.{u}) (X : Over Z) (K : SSet.{u}) : Over Z :=
  Over.mk (prodSnd (max K) X.left ≫ X.hom)

/-- Parameter maps act through the same original product map over the base. -/
def overParameterFunctor (Z : Marked.{u}) (X : Over Z) : SSet.{u} ⥤ Over Z where
  obj K := overParameter Z X K
  map {K K'} a := Over.homMk (prodMap (maximal.map a) (𝟙 X.left)) (by
    apply Hom.ext
    rfl)
  map_id K := by
    apply Over.OverMorphism.ext
    exact prodMap_id (max K) X.left
  map_comp a b := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl

/-- Original maps over the base are literally the full marked families with their supplied base equation. -/
def overParameterHomFamilyEquiv (Z : Marked.{u}) (X Y : Over Z) (K : SSet.{u}) :
    (overParameter Z X K ⟶ Y) ≃ RelativeMaxFamily K X.hom Y.hom where
  toFun f := ⟨f.left, Over.w f⟩
  invFun f := Over.homMk f.val f.property
  left_inv f := by apply Over.OverMorphism.ext; rfl
  right_inv f := by apply Subtype.ext; rfl

/-- The actual relative maximal complex represents all original parameter families over the same base. -/
def overParameterHomEquiv (Z : Marked.{u}) (X : Over Z) (K : SSet.{u}) (Y : Over Z) :
    (overParameter Z X K ⟶ Y) ≃ (K ⟶ relativeMappingComplex .maximal X.hom Y.hom) :=
  (overParameterHomFamilyEquiv Z X Y K).trans (relativeMaxFamilyEquiv K X.hom Y.hom)

/-- Parameter precomposition retains the original maximally marked product map in slice uncurrying. -/
theorem overParameterHomEquiv_symm_pre (Z : Marked.{u}) (X Y : Over Z)
    {K K' : SSet.{u}} (a : K' ⟶ K) (g : K ⟶ relativeMappingComplex .maximal X.hom Y.hom) :
    (overParameterHomEquiv Z X K' Y).symm (a ≫ g) =
      (overParameterFunctor Z X).map a ≫ (overParameterHomEquiv Z X K Y).symm g := by
  apply Over.OverMorphism.ext
  exact relativeMaxFamilyEquiv_symm_pre X.hom Y.hom a g

/-- Slice target composition curries to the same native relative postcomposition map. -/
theorem overParameterHomEquiv_post (Z : Marked.{u}) (X : Over Z) (K : SSet.{u})
    {Y Y' : Over Z} (f : overParameter Z X K ⟶ Y) (g : Y ⟶ Y') :
    overParameterHomEquiv Z X K Y' (f ≫ g) =
      overParameterHomEquiv Z X K Y f ≫
        relativeMappingPost .maximal X.hom g.left Y.hom Y'.hom (Over.w g) := by
  let P := overParameterHomEquiv Z X K Y f
  let P' := overParameterHomEquiv Z X K Y' (f ≫ g)
  let T := relativeMappingPost .maximal X.hom g.left Y.hom Y'.hom (Over.w g)
  let a : relativeMappingComplex .maximal X.hom Y.hom ⟶ mappingComplex .maximal X.left Y.left :=
    pullback.fst (mappingComplexPost .maximal X.left Y.hom) (mappingBasePoint .maximal X.hom)
  let a' : relativeMappingComplex .maximal X.hom Y'.hom ⟶ mappingComplex .maximal X.left Y'.left :=
    pullback.fst (mappingComplexPost .maximal X.left Y'.hom) (mappingBasePoint .maximal X.hom)
  let b : relativeMappingComplex .maximal X.hom Y.hom ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost .maximal X.left Y.hom) (mappingBasePoint .maximal X.hom)
  let b' : relativeMappingComplex .maximal X.hom Y'.hom ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (mappingComplexPost .maximal X.left Y'.hom) (mappingBasePoint .maximal X.hom)
  have hP : P ≫ a = maxCurry f.left := pullback.lift_fst _ _ _
  have hP' : P' ≫ a' = maxCurry (f.left ≫ g.left) := pullback.lift_fst _ _ _
  have hT : T ≫ a' = a ≫ mappingComplexPost .maximal X.left g.left := relativeMappingPost_fst _ _ _ _ _ _
  apply (IsPullback.of_hasPullback (mappingComplexPost .maximal X.left Y'.hom)
    (mappingBasePoint .maximal X.hom)).hom_ext
  · change P' ≫ a' = (P ≫ T) ≫ a'
    calc
      _ = maxCurry (f.left ≫ g.left) := hP'
      _ = maxCurry f.left ≫ mappingComplexPost .maximal X.left g.left := maxCurry_post f.left g.left
      _ = (P ≫ a) ≫ mappingComplexPost .maximal X.left g.left := congrArg (fun t => t ≫ _) hP.symm
      _ = P ≫ (a ≫ mappingComplexPost .maximal X.left g.left) := Category.assoc _ _ _
      _ = P ≫ (T ≫ a') := congrArg (fun t => P ≫ t) hT.symm
      _ = _ := (Category.assoc _ _ _).symm
  · change P' ≫ b' = (P ≫ T) ≫ b'
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The original parameter tensor and relative mapping complex form the genuine adjunction over the supplied base. -/
def overParameterAdjunction (Z : Marked.{u}) (X : Over Z) :
    overParameterFunctor Z X ⊣ overTargetMappingFunctor .maximal Z X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun K Y => overParameterHomEquiv Z X K Y
      homEquiv_naturality_left_symm := by
        intro K' K Y a g
        exact overParameterHomEquiv_symm_pre Z X Y a g
      homEquiv_naturality_right := by
        intro K Y Y' f g
        exact overParameterHomEquiv_post Z X K f g }

/-- Universal slice evaluation uses exactly the original marked relative evaluation map. -/
theorem overParameterAdjunction_counit_left (Z : Marked.{u}) (X Y : Over Z) :
    ((overParameterAdjunction Z X).counit.app Y).left = relativeEvaluation X.hom Y.hom := by
  let c : relativeMappingComplex .maximal X.hom Y.hom ⟶ mappingComplex .maximal X.left Y.left :=
    pullback.fst (mappingComplexPost .maximal X.left Y.hom) (mappingBasePoint .maximal X.hom)
  change maxUncurry (𝟙 (relativeMappingComplex .maximal X.hom Y.hom) ≫ c) = maxUncurry c
  exact congrArg maxUncurry (Category.id_comp c)

/-- The genuine original slice parameter tensor preserves colimits through its actual adjunction. -/
theorem overParameter_preservesColimits (Z : Marked.{u}) (X : Over Z) :
    PreservesColimitsOfSize.{u, u} (overParameterFunctor Z X) :=
  (overParameterAdjunction Z X).leftAdjoint_preservesColimits

end SSet.Marked
