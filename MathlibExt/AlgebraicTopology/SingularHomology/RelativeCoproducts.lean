/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.Coproducts
public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeHomology
public import MathlibExt.CategoryTheory.Limits.Shapes.CokernelAdjunction
public import MathlibExt.Topology.Category.TopPair.CoproductColimits

/-!
# Coproducts of relative singular chain complexes

The relative singular chain functor preserves coproducts of topological pairs.
The canonical coproduct comparison isomorphism commutes with each pair
inclusion.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicTopology

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

variable {J : Type w} (P : J → TopPair.{w}) (R : C)

noncomputable def singularPairChainArrowMapSigmaCofanIsColimit :
    IsColimit ((singularPairChainArrowFunctor C R).mapCocone
      (TopPair.sigmaCofan P)) := by
  let chain := (singularChainComplexFunctor (C := C)).obj R
  have hProjSnd : IsColimit (TopPair.proj₂.mapCocone (TopPair.sigmaCofan P)) :=
    (Cofan.isColimitMapCoconeEquiv TopPair.proj₂ P (TopPair.sigmaCofan P)).symm
      (coproductIsCoproduct _)
  have hProjFst : IsColimit (TopPair.proj₁.mapCocone (TopPair.sigmaCofan P)) :=
    (Cofan.isColimitMapCoconeEquiv TopPair.proj₁ P (TopPair.sigmaCofan P)).symm
      (coproductIsCoproduct _)
  have hLeft : IsColimit
      ((Arrow.leftFunc).mapCocone
        ((singularPairChainArrowFunctor C R).mapCocone
          (TopPair.sigmaCofan P))) := by
    change IsColimit ((TopPair.proj₂ ⋙ chain).mapCocone
      (TopPair.sigmaCofan P))
    have hEq : (TopPair.proj₂ ⋙ chain).mapCocone
        (TopPair.sigmaCofan P) =
        chain.mapCocone (TopPair.proj₂.mapCocone
          (TopPair.sigmaCofan P)) := rfl
    rw [hEq]
    exact isColimitOfPreserves chain hProjSnd
  have hRight : IsColimit
      ((Arrow.rightFunc).mapCocone
        ((singularPairChainArrowFunctor C R).mapCocone
          (TopPair.sigmaCofan P))) := by
    change IsColimit ((TopPair.proj₁ ⋙ chain).mapCocone
      (TopPair.sigmaCofan P))
    have hEq : (TopPair.proj₁ ⋙ chain).mapCocone
        (TopPair.sigmaCofan P) =
        chain.mapCocone (TopPair.proj₁.mapCocone
          (TopPair.sigmaCofan P)) := rfl
    rw [hEq]
    exact isColimitOfPreserves chain hProjFst
  exact Comma.fstSndJointlyReflectColimit hLeft hRight

noncomputable def relativeSingularChainMapSigmaCofanIsColimit :
    IsColimit ((relativeSingularChainFunctor C R).mapCocone
      (TopPair.sigmaCofan P)) := by
  have hArrow := singularPairChainArrowMapSigmaCofanIsColimit (C := C) P R
  let cokerF := Limits.coker (C := ChainComplex C ℕ)
  haveI : PreservesColimitsOfShape (Discrete J) cokerF :=
    (Limits.cokerAdjunction (C := ChainComplex C ℕ)).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have hCoker : IsColimit (cokerF.mapCocone
      ((singularPairChainArrowFunctor C R).mapCocone
        (TopPair.sigmaCofan P))) :=
    isColimitOfPreserves cokerF hArrow
  change IsColimit
    ((singularPairChainArrowFunctor C R ⋙ cokerF).mapCocone
      (TopPair.sigmaCofan P))
  exact hCoker

instance relativeSingularChainFunctor_preservesColimit_discrete :
    PreservesColimit (Discrete.functor P)
      (relativeSingularChainFunctor C R) :=
  preservesColimit_of_preserves_colimit_cocone
    (TopPair.sigmaCofanIsColimit P)
    (relativeSingularChainMapSigmaCofanIsColimit P R)

instance relativeSingularChainFunctor_preservesColimitsOfShape_discrete :
    PreservesColimitsOfShape (Discrete J)
      (relativeSingularChainFunctor C R) :=
  preservesColimitsOfShape_of_discrete _

noncomputable def relativeSingularChainSigmaIso :
    (∐ fun j => (relativeSingularChainFunctor C R).obj (P j)) ≅
      (relativeSingularChainFunctor C R).obj (TopPair.sigma P) :=
  (PreservesCoproduct.iso (relativeSingularChainFunctor C R) P).symm ≪≫
    (relativeSingularChainFunctor C R).mapIso (TopPair.sigmaIsoSigma P)

@[reassoc (attr := simp)]
theorem relativeSingularChainSigmaIso_hom_ι (j : J) :
    Sigma.ι (fun j => (relativeSingularChainFunctor C R).obj (P j)) j ≫
      (relativeSingularChainSigmaIso P R).hom =
      (relativeSingularChainFunctor C R).map (TopPair.sigmaι P j) := by
  rw [relativeSingularChainSigmaIso, Iso.trans_hom, Functor.mapIso_hom]
  change Sigma.ι _ j ≫ (PreservesCoproduct.iso (relativeSingularChainFunctor C R) P).inv ≫
      (relativeSingularChainFunctor C R).map (TopPair.sigmaIsoSigma P).hom = _
  rw [PreservesCoproduct.inv_hom]
  rw [← Category.assoc]
  rw [Limits.ι_comp_sigmaComparison]
  rw [← (relativeSingularChainFunctor C R).map_comp, TopPair.sigmaIsoSigma_hom_ι]

end AlgebraicTopology
