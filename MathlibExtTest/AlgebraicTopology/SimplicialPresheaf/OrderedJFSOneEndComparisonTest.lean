/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneEndComparison
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open SimplicialPresheaf SimplicialPresheaf.OrderedJFS
private theorem retainedEndRoundtrips (A Z : Original.{u} 1) :
    (oneRawEndIso A Z).hom ≫ (oneRawEndIso A Z).inv = 𝟙 _ ∧
    (oneRawEndIso A Z).inv ≫ (oneRawEndIso A Z).hom = 𝟙 _ :=
  ⟨(oneRawEndIso A Z).hom_inv_id, (oneRawEndIso A Z).inv_hom_id⟩
private theorem retainedPrecompFourLegs {A B : Original.{u} 1}
    (f : A ⟶ B) (Z : Original.{u} 1) :
    (oneMappingPrecompArrowIso f Z).hom.left = (oneRawEndIso B Z).hom ∧
    (oneMappingPrecompArrowIso f Z).hom.right = (oneRawEndIso A Z).hom ∧
    (oneMappingPrecompArrowIso f Z).inv.left = (oneRawEndIso B Z).inv ∧
    (oneMappingPrecompArrowIso f Z).inv.right = (oneRawEndIso A Z).inv :=
  oneMappingPrecompArrowIso_legs f Z
private theorem retainedPrecompBothSquares {A B : Original.{u} 1}
    (f : A ⟶ B) (Z : Original.{u} 1) :
    (oneMappingPrecompArrowIso f Z).hom.left ≫
      innerHomPre (oneOriginalEquivalence.{u}.functor.map f)
        (oneOriginalEquivalence.{u}.functor.obj Z) =
      innerHomPre f Z ≫ (oneMappingPrecompArrowIso f Z).hom.right ∧
    (oneMappingPrecompArrowIso f Z).inv.left ≫ innerHomPre f Z =
      innerHomPre (oneOriginalEquivalence.{u}.functor.map f)
        (oneOriginalEquivalence.{u}.functor.obj Z) ≫ (oneMappingPrecompArrowIso f Z).inv.right :=
  ⟨(oneMappingPrecompArrowIso f Z).hom.w, (oneMappingPrecompArrowIso f Z).inv.w⟩
private theorem retainedEveryScalarOperator (A Z : Original.{u} 1)
    {n m : SimplexCategoryᵒᵖ} (theta : n ⟶ m) :
    (innerHom A Z).map theta ≫ (oneRawEndIso A Z).hom.app m =
      (oneRawEndIso A Z).hom.app n ≫
        (innerHom (oneOriginalEquivalence.{u}.functor.obj A)
          (oneOriginalEquivalence.{u}.functor.obj Z)).map theta :=
  (oneRawEndIso A Z).hom.naturality theta
