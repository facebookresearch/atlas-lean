/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceAdjunction

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.JoinSliceAdjunctionTest

variable {K X A : SSet.{u}} (f : K ⟶ X)

example (φ : A ⟶ SSet.sliceUnder X f) :
    (SSet.sliceUnder.homEquiv X f A φ).1 =
      (SSet.join.obj K).map φ ≫ SSet.sliceUnder.evaluation X f := by
  rw [SSet.sliceUnder.homEquiv_apply]

example (g : { h : K ⋆ A ⟶ X // SSet.joinInl K A ≫ h = f }) :
    (SSet.sliceUnder.homEquiv X f A).symm g =
      SSet.sliceUnder.lift f g :=
  SSet.sliceUnder.homEquiv_symm_apply X f A g

example (g : { h : K ⋆ A ⟶ X // SSet.joinInl K A ≫ h = f }) :
    SSet.sliceUnder.homEquiv X f A
        ((SSet.sliceUnder.homEquiv X f A).symm g) = g :=
  (SSet.sliceUnder.homEquiv X f A).apply_symm_apply g

example :
    SSet.joinInl K (SSet.sliceUnder X f) ≫
        SSet.sliceUnder.evaluation X f = f :=
  SSet.sliceUnder.joinInl_evaluation X f

example :
    SSet.joinInr K (SSet.sliceUnder X f) ≫
        SSet.sliceUnder.evaluation X f = SSet.sliceUnder.proj X f :=
  SSet.sliceUnder.joinInr_evaluation X f

example (n : SimplexCategory) (g : (SSet.sliceUnder X f).obj (op n)) :
    (SSet.join.obj K).map (SSet.yonedaEquiv.symm g) ≫
        SSet.sliceUnder.evaluation X f = g.1 :=
  SSet.sliceUnder.evaluation_wholeMap X f n g

example (φ : A ⟶ SSet.sliceOver X f) :
    (SSet.sliceOver.homEquiv X f A φ).1 =
      (SSet.join.map φ).app K ≫ SSet.sliceOver.evaluation X f := by
  rw [SSet.sliceOver.homEquiv_apply]

example (g : { h : A ⋆ K ⟶ X // SSet.joinInr A K ≫ h = f }) :
    (SSet.sliceOver.homEquiv X f A).symm g =
      SSet.sliceOver.lift f g :=
  SSet.sliceOver.homEquiv_symm_apply X f A g

example (g : { h : A ⋆ K ⟶ X // SSet.joinInr A K ≫ h = f }) :
    SSet.sliceOver.homEquiv X f A
        ((SSet.sliceOver.homEquiv X f A).symm g) = g :=
  (SSet.sliceOver.homEquiv X f A).apply_symm_apply g

example :
    SSet.joinInl (SSet.sliceOver X f) K ≫
        SSet.sliceOver.evaluation X f = SSet.sliceOver.proj X f :=
  SSet.sliceOver.joinInl_evaluation X f

example :
    SSet.joinInr (SSet.sliceOver X f) K ≫
        SSet.sliceOver.evaluation X f = f :=
  SSet.sliceOver.joinInr_evaluation X f

example (n : SimplexCategory) (g : (SSet.sliceOver X f).obj (op n)) :
    (SSet.join.map (SSet.yonedaEquiv.symm g)).app K ≫
        SSet.sliceOver.evaluation X f = g.1 :=
  SSet.sliceOver.evaluation_wholeMap X f n g

example (P : Under K) (q : (SSet.joinUnder K).obj A ⟶ P) :
    SSet.joinUnderHomEquiv K A P q =
      (SSet.sliceUnder.homEquiv P.right P.hom A).symm
        ⟨q.right, q.w⟩ :=
  SSet.joinUnderHomEquiv_apply K A P q

example (P : Under K) (q : (SSet.joinOver K).obj A ⟶ P) :
    SSet.joinOverHomEquiv K A P q =
      (SSet.sliceOver.homEquiv P.right P.hom A).symm
        ⟨q.right, q.w⟩ :=
  SSet.joinOverHomEquiv_apply K A P q

example : SSet.joinUnder K ⊣ SSet.joinLeftDivision K :=
  SSet.joinUnderAdjunction K

example : SSet.joinOver K ⊣ SSet.joinRightDivision K :=
  SSet.joinOverAdjunction K

example (Y : SSet.{u}) :
    (SSet.sliceUnder.initialIso Y).hom =
      SSet.sliceUnder.proj Y (initial.to Y) :=
  SSet.sliceUnder.initialIso_hom Y

example (Y : SSet.{u}) :
    (SSet.sliceOver.initialIso Y).hom =
      SSet.sliceOver.proj Y (initial.to Y) :=
  SSet.sliceOver.initialIso_hom Y

example {Y Z : SSet.{u}} (p : Y ⟶ Z) :
    SSet.sliceUnder.initialMap p ≫
        (SSet.sliceUnder.initialIso Z).hom =
      (SSet.sliceUnder.initialIso Y).hom ≫ p := by
  simpa using SSet.sliceUnder.initialMap_comp_proj p

example {Y Z : SSet.{u}} (p : Y ⟶ Z) :
    SSet.sliceOver.initialMap p ≫
        (SSet.sliceOver.initialIso Z).hom =
      (SSet.sliceOver.initialIso Y).hom ≫ p := by
  simpa using SSet.sliceOver.initialMap_comp_proj p

example (Y : SSet.{u}) :
    SSet.sliceUnder.initialNatIso.hom.app Y =
      (SSet.sliceUnder.initialIso Y).hom := rfl

example (Y : SSet.{u}) :
    SSet.sliceOver.initialNatIso.hom.app Y =
      (SSet.sliceOver.initialIso Y).hom := rfl

end MathlibExtTest.AlgebraicTopology.SimplicialSet.JoinSliceAdjunctionTest
