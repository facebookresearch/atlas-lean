/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Monad.BarFunctorial

/-!
# Genuine outer-whiskering consumer tests

Tiny public-contract coverage for the genuine outer-whiskering isomorphisms in
`BarFunctorial`: degree components for target/source whiskering with whiskered
genuine-bar sources, two module-morphism naturality squares, unitor/associator
orientation checks, and four bundled no-degree identity/composition coherence
laws. Uses only public declarations; no production coherence proof is
duplicated. The whiskered (`...WhiskerIso`) statements detect omitted promotion
or flipped associator orientation.
-/

namespace CategoryTheory.Monad.BarFunctorialTests

open CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}
variable {B : Type u₄} [Category.{v₄} B] (H : B ⥤ A)
variable {E : Type u₄} [Category.{v₄} E] (K : D ⥤ E)

-- Genuine target-postcomposition degree component with whiskered source.
example (n : ℕ) :
    (twoSidedBarPostcompWhiskerIso K R L).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (barDataPostcompOuterIsoObj K R L n).hom :=
  twoSidedBarPostcompWhiskerIso_hom_app_op_mk K R L n

-- Genuine source-precomposition degree component with whiskered source.
example (n : ℕ) :
    (twoSidedBarPrecompWhiskerIso H R L).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (barDataPrecompOuterIsoObj H R L n).hom :=
  twoSidedBarPrecompWhiskerIso_hom_app_op_mk H R L n

-- Naturality square under generic module morphisms (postcomposition side).
example {R R' : RightModule T D} {L L' : LeftModule A T}
    (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) :
    (((SimplicialObject.whiskering _ _).obj
        (functorPostcompOuter K)).map
          (twoSidedBarHom fR fL)).app (Opposite.op (SimplexCategory.mk n)) ≫
        (twoSidedBarPostcompWhiskerIso K R' L').hom.app
          (Opposite.op (SimplexCategory.mk n)) =
        (twoSidedBarPostcompWhiskerIso K R L).hom.app
          (Opposite.op (SimplexCategory.mk n)) ≫
        (twoSidedBarHom ((RightModule.postcompFunctor K).map fR) fL).app
          (Opposite.op (SimplexCategory.mk n)) :=
  twoSidedBarPostcompWhiskerIso_naturality_app_op_mk K fR fL n

-- Naturality square under generic module morphisms (precomposition side).
example {R R' : RightModule T D} {L L' : LeftModule A T}
    (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) :
    (((SimplicialObject.whiskering _ _).obj
        (functorPrecompOuter H)).map
          (twoSidedBarHom fR fL)).app (Opposite.op (SimplexCategory.mk n)) ≫
        (twoSidedBarPrecompWhiskerIso H R' L').hom.app
          (Opposite.op (SimplexCategory.mk n)) =
        (twoSidedBarPrecompWhiskerIso H R L).hom.app
          (Opposite.op (SimplexCategory.mk n)) ≫
        (twoSidedBarHom fR ((LeftModule.precompFunctor H).map fL)).app
          (Opposite.op (SimplexCategory.mk n)) :=
  twoSidedBarPrecompWhiskerIso_naturality_app_op_mk H fR fL n

-- Outer target-postcomposition identity pins the right unitor.
example (G : A ⥤ D) :
    (functorPostcompOuterId).hom.app G = (Functor.rightUnitor G).hom :=
  functorPostcompOuterId_hom_app G

-- Outer source-precomposition composition pins the reversed associator.
example (J : B ⥤ B) (G : A ⥤ D) :
    (functorPrecompOuterComp H J).hom.app G =
      (Functor.associator J H G).symm.hom :=
  functorPrecompOuterComp_hom_app H J G

-- Target-postcomposition identity coherence as a bundled NatTrans equality (no `n`).
example :
    (twoSidedBarPostcompWhiskerNatIso (T := T) (A := A) (E := D) (𝟭 D)).hom ≫
      twoSidedBarPostcompModuleIdNatIso.hom =
    (Functor.isoWhiskerLeft (twoSidedBarFunctor T)
      ((SimplicialObject.whiskering (A ⥤ D) (A ⥤ D)).mapIso
        functorPostcompOuterId)).hom ≫
      (Functor.rightUnitor _).hom :=
  twoSidedBarPostcompWhiskerNatIso_id

-- Source-precomposition identity coherence as a bundled NatTrans equality (no `n`).
example :
    (twoSidedBarPrecompWhiskerNatIso (T := T) (D := D) (𝟭 A)).hom ≫
      twoSidedBarPrecompModuleIdNatIso.hom =
    (Functor.isoWhiskerLeft (twoSidedBarFunctor T)
      ((SimplicialObject.whiskering (A ⥤ D) (A ⥤ D)).mapIso
        functorPrecompOuterId)).hom ≫
      (Functor.rightUnitor _).hom :=
  twoSidedBarPrecompWhiskerNatIso_id

-- Source-precomposition composition coherence pins contravariant `J ⋙ H` order (no `n`).
example (J : B ⥤ B) :
    (Functor.isoWhiskerRight (twoSidedBarPrecompWhiskerNatIso (T := T) (D := D) H)
      ((SimplicialObject.whiskering (B ⥤ D) (B ⥤ D)).obj (functorPrecompOuter J))).hom ≫
    (Functor.isoWhiskerLeft ((𝟭 (RightModule T D)).prod (LeftModule.precompFunctor (T := T) H))
      (twoSidedBarPrecompWhiskerNatIso (T := T) (D := D) J)).hom ≫
    (twoSidedBarPrecompModuleCompNatIso (T := T) (H := H) (J := J)).hom =
    (Functor.isoWhiskerLeft (twoSidedBarFunctor T)
      ((SimplicialObject.whiskering (A ⥤ D) (B ⥤ D)).mapIso
        (functorPrecompOuterComp H J))).hom ≫
    (twoSidedBarPrecompWhiskerNatIso (T := T) (D := D) (J ⋙ H)).hom :=
  twoSidedBarPrecompWhiskerNatIso_comp H J

-- Target-postcomposition composition coherence pins covariant `K ⋙ Q` order (no `n`).
example (Q : E ⥤ E) :
    (Functor.isoWhiskerRight (twoSidedBarPostcompWhiskerNatIso (T := T) (A := A) (E := E) K)
      ((SimplicialObject.whiskering (A ⥤ E) (A ⥤ E)).obj (functorPostcompOuter Q))).hom ≫
    (Functor.isoWhiskerLeft ((RightModule.postcompFunctor (T := T) K).prod (𝟭 (LeftModule A T)))
      (twoSidedBarPostcompWhiskerNatIso (T := T) (A := A) (E := E) Q)).hom ≫
    (twoSidedBarPostcompModuleCompNatIso (K := K) (Q := Q)).hom =
    (Functor.isoWhiskerLeft (twoSidedBarFunctor T)
      ((SimplicialObject.whiskering (A ⥤ D) (A ⥤ E)).mapIso
        (functorPostcompOuterComp K Q))).hom ≫
    (twoSidedBarPostcompWhiskerNatIso (T := T) (A := A) (E := E) (K ⋙ Q)).hom :=
  twoSidedBarPostcompWhiskerNatIso_comp K Q

end CategoryTheory.Monad.BarFunctorialTests
