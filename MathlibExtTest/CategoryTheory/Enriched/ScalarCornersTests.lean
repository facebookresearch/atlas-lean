/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Enriched.ScalarCorners

/-!
# Public scalar adjunction and corner API checks

These tests use arbitrary enriched diagrams. They check contravariant scalar
composition, the actual parametrized Hom correspondence and Arrow bijection,
and evaluation of supplied pullback corners with only base pullbacks.
-/

set_option autoImplicit false
noncomputable section
universe uA uV vV

open CategoryTheory Limits Opposite MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace MathlibExtTest.ScalarCorners

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

example (M : V) (F : EnrichedFunctorCat V A) :
    ((ScalarLeibniz.cotensorBifunctor (V := V) (A := A)).obj (op M)).obj F =
      cotensorObject M F := rfl

example {M N P : V} (i : M ⟶ N) (j : N ⟶ P) (F : EnrichedFunctorCat V A) :
    ((ScalarLeibniz.cotensorBifunctor (V := V) (A := A)).map (i ≫ j).op).app F =
      ((ScalarLeibniz.cotensorBifunctor (V := V) (A := A)).map j.op).app F ≫
        ((ScalarLeibniz.cotensorBifunctor (V := V) (A := A)).map i.op).app F :=
  cotensorScalarMap_comp i j F

example (M : V) (F G : EnrichedFunctorCat V A) :
    (tensorLeftObject M F ⟶ G) ≃ (F ⟶ cotensorObject M G) :=
  ScalarLeibniz.parametrizedAdjunction.homEquiv

example (M : V) (F G : EnrichedFunctorCat V A)
    (f : tensorLeftObject M F ⟶ G) (a : A) :
    component (ScalarLeibniz.parametrizedAdjunction.homEquiv f) a =
      MonoidalClosed.curry (component f a) := by
  change component ((ScalarLeibniz.adjunction M).homEquiv F G f) a = _
  rw [ScalarLeibniz.adjunction_homEquiv]
  exact ScalarLeibniz.adjunct_component M F G f a

example (M : V) (F G : EnrichedFunctorCat V A)
    (f : tensorLeftObject M F ⟶ G) :
    ScalarLeibniz.parametrizedAdjunction.homEquiv.symm
        (ScalarLeibniz.parametrizedAdjunction.homEquiv f) = f :=
  ScalarLeibniz.parametrizedAdjunction.homEquiv.symm_apply_apply f

example {M N : V} (i : M ⟶ N) (F G : EnrichedFunctorCat V A)
    (f : tensorLeftObject N F ⟶ G) :
    ScalarLeibniz.parametrizedAdjunction.homEquiv (scalarTensorMap i F ≫ f) =
      ScalarLeibniz.parametrizedAdjunction.homEquiv f ≫ cotensorScalarMap i G :=
  ScalarLeibniz.parametrizedAdjunction.homEquiv_naturality_one i f

example [HasPushouts V] : HasPushouts (EnrichedFunctorCat V A) := inferInstance

example [HasPullbacks V] : HasPullbacks (EnrichedFunctorCat V A) := inferInstance

example [HasPushouts V] {M N : V} (i : M ⟶ N)
    {F G : EnrichedFunctorCat V A} (j : F ⟶ G) :
    (ScalarLeibniz.tensorBifunctor (V := V) (A := A)).PushoutObjObj i j :=
  ScalarLeibniz.pushoutSquare i j

example [HasPullbacks V] {M N : V} (i : M ⟶ N)
    {F G : EnrichedFunctorCat V A} (p : F ⟶ G) :
    (ScalarLeibniz.cotensorBifunctor (V := V) (A := A)).PullbackObjObj i p :=
  ScalarLeibniz.pullbackSquare i p

section PullbackEvaluation

variable [HasPullbacks V] {M N : V} (i : M ⟶ N)
  {F G : EnrichedFunctorCat V A} (p : F ⟶ G)
  (sq : (ScalarLeibniz.cotensorBifunctor (V := V) (A := A)).PullbackObjObj i p)
  (a : A)

example : (ScalarLeibniz.evaluatedPullbackSquare i p sq a).fst =
    component sq.fst a := rfl

example : (ScalarLeibniz.evaluatedPullbackSquare i p sq a).snd =
    component sq.snd a := rfl

example : (ScalarLeibniz.evaluatedPullbackSquare i p sq a).π =
    component sq.π a := ScalarLeibniz.evaluatedPullbackSquare_π i p sq a

example : IsPullback (component sq.fst a) (component sq.snd a)
    ((ihom M).map (component p a))
      ((MonoidalClosed.pre i).app (G.toEnrichedFunctor.obj a)) := by
  exact (ScalarLeibniz.evaluatedPullbackSquare i p sq a).isPullback

example : component sq.π a ≫ component sq.fst a =
    (MonoidalClosed.pre i).app (F.toEnrichedFunctor.obj a) :=
  (ScalarLeibniz.evaluatedPullbackSquare i p sq a).π_fst

example : component sq.π a ≫ component sq.snd a = (ihom N).map (component p a) :=
  (ScalarLeibniz.evaluatedPullbackSquare i p sq a).π_snd

end PullbackEvaluation

section ArrowCorrespondence

variable {M N : V} {i : M ⟶ N}
  {F G X Y : EnrichedFunctorCat V A} {j : F ⟶ G} {p : X ⟶ Y}
  (po : (ScalarLeibniz.tensorBifunctor (V := V) (A := A)).PushoutObjObj i j)
  (pb : (ScalarLeibniz.cotensorBifunctor (V := V) (A := A)).PullbackObjObj i p)

example : (Arrow.mk po.ι ⟶ Arrow.mk p) ≃ (Arrow.mk j ⟶ Arrow.mk pb.π) :=
  ScalarLeibniz.arrowHomEquiv po pb

example (f : Arrow.mk po.ι ⟶ Arrow.mk p) :
    (ScalarLeibniz.arrowHomEquiv po pb).symm
      (ScalarLeibniz.arrowHomEquiv po pb f) = f :=
  (ScalarLeibniz.arrowHomEquiv po pb).symm_apply_apply f

example : HasLiftingProperty po.ι p ↔ HasLiftingProperty j pb.π :=
  ScalarLeibniz.parametrizedAdjunction.hasLiftingProperty_iff po pb

end ArrowCorrespondence

end MathlibExtTest.ScalarCorners
