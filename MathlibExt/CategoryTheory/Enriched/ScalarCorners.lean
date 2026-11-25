/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.ScalarLeibniz
public import MathlibExt.CategoryTheory.Enriched.ScalarTensorBifunctor
public import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Full scalar bifunctors, actual parametrized adjunction and evaluated corners

The scalar and diagram maps are the original maps. Evaluation carries the
complete cotensor pullback corner to the original base internal-Hom corner.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uA uV vV

open CategoryTheory Limits Opposite MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.ScalarLeibniz

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- Reuse the complete scalar tensor bifunctor with all original scalar
and diagram transformations. -/
abbrev tensorBifunctor : V ⥤ EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V A :=
  EnrichedFunctorCat.tensorBifunctor (V := V) (A := A)

/-- The genuine scalar cotensor bifunctor retains original full
contravariant coefficient maps and all diagram maps. -/
def cotensorBifunctor : Vᵒᵖ ⥤ EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V A where
  obj M := cotensor M.unop
  map h :=
    { app F := cotensorScalarMap h.unop F
      naturality _ _ j := cotensorScalarMap_naturality h.unop j }
  map_id M := by
    apply NatTrans.ext
    funext F
    exact cotensorScalarMap_id M.unop F
  map_comp h k := by
    apply NatTrans.ext
    funext F
    exact cotensorScalarMap_comp k.unop h.unop F

/-- Coefficient naturality keeps the actual original curry and
precomposition maps on every component. -/
theorem adjunct_scalar {M N : V} (h : M ⟶ N)
    (F G : EnrichedFunctorCat V A) (f : tensorLeftObject N F ⟶ G) :
    adjunct M F G (scalarTensorMap h F ≫ f) =
      adjunct N F G f ≫ cotensorScalarMap h G := by
  apply hom_ext
  intro a
  rw [adjunct_component, component_comp, scalarTensorMap_component,
    component_comp, adjunct_component, cotensorScalarMap_component]
  exact (MonoidalClosed.curry_pre_app h (component f a)).symm

/-- The complete scalar family is an actual parametrized adjunction. -/
def parametrizedAdjunction :
    tensorBifunctor (V := V) (A := A) ⊣₂ cotensorBifunctor :=
  ParametrizedAdjunction.mk' (fun M => adjunction M) (by
    intro M N h F G f
    change (adjunction M).homEquiv F G (scalarTensorMap h F ≫ f) =
      (adjunction N).homEquiv F G f ≫ cotensorScalarMap h G
    let f₀ : tensorLeftObject N F ⟶ G := f
    have hM := adjunction_homEquiv_apply M F G (scalarTensorMap h F ≫ f₀)
    have hN := adjunction_homEquiv_apply N F G f₀
    exact hM.trans ((adjunct_scalar h F G f₀).trans
      (congrArg (fun t => t ≫ cotensorScalarMap h G) hN.symm)))

/-- The actual scalar pushout-product square uses the original scalar
map, original diagram map, and both canonical pushout injections. -/
def pushoutSquare [HasPushouts (EnrichedFunctorCat V A)]
    {M N : V} (i : M ⟶ N) {F G : EnrichedFunctorCat V A} (j : F ⟶ G) :
    tensorBifunctor.PushoutObjObj i j :=
  Functor.PushoutObjObj.ofHasPushout tensorBifunctor i j

/-- The actual cotensor pullback corner uses the original scalar
precomposition and diagram maps with both canonical projections. -/
def pullbackSquare [HasPullbacks (EnrichedFunctorCat V A)]
    {M N : V} (i : M ⟶ N) {F G : EnrichedFunctorCat V A} (p : F ⟶ G) :
    cotensorBifunctor.PullbackObjObj i p :=
  Functor.PullbackObjObj.ofHasPullback cotensorBifunctor i p

/-- Evaluation of any genuine enriched cotensor corner is the base
internal-Hom corner on the same original coefficient and component maps. -/
def evaluatedPullbackSquare [HasPullbacks V]
    {M N : V} (i : M ⟶ N) {F G : EnrichedFunctorCat V A} (p : F ⟶ G)
    (sq : cotensorBifunctor.PullbackObjObj i p) (a : A) :
    MonoidalClosed.internalHom.PullbackObjObj i (component p a) where
  pt := sq.pt.toEnrichedFunctor.obj a
  fst := component sq.fst a
  snd := component sq.snd a
  isPullback := by
    have h := (evaluation a).map_isPullback sq.isPullback
    change IsPullback (component sq.fst a) (component sq.snd a)
      (component (cotensorMap M p) a)
      (component (cotensorScalarMap i G) a) at h
    rw [cotensorMap_component, cotensorScalarMap_component] at h
    exact h
  π := component sq.π a
  π_fst := by
    have h := congrArg (fun t => component t a) sq.π_fst
    change component (sq.π ≫ sq.fst) a = component (cotensorScalarMap i F) a at h
    rw [component_comp, cotensorScalarMap_component] at h
    exact h
  π_snd := by
    have h := congrArg (fun t => component t a) sq.π_snd
    change component (sq.π ≫ sq.snd) a = component (cotensorMap N p) a at h
    rw [component_comp, cotensorMap_component] at h
    exact h

/-- The evaluated corner map is literally the original component map. -/
theorem evaluatedPullbackSquare_π [HasPullbacks V]
    {M N : V} (i : M ⟶ N) {F G : EnrichedFunctorCat V A} (p : F ⟶ G)
    (sq : cotensorBifunctor.PullbackObjObj i p) (a : A) :
    (evaluatedPullbackSquare i p sq a).π = component sq.π a := rfl

/-- The actual whole Arrow correspondence keeps the original pushout
legs and pullback projections in both directions. -/
def arrowHomEquiv {M N : V} {i : M ⟶ N}
    {F G X Y : EnrichedFunctorCat V A} {j : F ⟶ G} {p : X ⟶ Y}
    (po : tensorBifunctor.PushoutObjObj i j)
    (pb : cotensorBifunctor.PullbackObjObj i p) :
    (Arrow.mk po.ι ⟶ Arrow.mk p) ≃ (Arrow.mk j ⟶ Arrow.mk pb.π) :=
  parametrizedAdjunction.arrowHomEquiv po pb

end CategoryTheory.EnrichedFunctorCat.ScalarLeibniz
