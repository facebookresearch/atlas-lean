/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.ScalarTensor
public import MathlibExt.CategoryTheory.Enriched.ScalarCotensor
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Actual scalar tensor-cotensor adjunction and Leibniz corners

Both directions keep the original full enriched Hom actions and native
component curry/uncurry maps. The index is plain enriched.
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

private theorem tensorMap_leftComponents
    (M : V) (F G : EnrichedFunctorCat V A)
    (f : tensorLeftObject M F ⟶ G) (a b : A) :
    (α_ M (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
        (M ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)) ≫ component f b =
      (component f a ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b) := by
  have h := f.uncurriedNaturality a b
  change MonoidalClosed.uncurry
      ((tensorLeftObject M F).toEnrichedFunctor.map a b) ≫ component f b =
    (component f a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b) at h
  rw [tensorHom_id] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ component f b)
      (tensorLeftObject_map_uncurry M F a b).symm).trans h)

/-- The actual scalar adjunct uses original component curry maps and
their full enriched Hom naturality. -/
@[no_expose]
def adjunct (M : V) (F G : EnrichedFunctorCat V A)
    (f : tensorLeftObject M F ⟶ G) : F ⟶ cotensorObject M G :=
  cotensorOfLeftComponents M F G (component f) (tensorMap_leftComponents M F G f)

/-- The adjunct's component is the literal original native curry. -/
theorem adjunct_component (M : V) (F G : EnrichedFunctorCat V A)
    (f : tensorLeftObject M F ⟶ G) (a : A) :
    component (adjunct M F G f) a = MonoidalClosed.curry (component f a) :=
  cotensorOfLeftComponents_component _ _ _ _ _ a

private theorem cotensorMap_tensorComponents
    (M : V) (F G : EnrichedFunctorCat V A) (t : F ⟶ cotensorObject M G) (a b : A) :
    MonoidalClosed.uncurry
        ((tensorLeftObject M F).toEnrichedFunctor.map a b) ≫
      MonoidalClosed.uncurry (component t b) =
    (MonoidalClosed.uncurry (component t a) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b) := by
  have h := cotensorComponent_naturality M F G t a b
  change (α_ M (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
      (M ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)) ≫
      MonoidalClosed.uncurry (component t b) =
    (MonoidalClosed.uncurry (component t a) ▷ (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b) at h
  rw [tensorHom_id]
  exact (congrArg (fun q => q ≫ MonoidalClosed.uncurry (component t b))
    (tensorLeftObject_map_uncurry M F a b)).trans ((Category.assoc _ _ _).trans h)

/-- The actual inverse scalar adjunct uses original component
uncurry maps with the proved complete source Hom equations. -/
@[no_expose]
def unadjunct (M : V) (F G : EnrichedFunctorCat V A)
    (t : F ⟶ cotensorObject M G) : tensorLeftObject M F ⟶ G :=
  GradedNatTrans.unitOfComponents (fun a => MonoidalClosed.uncurry (component t a))
    (cotensorMap_tensorComponents M F G t)

/-- The inverse adjunct keeps its literal component uncurry. -/
theorem unadjunct_component (M : V) (F G : EnrichedFunctorCat V A)
    (t : F ⟶ cotensorObject M G) (a : A) :
    component (unadjunct M F G t) a = MonoidalClosed.uncurry (component t a) :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The full original tensor map is recovered. -/
theorem unadjunct_adjunct (M : V) (F G : EnrichedFunctorCat V A)
    (f : tensorLeftObject M F ⟶ G) : unadjunct M F G (adjunct M F G f) = f := by
  apply hom_ext
  intro a
  rw [unadjunct_component, adjunct_component]
  exact MonoidalClosed.uncurry_curry (component f a)

/-- The full original cotensor map is recovered. -/
theorem adjunct_unadjunct (M : V) (F G : EnrichedFunctorCat V A)
    (t : F ⟶ cotensorObject M G) : adjunct M F G (unadjunct M F G t) = t := by
  apply hom_ext
  intro a
  rw [adjunct_component, unadjunct_component, MonoidalClosed.curry_uncurry]

/-- The entire scalar tensor/cotensor Hom correspondence. -/
@[no_expose]
def homEquiv (M : V) (F G : EnrichedFunctorCat V A) :
    (tensorLeftObject M F ⟶ G) ≃ (F ⟶ cotensorObject M G) where
  toFun := adjunct M F G
  invFun := unadjunct M F G
  left_inv := unadjunct_adjunct M F G
  right_inv := adjunct_unadjunct M F G

/-- Applying the scalar Hom correspondence gives the original adjunct. -/
@[simp]
theorem homEquiv_apply (M : V) (F G : EnrichedFunctorCat V A)
    (f : tensorLeftObject M F ⟶ G) :
    homEquiv M F G f = adjunct M F G f := by
  rfl

/-- Applying its inverse gives the original unadjunct. -/
@[simp]
theorem homEquiv_symm_apply (M : V) (F G : EnrichedFunctorCat V A)
    (t : F ⟶ cotensorObject M G) :
    (homEquiv M F G).symm t = unadjunct M F G t := by
  rfl

/-- Adjunction naturality retains arbitrary original diagram source maps. -/
theorem adjunct_source (M : V) {F F' G : EnrichedFunctorCat V A}
    (j : F' ⟶ F) (f : tensorLeftObject M F ⟶ G) :
    adjunct M F' G (tensorLeftMap M j ≫ f) = j ≫ adjunct M F G f := by
  apply hom_ext
  intro a
  rw [adjunct_component, component_comp, tensorLeftMap_component,
    component_comp, adjunct_component]
  exact MonoidalClosed.curry_natural_left (component j a) (component f a)

/-- Adjunction naturality retains arbitrary original diagram target maps. -/
theorem adjunct_target (M : V) {F G G' : EnrichedFunctorCat V A}
    (f : tensorLeftObject M F ⟶ G) (p : G ⟶ G') :
    adjunct M F G' (f ≫ p) = adjunct M F G f ≫ cotensorMap M p := by
  apply hom_ext
  intro a
  rw [adjunct_component, component_comp, component_comp,
    adjunct_component, cotensorMap_component]
  exact MonoidalClosed.curry_natural_right (component f a) (component p a)

/-- Inverse adjunct source naturality uses the same original unit
transformation and literal uncurried component maps. -/
theorem unadjunct_source (M : V) {F F' G : EnrichedFunctorCat V A}
    (j : F' ⟶ F) (t : F ⟶ cotensorObject M G) :
    unadjunct M F' G (j ≫ t) = tensorLeftMap M j ≫ unadjunct M F G t := by
  apply hom_ext
  intro a
  rw [unadjunct_component, component_comp, component_comp,
    tensorLeftMap_component, unadjunct_component]
  exact MonoidalClosed.uncurry_natural_left (component j a) (component t a)

/-- Fixed scalar tensor is genuinely left adjoint to the original
pointwise cotensor functor. -/
@[no_expose]
def adjunction (M : V) :
    EnrichedFunctorCat.tensorLeft (V := V) (A := A) M ⊣ cotensor M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv M
      homEquiv_naturality_left_symm j f := unadjunct_source M j f
      homEquiv_naturality_right f p := adjunct_target M f p }

/-- The full ordinary adjunction uses its original entire scalar
tensor-cotensor Hom correspondence. -/
theorem adjunction_homEquiv (M : V) (F G : EnrichedFunctorCat V A) :
    (adjunction M).homEquiv F G = homEquiv M F G := by
  unfold adjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]

/-- The adjunction applies through the original scalar adjunct API. -/
@[simp]
theorem adjunction_homEquiv_apply (M : V) (F G : EnrichedFunctorCat V A)
    (f : tensorLeftObject M F ⟶ G) :
    (adjunction M).homEquiv F G f = adjunct M F G f := by
  have h := congrArg
    (fun e : (tensorLeftObject M F ⟶ G) ≃ (F ⟶ cotensorObject M G) ↦ e f)
    (adjunction_homEquiv M F G)
  exact h.trans (homEquiv_apply M F G f)

/-- The inverse adjunction applies through the original unadjunct API. -/
@[simp]
theorem adjunction_homEquiv_symm_apply (M : V) (F G : EnrichedFunctorCat V A)
    (t : F ⟶ cotensorObject M G) :
    ((adjunction M).homEquiv F G).symm t = unadjunct M F G t := by
  have h := congrArg
    (fun e : (tensorLeftObject M F ⟶ G) ≃ (F ⟶ cotensorObject M G) ↦ e.symm t)
    (adjunction_homEquiv M F G)
  exact h.trans (homEquiv_symm_apply M F G t)

end CategoryTheory.EnrichedFunctorCat.ScalarLeibniz
