/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialSet/Pointed/Closed.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Smash.Basic

-- Currying and uncurrying are mutually inverse on simplices only after unfolding the basepoints
-- and the smash product of pointed simplicial sets and of pointed types, whose bodies are not
-- exposed.
import all MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Basic
import all MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Smash.Basic
import all MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Category.Pointed.Smash.Basic

/-!
# The pointed mapping simplicial set

For pointed simplicial sets `X` and `Y`, the pointed mapping simplicial set `Map_*(X, Y)` is the
subcomplex of the internal hom `[X, Y]` of the underlying simplicial sets consisting of the based
maps. An `n`-simplex of `[X, Y]` is a family of maps `X_m ⟶ Y_m` indexed by the `m`-simplices of
`Δ[n]` and natural in `m` (Mathlib's `Functor.HomObj`); it is based when every map of the family
sends the basepoint of `X` to the basepoint of `Y`. The basepoint of `Map_*(X, Y)` is the
constant map to the basepoint of `Y`.

Currying identifies based maps `X ∧ Y ⟶ Z` out of the smash product with based maps
`Y ⟶ Map_*(X, Z)`, naturally in `Y` and `Z`, so the smash product of pointed simplicial sets is a
closed monoidal structure. Consequently `X ∧ -` is a left adjoint and preserves all colimits; as
the smash product is symmetric, so is `- ∧ X`, by `Mathlib.CategoryTheory.Monoidal.Closed.Braided`.
Applied to the simplicial circle `S¹`, this gives the adjunction `S¹ ∧ - ⊣ Map_*(S¹, -)` between
simplicial suspension and loops.

## Main definitions

* `PointedSSet.basedMaps X Y`: the subcomplex of based maps in the internal hom
  `[X.right, Y.right]` of simplicial sets.
* `PointedSSet.ihom X`: the functor `Y ↦ Map_*(X, Y)`, acting by postcomposition.
* `PointedSSet.tensorHomEquiv X Y Z`: the currying bijection `(X ⊗ Y ⟶ Z) ≃ (Y ⟶ Map_*(X, Z))`.
* `PointedSSet.pointRestriction E K`: the constant family of maps to the basepoint of `E`.

## Main statements

* The instance `MonoidalClosed PointedSSet`, with right adjoint `PointedSSet.ihom X` to
  `tensorLeft X`.
* `PointedSSet.homEquiv_def`: its hom-set bijection is `PointedSSet.tensorHomEquiv`.
* Simplex-level descriptions of currying, uncurrying, evaluation and coevaluation.
* `PointedSSet.range_le_basedMaps_iff`: a family is based exactly when its restriction to the
  source basepoint is constant at the target basepoint.
* `PointedSSet.basedMaps_isPullback`: based maps are the fibre of restriction to the basepoint.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace MathlibExt.SpectraSource

namespace PointedSSet

variable (X Y Z : PointedSSet.{u})

/-- The based maps among the simplices of the internal hom `[X, Y]` of the underlying simplicial
sets: the `n`-simplices whose every component sends the basepoint of `X` to the basepoint
of `Y`. -/
def basedMaps : SSet.Subcomplex ((ihom X.right).obj Y.right) where
  obj n := {φ | ∀ m (f : n ⟶ m), φ.app m f (X.point m) = Y.point m}
  map g _ hφ m f := hφ m (g ≫ f)

variable {X Y Z}

@[simp]
lemma mem_basedMaps_iff {n : SimplexCategoryᵒᵖ} (φ : ((ihom X.right).obj Y.right).obj n) :
    φ ∈ (basedMaps X Y).obj n ↔ ∀ m (f : n ⟶ m), φ.app m f (X.point m) = Y.point m :=
  Iff.rfl

/-- A based simplex of the internal hom sends the basepoint to the basepoint. -/
@[simp]
lemma basedMaps_app_point {n m : SimplexCategoryᵒᵖ} (φ : (basedMaps X Y).obj n) (f : n ⟶ m) :
    φ.1.app m f (X.point m) = Y.point m :=
  φ.2 m f

variable (X Y)

/-- The constant map at the basepoint, as the basepoint of the simplicial set of based maps. -/
def basedMapsPoint : Δ[0] ⟶ (basedMaps X Y).toSSet where
  app _ := ↾fun _ ↦ ⟨Functor.HomObj.ofNatTrans (SSet.const (Y.point _)), fun _ _ ↦ by simp⟩

/-- The pointed mapping simplicial set `Map_*(X, Y)` of based maps, as a functor of `Y`; it
acts on based maps by postcomposition. -/
@[expose]
protected def ihom : PointedSSet.{u} ⥤ PointedSSet.{u} where
  obj Y := Under.mk (basedMapsPoint X Y)
  map {Y Y'} g := Under.homMk
    { app n := ↾fun φ ↦ ⟨φ.1.comp (.ofNatTrans g.right), (mem_basedMaps_iff _).2 fun m f ↦ by
        -- A simplex of `[X, Y]` is a `Functor.HomObj` only after unfolding Mathlib's internal
        -- hom, so `simp` cannot rewrite `Functor.HomObj.comp`; `change` states the component.
        change g.right.app m (φ.1.app m f (X.point m)) = _
        simp [basedMaps_app_point φ f]⟩
      naturality _ _ _ := rfl }
    (by
      ext n a
      apply Subtype.ext
      refine Functor.functorHom_ext fun m f ↦ ?_
      ext x
      simp [basedMapsPoint])

variable {X Y} in
/-- Two simplices of `Map_*(X, Y)` are equal when their components agree on every simplex. -/
@[ext]
lemma ihom_obj_right_ext {n : SimplexCategoryᵒᵖ} {φ ψ : ((PointedSSet.ihom X).obj Y).right.obj n}
    (h : ∀ m (f : n ⟶ m) x, (φ : (basedMaps X Y).obj n).1.app m f x =
      (ψ : (basedMaps X Y).obj n).1.app m f x) :
    φ = ψ :=
  Subtype.ext (Functor.functorHom_ext fun m f ↦ by ext x; exact h m f x)

variable {X Y} in
/-- The curried map `Y ⟶ [X, Z]` of `f : X ⊗ Y ⟶ Z` sends a simplex `y` to the map
`x ↦ f (x ∧ y)`. -/
private lemma functorHomEquiv_symm_smashProj_comp_app_app_apply (f : X ⊗ Y ⟶ Z)
    {n m : SimplexCategoryᵒᵖ} (y : Y.right.obj n) (g : n ⟶ m) (x : X.right.obj m) :
    dsimp% (((FunctorToTypes.functorHomEquiv X.right Y.right Z.right).symm
      (smashProj X Y ≫ f.right)).app n y).app m g x = f.right.app m (smashMk x (Y.right.map g y)) :=
  (rfl)

variable {X Y} in
/-- The uncurried map `X ⊗ Y ⟶ Z` of a based map `g : Y ⟶ Map_*(X, Z)` sends `(x, y)` to
`g y` evaluated at `x`. -/
private lemma functorHomEquiv_comp_ι_app_apply (g : Y ⟶ (PointedSSet.ihom X).obj Z)
    {n : SimplexCategoryᵒᵖ} (x : X.right.obj n) (y : Y.right.obj n) :
    dsimp% (FunctorToTypes.functorHomEquiv X.right Y.right Z.right
      (g.right ≫ (basedMaps X Z).ι)).app n (x, y) =
      (g.right.app n y : (basedMaps X Z).obj n).1.app n (𝟙 n) x := (rfl)

variable (Z)

/-- Currying identifies based maps `X ⊗ Y ⟶ Z` out of the smash product with based maps
`Y ⟶ Map_*(X, Z)`: a simplex `y` goes to the based map `x ↦ f (x ∧ y)`. -/
def tensorHomEquiv : (X ⊗ Y ⟶ Z) ≃ (Y ⟶ (PointedSSet.ihom X).obj Z) where
  -- The goals below are about simplices of `[X, Z]`, which are `Functor.HomObj`s only after
  -- unfolding Mathlib's internal hom. Where they are not type-correct at the transparency `rw`
  -- uses, the evaluation lemmas above are chained in with `Eq.trans` instead.
  toFun f := Under.homMk
    (SSet.Subcomplex.lift (B := basedMaps X Z)
      ((FunctorToTypes.functorHomEquiv X.right Y.right Z.right).symm (smashProj X Y ≫ f.right))
      (by
        rintro n _ ⟨y, rfl⟩ m g
        rw [functorHomEquiv_symm_smashProj_comp_app_app_apply]
        simp))
    (by
      ext n a m g x
      refine (functorHomEquiv_symm_smashProj_comp_app_app_apply f (Y.hom.app n a) g x).trans ?_
      simp [PointedSSet.ihom, basedMapsPoint])
  invFun g := smashLift
    (FunctorToTypes.functorHomEquiv X.right Y.right Z.right (g.right ≫ (basedMaps X Z).ι))
    (fun n y ↦ (g.right.app n y : (basedMaps X Z).obj n).2 n (𝟙 n))
    (fun n x ↦ by
      refine (functorHomEquiv_comp_ι_app_apply g x _).trans ?_
      rw [app_point]
      simp [PointedSSet.ihom, basedMapsPoint])
  left_inv f := tensor_ext fun n x y ↦ by
    refine (smashLift_app_smashMk _ _ _ x y).trans ?_
    refine (functorHomEquiv_comp_ι_app_apply _ x y).trans ?_
    refine (functorHomEquiv_symm_smashProj_comp_app_app_apply f y (𝟙 n) x).trans ?_
    simp
  right_inv g := by
    ext n y m f x
    -- Naturality of `g.right` at `f`, evaluated at `𝟙 m` and `x`. `simp` would prove the
    -- naturality square itself again and reduce it to `True`, so it is applied directly.
    refine (congrArg (fun φ : (basedMaps X Z).obj m ↦ φ.1.app m (𝟙 m) x)
      (NatTrans.naturality_apply g.right f y)).trans ?_
    -- The simplicial operator of `Map_*(X, Z)` along `f` precomposes with `f`, so the goal is
    -- `Category.comp_id f` under the component; `ihom_obj_right_map_coe_app_apply` states this
    -- for `ihom X`, which is only available once the instance below is built.
    exact congrArg (fun h ↦ (g.right.app n y : (basedMaps X Z).obj n).1.app m h x)
      (Category.comp_id f)

variable {X Y Z}

@[simp]
lemma tensorHomEquiv_apply_right_app_coe_app_apply (f : X ⊗ Y ⟶ Z) {n m : SimplexCategoryᵒᵖ}
    (y : Y.right.obj n) (g : n ⟶ m) (x : X.right.obj m) :
    dsimp% ((tensorHomEquiv X Y Z f).right.app n y : (basedMaps X Z).obj n).1.app m g x =
      f.right.app m (smashMk x (Y.right.map g y)) := (rfl)

@[simp]
lemma tensorHomEquiv_symm_apply_right_app_smashMk (g : Y ⟶ (PointedSSet.ihom X).obj Z)
    {n : SimplexCategoryᵒᵖ} (x : X.right.obj n) (y : Y.right.obj n) :
    dsimp% ((tensorHomEquiv X Y Z).symm g).right.app n (smashMk x y) =
      (g.right.app n y : (basedMaps X Z).obj n).1.app n (𝟙 n) x := (rfl)

/-- Currying is natural in the source: precomposition with `f` corresponds to precomposition
with `X ◁ f`. -/
lemma tensorHomEquiv_symm_comp {Y' : PointedSSet.{u}} (f : Y' ⟶ Y)
    (g : Y ⟶ (PointedSSet.ihom X).obj Z) :
    (tensorHomEquiv X Y' Z).symm (f ≫ g) = X ◁ f ≫ (tensorHomEquiv X Y Z).symm g :=
  tensor_ext fun _ _ _ ↦ by simp

/-- Currying is natural in the target: postcomposition with `g` corresponds to postcomposition
with `Map_*(X, g)`. -/
lemma tensorHomEquiv_comp {Z' : PointedSSet.{u}} (f : X ⊗ Y ⟶ Z) (g : Z ⟶ Z') :
    tensorHomEquiv X Y Z' (f ≫ g) = tensorHomEquiv X Y Z f ≫ (PointedSSet.ihom X).map g :=
  (rfl)

/-- The smash product of pointed simplicial sets is closed: `X ⊗ -` is left adjoint to the
pointed mapping simplicial set functor `Map_*(X, -)`. -/
instance monoidalClosed : MonoidalClosed PointedSSet.{u} where
  closed X :=
    { rightAdj := PointedSSet.ihom X
      adj := Adjunction.mkOfHomEquiv
        { homEquiv := tensorHomEquiv X
          homEquiv_naturality_left_symm := tensorHomEquiv_symm_comp
          homEquiv_naturality_right := tensorHomEquiv_comp } }

/-- The hom-set bijection of the smash–hom adjunction is `PointedSSet.tensorHomEquiv`. -/
lemma homEquiv_def (X Y Z : PointedSSet.{u}) :
    (ihom.adjunction X).homEquiv Y Z = tensorHomEquiv X Y Z :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
lemma curry_right_app_coe_app_apply (f : X ⊗ Y ⟶ Z) {n m : SimplexCategoryᵒᵖ}
    (y : Y.right.obj n) (g : n ⟶ m) (x : X.right.obj m) :
    dsimp% ((MonoidalClosed.curry f).right.app n y : (basedMaps X Z).obj n).1.app m g x =
      f.right.app m (smashMk x (Y.right.map g y)) := by
  rw [← MonoidalClosed.homEquiv_apply_eq, homEquiv_def]
  exact tensorHomEquiv_apply_right_app_coe_app_apply f y g x

@[simp]
lemma uncurry_right_app_smashMk (g : Y ⟶ (ihom X).obj Z) {n : SimplexCategoryᵒᵖ}
    (x : X.right.obj n) (y : Y.right.obj n) :
    dsimp% (MonoidalClosed.uncurry g).right.app n (smashMk x y) =
      (g.right.app n y : (basedMaps X Z).obj n).1.app n (𝟙 n) x := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq, homEquiv_def]
  exact tensorHomEquiv_symm_apply_right_app_smashMk g x y

/-- A simplex of `Map_*(X, Y)` sends the basepoint of `X` to the basepoint of `Y`. -/
@[simp]
lemma ihom_obj_right_coe_app_point {n m : SimplexCategoryᵒᵖ} (φ : ((ihom X).obj Y).right.obj n)
    (f : n ⟶ m) :
    dsimp% (φ : (basedMaps X Y).obj n).1.app m f (X.point m) = Y.point m :=
  basedMaps_app_point φ f

/-- The simplicial operator of `Map_*(X, Y)` along `f` precomposes the components of a based map
with `f`. -/
@[simp]
lemma ihom_obj_right_map_coe_app_apply {n m k : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (φ : ((ihom X).obj Y).right.obj n) (g : m ⟶ k) (x : X.right.obj k) :
    dsimp% (((ihom X).obj Y).right.map f φ : (basedMaps X Y).obj m).1.app k g x =
      (φ : (basedMaps X Y).obj n).1.app k (f ≫ g) x := (rfl)

/-- The basepoint of `Map_*(X, Y)` is the constant map to the basepoint of `Y`. -/
@[simp]
lemma ihom_obj_point_coe_app_apply {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : X.right.obj m) :
    dsimp% (((ihom X).obj Y).point n : (basedMaps X Y).obj n).1.app m f x = Y.point m :=
  -- The basepoint is `basedMapsPoint X Y`, the constant map `HomObj.ofNatTrans (SSet.const _)`;
  -- its component at `x` unfolds to a face of the basepoint of `Y`. `simp` cannot see through
  -- the internal hom of `MonoidalClosed` here, so the unfolded goal is closed by `map_point`.
  map_point Y _

/-- Precomposition of a based mapping simplex acts on its source components. -/
@[simp]
lemma pre_right_app_coe_app_apply {W : PointedSSet.{u}} (i : W ⟶ X)
    {n m : SimplexCategoryᵒᵖ} (φ : ((ihom X).obj Y).right.obj n)
    (f : n ⟶ m) (x : W.right.obj m) :
    dsimp% ((((MonoidalClosed.pre i).app Y).right.app n φ :
      (basedMaps W Y).obj n).1.app m f x) =
        (φ : (basedMaps X Y).obj n).1.app m f (i.right.app m x) := by
  have h := congrArg (fun k : W ⊗ (ihom X).obj Y ⟶ Y ↦
    k.right.app m (smashMk x (((ihom X).obj Y).right.map f φ)))
    (MonoidalClosed.id_tensor_pre_app_comp_ev i Y)
  simp only [Under.comp_right, NatTrans.comp_app, types_comp_apply,
    whiskerLeft_app_smashMk, whiskerRight_app_smashMk,
    ← MonoidalClosed.uncurry_id_eq_ev, uncurry_right_app_smashMk,
    Under.id_right, NatTrans.id_app, types_id_apply] at h
  have hn := congrArg (fun ψ : ((ihom W).obj Y).right.obj m ↦
    (ψ : (basedMaps W Y).obj m).1.app m (𝟙 m) x)
    (NatTrans.naturality_apply ((MonoidalClosed.pre i).app Y).right f φ)
  simpa only [Under.comp_right, NatTrans.comp_app, types_comp_apply,
    whiskerLeft_app_smashMk, whiskerRight_app_smashMk,
    ihom_obj_right_map_coe_app_apply,
    Category.comp_id] using hn.symm.trans h

/-- The internal hom acts on based maps by postcomposition. -/
@[simp]
lemma ihom_map_right_app_coe_app_apply (g : Y ⟶ Z) {n m : SimplexCategoryᵒᵖ}
    (φ : ((ihom X).obj Y).right.obj n) (f : n ⟶ m) (x : X.right.obj m) :
    dsimp% (((ihom X).map g).right.app n φ : (basedMaps X Z).obj n).1.app m f x =
      g.right.app m ((φ : (basedMaps X Y).obj n).1.app m f x) := (rfl)

/-- Evaluation `X ⊗ Map_*(X, Y) ⟶ Y` applies a based map to a simplex. -/
@[simp]
lemma ihom_ev_app_right_app_smashMk {n : SimplexCategoryᵒᵖ} (x : X.right.obj n)
    (φ : ((ihom X).obj Y).right.obj n) :
    dsimp% ((ihom.ev X).app Y).right.app n (smashMk x φ) =
      (φ : (basedMaps X Y).obj n).1.app n (𝟙 n) x := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_right_app_smashMk]
  simp

/-- Coevaluation `Y ⟶ Map_*(X, X ⊗ Y)` sends a simplex `y` to the based map `x ↦ x ∧ y`. -/
@[simp]
lemma ihom_coev_app_right_app_coe_app_apply {n m : SimplexCategoryᵒᵖ} (y : Y.right.obj n)
    (f : n ⟶ m) (x : X.right.obj m) :
    dsimp% (((ihom.coev X).app Y).right.app n y : (basedMaps X (X ⊗ Y)).obj n).1.app m f x =
      smashMk x (Y.right.map f y) := by
  rw [← MonoidalClosed.curry_id_eq_coev, curry_right_app_coe_app_apply]
  simp

section Restriction

open CategoryTheory.ConcreteCategory MonoidalClosed Limits

variable {E B : PointedSSet.{u}}

/-- Restriction of an unpointed mapping simplex to the chosen point of its source. -/
@[simp]
lemma pre_point_app (X E : PointedSSet.{u}) {n m : SimplexCategoryᵒᵖ}
    (φ : ((CategoryTheory.ihom X.right).obj E.right).obj n) (f : n ⟶ m)
    (z : (Δ[0] : SSet.{u}).obj m) :
    (((MonoidalClosed.pre X.hom).app E.right).app n φ).app m f z =
      φ.app m f (X.point m) := by
  have h := congrArg (fun k : (Δ[0] : SSet.{u}) ⊗
      (CategoryTheory.ihom X.right).obj E.right ⟶ E.right ↦
    k.app m (z, ((CategoryTheory.ihom X.right).obj E.right).map f φ))
      (id_tensor_pre_app_comp_ev X.hom E.right)
  -- Evaluation applies a mapping simplex at the identity; simplicial restriction by `f`
  -- turns that identity component into its `f` component.
  change (((MonoidalClosed.pre X.hom).app E.right).app m
    (((CategoryTheory.ihom X.right).obj E.right).map f φ)).app m (𝟙 m) z =
      (((CategoryTheory.ihom X.right).obj E.right).map f φ).app m (𝟙 m)
        (X.hom.app m z) at h
  have hn := congrArg (fun ψ : ((CategoryTheory.ihom (Δ[0] : SSet.{u})).obj
      E.right).obj m ↦ ψ.app m (𝟙 m) z)
    (NatTrans.naturality_apply ((MonoidalClosed.pre X.hom).app E.right) f φ)
  have result := hn.symm.trans h
  -- The simplicial operator on the native internal hom precomposes its simplex index.
  change (((MonoidalClosed.pre X.hom).app E.right).app n φ).app m (f ≫ 𝟙 m) z =
    φ.app m (f ≫ 𝟙 m) (X.hom.app m z) at result
  simpa only [Category.comp_id, hom_app] using result

/-- The constant family of maps from the zero-simplex to the chosen point of `E`. -/
def pointRestriction (E : PointedSSet.{u}) (K : SSet.{u}) :
    K ⟶ (CategoryTheory.ihom (Δ[0] : SSet.{u})).obj E.right where
  app _ := ↾fun _ ↦ Functor.HomObj.ofNatTrans E.hom

/-- Every component of the constant family is the chosen point. -/
@[simp]
lemma pointRestriction_app_app (E : PointedSSet.{u}) (K : SSet.{u})
    {n m : SimplexCategoryᵒᵖ} (x : K.obj n) (f : n ⟶ m) (z : (Δ[0] : SSet.{u}).obj m) :
    ((pointRestriction E K).app n x).app m f z = E.point m :=
  hom_app E m z

/-- Constant families at the basepoint are natural in their parameter. -/
@[reassoc (attr := simp)]
lemma comp_pointRestriction (E : PointedSSet.{u}) {K L : SSet.{u}} (f : K ⟶ L) :
    f ≫ pointRestriction E L = pointRestriction E K := (rfl)

/-- Based maps preserve the constant family at the basepoint. -/
@[reassoc (attr := simp)]
lemma pointRestriction_comp_ihom_map (p : E ⟶ B) (K : SSet.{u}) :
    pointRestriction E K ≫ (CategoryTheory.ihom (Δ[0] : SSet.{u})).map p.right =
      pointRestriction B K := by
  ext n : 1
  apply ConcreteCategory.hom_ext
  intro x
  apply Functor.functorHom_ext fun m f ↦ ?_
  ext z
  -- Postcomposition on the unpointed internal hom composes its component maps.
  change p.right.app m (E.hom.app m z) = B.hom.app m z
  simp only [hom_app, app_point]

/-- A family of unpointed maps is based exactly when restriction to the source basepoint
is the constant family at the target basepoint. -/
lemma range_le_basedMaps_iff (X E : PointedSSet.{u}) {K : SSet.{u}}
    (f : K ⟶ (CategoryTheory.ihom X.right).obj E.right) :
    SSet.Subcomplex.range f ≤ basedMaps X E ↔
      f ≫ (MonoidalClosed.pre X.hom).app E.right = pointRestriction E K := by
  constructor
  · intro hf
    ext n : 1
    apply ConcreteCategory.hom_ext
    intro x
    apply Functor.functorHom_ext fun m g ↦ ?_
    ext z
    exact (pre_point_app X E (f.app n x) g z).trans
      (((mem_basedMaps_iff _).1 (hf n ⟨x, rfl⟩) m g).trans
        (pointRestriction_app_app E K x g z).symm)
  · intro hf n φ hφ
    obtain ⟨x, rfl⟩ := hφ
    apply (mem_basedMaps_iff _).2
    intro m g
    have h := congrArg (fun k : K ⟶ (CategoryTheory.ihom (Δ[0] : SSet.{u})).obj E.right ↦
      (k.app n x).app m g (SSet.stdSimplex.const 0 0 m)) hf
    exact (pre_point_app X E (f.app n x) g _).symm.trans
      (h.trans (pointRestriction_app_app E K x g _))

/-- The inclusion of based maps restricts to the constant family at the basepoint. -/
@[reassoc (attr := simp)]
lemma basedMaps_ι_comp_pre (X E : PointedSSet.{u}) :
    (basedMaps X E).ι ≫ (MonoidalClosed.pre X.hom).app E.right =
      pointRestriction E (basedMaps X E).toSSet :=
  (range_le_basedMaps_iff X E _).1 (by rintro n _ ⟨φ, rfl⟩; exact φ.2)

/-- The based mapping simplicial set is the fibre of restriction to the source basepoint
at the target basepoint, expressed as a pullback over the zero-simplex. -/
theorem basedMaps_isPullback (X E : PointedSSet.{u}) :
    IsPullback (basedMaps X E).ι (SSet.stdSimplex.isTerminalObj₀.from _)
      ((MonoidalClosed.pre X.hom).app E.right) (pointRestriction E Δ[0]) := by
  have hw : (basedMaps X E).ι ≫ (MonoidalClosed.pre X.hom).app E.right =
      SSet.stdSimplex.isTerminalObj₀.from _ ≫ pointRestriction E Δ[0] := by simp
  let lift (s : PullbackCone ((MonoidalClosed.pre X.hom).app E.right)
      (pointRestriction E Δ[0])) : s.pt ⟶ (basedMaps X E).toSSet :=
    SSet.Subcomplex.lift s.fst ((range_le_basedMaps_iff X E _).2
      (s.condition.trans (comp_pointRestriction E s.snd)))
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw lift
    (fun _ ↦ SSet.Subcomplex.lift_ι _ _)
    (fun _ ↦ SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
    (fun s m hm _ ↦ (cancel_mono (basedMaps X E).ι).1
      (hm.trans (SSet.Subcomplex.lift_ι _ _).symm)))

/-- Inclusion of based maps into unpointed maps commutes with postcomposition. -/
@[simp, reassoc]
lemma ihom_map_right_comp_ι (X : PointedSSet.{u}) (p : E ⟶ B) :
    ((PointedSSet.ihom X).map p).right ≫ (basedMaps X B).ι =
      (basedMaps X E).ι ≫ (CategoryTheory.ihom X.right).map p.right := by
  ext n : 1
  rfl

/-- Inclusion of based maps into unpointed maps commutes with precomposition. -/
@[simp, reassoc]
lemma pre_right_comp_ι {W X : PointedSSet.{u}} (i : W ⟶ X) (E : PointedSSet.{u}) :
    ((MonoidalClosed.pre i).app E).right ≫ (basedMaps W E).ι =
      (basedMaps X E).ι ≫ (MonoidalClosed.pre i.right).app E.right := by
  ext n : 1
  apply ConcreteCategory.hom_ext
  intro φ
  apply Functor.functorHom_ext fun m f ↦ ?_
  ext x
  have h := congrArg (fun k : W.right ⊗ (CategoryTheory.ihom X.right).obj E.right ⟶
      E.right ↦ k.app m (x, ((CategoryTheory.ihom X.right).obj E.right).map f φ.1))
    (MonoidalClosed.id_tensor_pre_app_comp_ev i.right E.right)
  have hn := congrArg (fun ψ : ((CategoryTheory.ihom W.right).obj E.right).obj m ↦
    ψ.app m (𝟙 m) x)
    (NatTrans.naturality_apply ((MonoidalClosed.pre i.right).app E.right) f φ.1)
  -- The unpointed internal hom is the native functor HomObj; evaluation is application.
  change (((MonoidalClosed.pre i.right).app E.right).app m
    (((CategoryTheory.ihom X.right).obj E.right).map f φ.1)).app m (𝟙 m) x =
      φ.1.app m (f ≫ 𝟙 m) (i.right.app m x) at h
  -- Its simplicial operators precompose the simplex index.
  change (((MonoidalClosed.pre i.right).app E.right).app n φ.1).app m (f ≫ 𝟙 m) x =
    _ at hn
  -- The subcomplex inclusions forget the proofs that the mapping simplices are based.
  change (((MonoidalClosed.pre i).app E).right.app n φ :
    (basedMaps W E).obj n).1.app m f x =
      (((MonoidalClosed.pre i.right).app E.right).app n φ.1).app m f x
  rw [pre_right_app_coe_app_apply]
  simpa only [Category.comp_id] using (hn.trans h).symm

end Restriction

end PointedSSet

end MathlibExt.SpectraSource
