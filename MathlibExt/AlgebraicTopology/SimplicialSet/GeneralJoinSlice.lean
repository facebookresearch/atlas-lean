/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinProperties
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# General join slices and structured join division

For an arbitrary simplicial map `f : K ⟶ X`, this file defines the genuine
join slices `X_{f/}` and `X_{/f}`.  Their simplices retain the whole original
maps `K ⋆ Δ[n] ⟶ X` and `Δ[n] ⋆ K ⟶ X`, respectively.

The fixed-factor join functors land in `Under K`.  This is essential: the raw
functor `K ⋆ - : SSet ⥤ SSet` does not preserve the initial object and cannot
have the asserted right adjoint on `SSet`.  The structured join and division
functors defined below have the correct source and target categories for the
eventual left and right join-division adjunctions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial CategoryTheory.MonoidalCategory.DayFunctor
  ExternalProduct CategoryTheory.Prod

universe u

namespace SSet

/-!
## General under-slices
-/

/-- The under-slice `X_{f/}` of a simplicial map `f : K ⟶ X`.

An `n`-simplex is a whole map `K ⋆ Δ[n] ⟶ X` whose restriction to the
fixed left factor is exactly `f`. -/
def sliceUnder (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) : SSet.{u} where
  obj n :=
    { g : K ⋆ SSet.stdSimplex.obj n.unop ⟶ X //
      SSet.joinInl K (SSet.stdSimplex.obj n.unop) ≫ g = f }
  map α := ↾fun g =>
    ⟨(SSet.join.obj K).map (SSet.stdSimplex.map α.unop) ≫ g.1, by
      rw [← Category.assoc, SSet.joinInl_comp_map]
      exact g.2⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    simp
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    simp [Category.assoc]

namespace sliceUnder

variable (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X)

/-- The literal whole-map description of the `n`-simplices of an under-slice. -/
def simplexEquiv (n : ℕ) :
    (sliceUnder X f).obj (op ⦋n⦌) ≃
      { g : K ⋆ Δ[n] ⟶ X // SSet.joinInl K Δ[n] ≫ g = f } :=
  Equiv.refl _

/-- The fixed-factor equation of an under-slice simplex. -/
@[simp]
lemma condition {n : SimplexCategoryᵒᵖ} (g : (sliceUnder X f).obj n) :
    SSet.joinInl K (SSet.stdSimplex.obj n.unop) ≫ g.1 = f :=
  g.2

/-- Simplicial operators act by precomposition in the free right factor. -/
@[simp]
lemma map_val {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (g : (sliceUnder X f).obj n) :
    ((sliceUnder X f).map α g).1 =
      (SSet.join.obj K).map (SSet.stdSimplex.map α.unop) ≫ g.1 :=
  rfl

/-- Projection to `X`, by restriction to the free right factor. -/
def proj : sliceUnder X f ⟶ X where
  app n := ↾fun g => SSet.yonedaEquiv
    (SSet.joinInr K (SSet.stdSimplex.obj n.unop) ≫ g.1)
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro g
    simp only [types_comp_apply]
    change SSet.yonedaEquiv
        (SSet.joinInr K (SSet.stdSimplex.obj m.unop) ≫
          ((SSet.join.obj K).map (SSet.stdSimplex.map α.unop) ≫ g.1)) =
      X.map α (SSet.yonedaEquiv
        (SSet.joinInr K (SSet.stdSimplex.obj n.unop) ≫ g.1))
    rw [← Category.assoc, ← SSet.map_comp_joinInr, Category.assoc]
    exact (SSet.yonedaEquiv_naturality α.unop _).symm

/-- Projection reads the restriction of the whole join map to the free factor. -/
@[simp]
lemma proj_apply {n : SimplexCategoryᵒᵖ} (g : (sliceUnder X f).obj n) :
    (proj X f).app n g = SSet.yonedaEquiv
      (SSet.joinInr K (SSet.stdSimplex.obj n.unop) ≫ g.1) :=
  rfl

/-- Postcomposition in the ambient target. -/
def map {Y : SSet.{u}} (p : X ⟶ Y) :
    sliceUnder X f ⟶ sliceUnder Y (f ≫ p) where
  app n := ↾fun g => ⟨g.1 ≫ p, by rw [← Category.assoc, g.2]⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change ((SSet.join.obj K).map (SSet.stdSimplex.map α.unop) ≫ g.1) ≫ p =
      (SSet.join.obj K).map (SSet.stdSimplex.map α.unop) ≫ (g.1 ≫ p)
    rw [Category.assoc]

@[simp]
lemma map_app_val {Y : SSet.{u}} (p : X ⟶ Y)
    {n : SimplexCategoryᵒᵖ} (g : (sliceUnder X f).obj n) :
    ((map X f p).app n g).1 = g.1 ≫ p :=
  rfl

@[reassoc (attr := simp)]
lemma map_proj {Y : SSet.{u}} (p : X ⟶ Y) :
    map X f p ≫ proj Y (f ≫ p) = proj X f ≫ p := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  simp only [NatTrans.comp_app, types_comp_apply, proj_apply, map_app_val]
  rw [← SSet.yonedaEquiv_comp, Category.assoc]

@[simp]
lemma map_id : map X f (𝟙 X) = 𝟙 (sliceUnder X f) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  simp only [map_app_val, NatTrans.id_app, types_id_apply, Category.comp_id]

@[simp]
lemma map_comp {Y Z : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ Z) :
    map X f (p ≫ q) = map X f p ≫ map Y (f ≫ p) q := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  simp only [NatTrans.comp_app, types_comp_apply, map_app_val, Category.assoc]

/-- Restriction along a map of fixed diagrams. -/
def restrict {K₀ : SSet.{u}} (i : K₀ ⟶ K) :
    sliceUnder X f ⟶ sliceUnder X (i ≫ f) where
  app n := ↾fun g =>
    ⟨(SSet.join.map i).app (SSet.stdSimplex.obj n.unop) ≫ g.1, by
      rw [← Category.assoc, ← SSet.map_comp_joinInl, Category.assoc, g.2]⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change (SSet.join.map i).app (SSet.stdSimplex.obj m.unop) ≫
        ((SSet.join.obj K).map (SSet.stdSimplex.map α.unop) ≫ g.1) =
      (SSet.join.obj K₀).map (SSet.stdSimplex.map α.unop) ≫
        ((SSet.join.map i).app (SSet.stdSimplex.obj n.unop) ≫ g.1)
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun z => z ≫ g.1)
      ((SSet.join.map i).naturality (SSet.stdSimplex.map α.unop)).symm

@[simp]
lemma restrict_app_val {K₀ : SSet.{u}} (i : K₀ ⟶ K)
    {n : SimplexCategoryᵒᵖ} (g : (sliceUnder X f).obj n) :
    ((restrict X f i).app n g).1 =
      (SSet.join.map i).app (SSet.stdSimplex.obj n.unop) ≫ g.1 :=
  rfl

@[reassoc (attr := simp)]
lemma restrict_proj {K₀ : SSet.{u}} (i : K₀ ⟶ K) :
    restrict X f i ≫ proj X (i ≫ f) = proj X f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  simp only [NatTrans.comp_app, types_comp_apply, proj_apply, restrict_app_val]
  rw [← Category.assoc, SSet.joinInr_comp_map]

@[simp]
lemma restrict_id : restrict X f (𝟙 K) = 𝟙 (sliceUnder X f) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  change (SSet.join.map (𝟙 K)).app
    (SSet.stdSimplex.obj n.unop) ≫ g.1 = g.1
  rw [SSet.join.map_id, NatTrans.id_app, Category.id_comp]

@[simp]
lemma restrict_comp {K₀ K₁ : SSet.{u}} (i : K₀ ⟶ K₁) (j : K₁ ⟶ K) :
    restrict X f (i ≫ j) =
      restrict X f j ≫ restrict X (j ≫ f) i := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  change (SSet.join.map (i ≫ j)).app
      (SSet.stdSimplex.obj n.unop) ≫ g.1 =
    (SSet.join.map i).app (SSet.stdSimplex.obj n.unop) ≫
      (SSet.join.map j).app (SSet.stdSimplex.obj n.unop) ≫ g.1
  rw [SSet.join.map_comp, NatTrans.comp_app, Category.assoc]

lemma restrict_map {K₀ : SSet.{u}} (i : K₀ ⟶ K) {Y : SSet.{u}}
    (p : X ⟶ Y) :
    restrict X f i ≫ map X (i ≫ f) p =
      map X f p ≫ restrict Y (f ≫ p) i := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  change ((SSet.join.map i).app (SSet.stdSimplex.obj n.unop) ≫ g.1) ≫ p =
    (SSet.join.map i).app (SSet.stdSimplex.obj n.unop) ≫ (g.1 ≫ p)
  exact Category.assoc _ _ _

end sliceUnder

/-!
## General over-slices
-/

/-- The over-slice `X_{/f}` of a simplicial map `f : K ⟶ X`.

An `n`-simplex is a whole map `Δ[n] ⋆ K ⟶ X` whose restriction to the
fixed right factor is exactly `f`. -/
def sliceOver (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X) : SSet.{u} where
  obj n :=
    { g : SSet.stdSimplex.obj n.unop ⋆ K ⟶ X //
      SSet.joinInr (SSet.stdSimplex.obj n.unop) K ≫ g = f }
  map α := ↾fun g =>
    ⟨(SSet.join.map (SSet.stdSimplex.map α.unop)).app K ≫ g.1, by
      rw [← Category.assoc, SSet.joinInr_comp_map]
      exact g.2⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    simp
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    simp [Category.assoc]

namespace sliceOver

variable (X : SSet.{u}) {K : SSet.{u}} (f : K ⟶ X)

/-- The literal whole-map description of the `n`-simplices of an over-slice. -/
def simplexEquiv (n : ℕ) :
    (sliceOver X f).obj (op ⦋n⦌) ≃
      { g : Δ[n] ⋆ K ⟶ X // SSet.joinInr Δ[n] K ≫ g = f } :=
  Equiv.refl _

@[simp]
lemma condition {n : SimplexCategoryᵒᵖ} (g : (sliceOver X f).obj n) :
    SSet.joinInr (SSet.stdSimplex.obj n.unop) K ≫ g.1 = f :=
  g.2

@[simp]
lemma map_val {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (g : (sliceOver X f).obj n) :
    ((sliceOver X f).map α g).1 =
      (SSet.join.map (SSet.stdSimplex.map α.unop)).app K ≫ g.1 :=
  rfl

/-- Projection to `X`, by restriction to the free left factor. -/
def proj : sliceOver X f ⟶ X where
  app n := ↾fun g => SSet.yonedaEquiv
    (SSet.joinInl (SSet.stdSimplex.obj n.unop) K ≫ g.1)
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro g
    simp only [types_comp_apply]
    change SSet.yonedaEquiv
        (SSet.joinInl (SSet.stdSimplex.obj m.unop) K ≫
          ((SSet.join.map (SSet.stdSimplex.map α.unop)).app K ≫ g.1)) =
      X.map α (SSet.yonedaEquiv
        (SSet.joinInl (SSet.stdSimplex.obj n.unop) K ≫ g.1))
    rw [← Category.assoc, ← SSet.map_comp_joinInl, Category.assoc]
    exact (SSet.yonedaEquiv_naturality α.unop _).symm

@[simp]
lemma proj_apply {n : SimplexCategoryᵒᵖ} (g : (sliceOver X f).obj n) :
    (proj X f).app n g = SSet.yonedaEquiv
      (SSet.joinInl (SSet.stdSimplex.obj n.unop) K ≫ g.1) :=
  rfl

/-- Postcomposition in the ambient target. -/
def map {Y : SSet.{u}} (p : X ⟶ Y) :
    sliceOver X f ⟶ sliceOver Y (f ≫ p) where
  app n := ↾fun g => ⟨g.1 ≫ p, by rw [← Category.assoc, g.2]⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change ((SSet.join.map (SSet.stdSimplex.map α.unop)).app K ≫ g.1) ≫ p =
      (SSet.join.map (SSet.stdSimplex.map α.unop)).app K ≫ (g.1 ≫ p)
    rw [Category.assoc]

@[simp]
lemma map_app_val {Y : SSet.{u}} (p : X ⟶ Y)
    {n : SimplexCategoryᵒᵖ} (g : (sliceOver X f).obj n) :
    ((map X f p).app n g).1 = g.1 ≫ p :=
  rfl

@[reassoc (attr := simp)]
lemma map_proj {Y : SSet.{u}} (p : X ⟶ Y) :
    map X f p ≫ proj Y (f ≫ p) = proj X f ≫ p := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  simp only [NatTrans.comp_app, types_comp_apply, proj_apply, map_app_val]
  rw [← SSet.yonedaEquiv_comp, Category.assoc]

@[simp]
lemma map_id : map X f (𝟙 X) = 𝟙 (sliceOver X f) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  simp only [map_app_val, NatTrans.id_app, types_id_apply, Category.comp_id]

@[simp]
lemma map_comp {Y Z : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ Z) :
    map X f (p ≫ q) = map X f p ≫ map Y (f ≫ p) q := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  simp only [NatTrans.comp_app, types_comp_apply, map_app_val, Category.assoc]

/-- Restriction along a map of fixed diagrams. -/
def restrict {K₀ : SSet.{u}} (i : K₀ ⟶ K) :
    sliceOver X f ⟶ sliceOver X (i ≫ f) where
  app n := ↾fun g =>
    ⟨(SSet.join.obj (SSet.stdSimplex.obj n.unop)).map i ≫ g.1, by
      rw [← Category.assoc, ← SSet.map_comp_joinInr, Category.assoc, g.2]⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change (SSet.join.obj (SSet.stdSimplex.obj m.unop)).map i ≫
        ((SSet.join.map (SSet.stdSimplex.map α.unop)).app K ≫ g.1) =
      (SSet.join.map (SSet.stdSimplex.map α.unop)).app K₀ ≫
        ((SSet.join.obj (SSet.stdSimplex.obj n.unop)).map i ≫ g.1)
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun z => z ≫ g.1)
      ((SSet.join.map (SSet.stdSimplex.map α.unop)).naturality i)

@[simp]
lemma restrict_app_val {K₀ : SSet.{u}} (i : K₀ ⟶ K)
    {n : SimplexCategoryᵒᵖ} (g : (sliceOver X f).obj n) :
    ((restrict X f i).app n g).1 =
      (SSet.join.obj (SSet.stdSimplex.obj n.unop)).map i ≫ g.1 :=
  rfl

@[reassoc (attr := simp)]
lemma restrict_proj {K₀ : SSet.{u}} (i : K₀ ⟶ K) :
    restrict X f i ≫ proj X (i ≫ f) = proj X f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  simp only [NatTrans.comp_app, types_comp_apply, proj_apply, restrict_app_val]
  rw [← Category.assoc, SSet.joinInl_comp_map]

@[simp]
lemma restrict_id : restrict X f (𝟙 K) = 𝟙 (sliceOver X f) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  change (SSet.join.obj (SSet.stdSimplex.obj n.unop)).map (𝟙 K) ≫ g.1 = g.1
  rw [(SSet.join.obj (SSet.stdSimplex.obj n.unop)).map_id, Category.id_comp]

@[simp]
lemma restrict_comp {K₀ K₁ : SSet.{u}} (i : K₀ ⟶ K₁) (j : K₁ ⟶ K) :
    restrict X f (i ≫ j) =
      restrict X f j ≫ restrict X (j ≫ f) i := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  change (SSet.join.obj (SSet.stdSimplex.obj n.unop)).map (i ≫ j) ≫ g.1 =
    (SSet.join.obj (SSet.stdSimplex.obj n.unop)).map i ≫
      (SSet.join.obj (SSet.stdSimplex.obj n.unop)).map j ≫ g.1
  rw [(SSet.join.obj (SSet.stdSimplex.obj n.unop)).map_comp, Category.assoc]

lemma restrict_map {K₀ : SSet.{u}} (i : K₀ ⟶ K) {Y : SSet.{u}}
    (p : X ⟶ Y) :
    restrict X f i ≫ map X (i ≫ f) p =
      map X f p ≫ restrict Y (f ≫ p) i := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  change ((SSet.join.obj (SSet.stdSimplex.obj n.unop)).map i ≫ g.1) ≫ p =
    (SSet.join.obj (SSet.stdSimplex.obj n.unop)).map i ≫ (g.1 ≫ p)
  exact Category.assoc _ _ _

end sliceOver

/-!
## Structured fixed-factor join functors
-/

/-- Join on the left by `K`, retaining the canonical inclusion as an object
under `K`. -/
def joinUnder (K : SSet.{u}) : SSet.{u} ⥤ Under K where
  obj A := Under.mk (joinInl K A)
  map a := Under.homMk ((join.obj K).map a) (joinInl_comp_map K a)
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

@[simp]
lemma joinUnder_obj_hom (K A : SSet.{u}) :
    ((joinUnder K).obj A).hom = joinInl K A :=
  rfl

@[simp]
lemma joinUnder_map_right (K : SSet.{u}) {A B : SSet.{u}} (a : A ⟶ B) :
    ((joinUnder K).map a).right = (join.obj K).map a :=
  rfl

/-- Join on the right by `K`, retaining the canonical inclusion as an object
under `K`. -/
def joinOver (K : SSet.{u}) : SSet.{u} ⥤ Under K where
  obj A := Under.mk (joinInr A K)
  map a := Under.homMk ((join.map a).app K) (joinInr_comp_map a K)
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

@[simp]
lemma joinOver_obj_hom (K A : SSet.{u}) :
    ((joinOver K).obj A).hom = joinInr A K :=
  rfl

@[simp]
lemma joinOver_map_right (K : SSet.{u}) {A B : SSet.{u}} (a : A ⟶ B) :
    ((joinOver K).map a).right = (join.map a).app K :=
  rfl

/-- Postcomposition along a morphism of structured targets. -/
def sliceUnder.mapUnder {K : SSet.{u}} {P Q : Under K} (q : P ⟶ Q) :
    sliceUnder P.right P.hom ⟶ sliceUnder Q.right Q.hom where
  app n := ↾fun g => ⟨g.1 ≫ q.right, by
    rw [← Category.assoc, g.2, q.w]⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change ((SSet.join.obj K).map (SSet.stdSimplex.map α.unop) ≫ g.1) ≫
        q.right =
      (SSet.join.obj K).map (SSet.stdSimplex.map α.unop) ≫ (g.1 ≫ q.right)
    exact Category.assoc _ _ _

@[simp]
lemma sliceUnder.mapUnder_app_val {K : SSet.{u}} {P Q : Under K}
    (q : P ⟶ Q) {n : SimplexCategoryᵒᵖ}
    (g : (sliceUnder P.right P.hom).obj n) :
    ((sliceUnder.mapUnder q).app n g).1 = g.1 ≫ q.right :=
  rfl

/-- Postcomposition along a morphism of structured targets. -/
def sliceOver.mapUnder {K : SSet.{u}} {P Q : Under K} (q : P ⟶ Q) :
    sliceOver P.right P.hom ⟶ sliceOver Q.right Q.hom where
  app n := ↾fun g => ⟨g.1 ≫ q.right, by
    rw [← Category.assoc, g.2, q.w]⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change ((SSet.join.map (SSet.stdSimplex.map α.unop)).app K ≫ g.1) ≫
        q.right =
      (SSet.join.map (SSet.stdSimplex.map α.unop)).app K ≫ (g.1 ≫ q.right)
    exact Category.assoc _ _ _

@[simp]
lemma sliceOver.mapUnder_app_val {K : SSet.{u}} {P Q : Under K}
    (q : P ⟶ Q) {n : SimplexCategoryᵒᵖ}
    (g : (sliceOver P.right P.hom).obj n) :
    ((sliceOver.mapUnder q).app n g).1 = g.1 ≫ q.right :=
  rfl

/-- The left join-division functor on structured targets. -/
def joinLeftDivision (K : SSet.{u}) : Under K ⥤ SSet.{u} where
  obj P := sliceUnder P.right P.hom
  map q := sliceUnder.mapUnder q
  map_id P := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change g.1 ≫ (𝟙 P : P ⟶ P).right = g.1
    rw [Under.id_right, Category.comp_id]
  map_comp q r := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change (g.1 ≫ q.right) ≫ r.right = g.1 ≫ (q ≫ r).right
    rw [Under.comp_right, Category.assoc]

/-- The right join-division functor on structured targets. -/
def joinRightDivision (K : SSet.{u}) : Under K ⥤ SSet.{u} where
  obj P := sliceOver P.right P.hom
  map q := sliceOver.mapUnder q
  map_id P := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change g.1 ≫ (𝟙 P : P ⟶ P).right = g.1
    rw [Under.id_right, Category.comp_id]
  map_comp q r := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change (g.1 ≫ q.right) ≫ r.right = g.1 ≫ (q ≫ r).right
    rw [Under.comp_right, Category.assoc]

end SSet
