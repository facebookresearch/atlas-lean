/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import MathlibExt.AlgebraicTopology.SimplexCategory.Reedy
public import MathlibExt.CategoryTheory.Reedy.Boundary

/-!
# Hom complexes of resolution diagrams

For a cosimplicial object `A` and a simplicial object `B`, the diagonal resolution Hom complex
has `(A.obj n.unop ⟶ B.obj n)` in degree `n`. Its simplicial operators use the actual maps of
both diagrams. This construction is a bifunctor, contravariant in `A` and covariant in `B`.

The left and right resolution Hom complexes specialize one diagram to a constant object.
This file proves their algebraic functoriality and the comparisons induced by the actual
augmentation and coaugmentation. Homotopical properties require separate framing theorems.
-/

section

/-
Copyright (c) 2026 Toskua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Toskua
-/

@[expose] public section

set_option autoImplicit false

universe v v₁ v₂ u u₁ u₂

open CategoryTheory Opposite

namespace HomotopicalAlgebra.ResolutionHomComplex

variable {C : Type u} [Category.{v} C]

/-- The diagonal Hom complex of the two actual resolution diagrams. -/
def obj (A : CosimplicialObject C) (B : SimplicialObject C) : SSet.{v} where
  obj n := A.obj n.unop ⟶ B.obj n
  map f := ↾fun h ↦ A.map f.unop ≫ h ≫ B.map f
  map_id n := by
    ext h
    simp
  map_comp f g := by
    ext h
    simp [Category.assoc]

/-- Every simplex is an actual map between the corresponding resolution objects. -/
theorem obj_obj (A : CosimplicialObject C) (B : SimplicialObject C)
    (n : SimplexCategoryᵒᵖ) :
    (obj A B).obj n = (A.obj n.unop ⟶ B.obj n) := rfl

/-- Formula for each simplicial operator, using both original diagram maps. -/
@[simp]
theorem obj_map_apply (A : CosimplicialObject C) (B : SimplicialObject C)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (h : A.obj n.unop ⟶ B.obj n) :
    (obj A B).map f h = A.map f.unop ≫ h ≫ B.map f := rfl

/-- Precomposition by a map of the actual cosimplicial resolutions. -/
def precomp {A A' : CosimplicialObject C} (a : A ⟶ A') (B : SimplicialObject C) :
    obj A' B ⟶ obj A B where
  app n := ↾fun h ↦ a.app n.unop ≫ h
  naturality {n m} f := by
    ext h
    dsimp only [obj] at h
    change a.app m.unop ≫ (A'.map f.unop ≫ h ≫ B.map f) =
      A.map f.unop ≫ (a.app n.unop ≫ h) ≫ B.map f
    calc
      a.app m.unop ≫ (A'.map f.unop ≫ h ≫ B.map f) =
          (a.app m.unop ≫ A'.map f.unop) ≫ h ≫ B.map f := by
        simp only [Category.assoc]
      _ = (A.map f.unop ≫ a.app n.unop) ≫ h ≫ B.map f :=
        congrArg (fun k ↦ k ≫ h ≫ B.map f) (a.naturality f.unop).symm
      _ = A.map f.unop ≫ (a.app n.unop ≫ h) ≫ B.map f := by
        simp only [Category.assoc]

/-- The original cosimplicial map is used in every degree of precomposition. -/
@[simp]
theorem precomp_app_apply {A A' : CosimplicialObject C} (a : A ⟶ A')
    (B : SimplicialObject C) (n : SimplexCategoryᵒᵖ) (h : A'.obj n.unop ⟶ B.obj n) :
    (precomp a B).app n h = a.app n.unop ≫ h := rfl

/-- Postcomposition by a map of the actual simplicial resolutions. -/
def postcomp (A : CosimplicialObject C) {B B' : SimplicialObject C} (b : B ⟶ B') :
    obj A B ⟶ obj A B' where
  app n := ↾fun h ↦ h ≫ b.app n
  naturality {n m} f := by
    ext h
    dsimp only [obj] at h
    change (A.map f.unop ≫ h ≫ B.map f) ≫ b.app m =
      A.map f.unop ≫ (h ≫ b.app n) ≫ B'.map f
    calc
      (A.map f.unop ≫ h ≫ B.map f) ≫ b.app m =
          A.map f.unop ≫ h ≫ (B.map f ≫ b.app m) := by
        simp only [Category.assoc]
      _ = A.map f.unop ≫ h ≫ (b.app n ≫ B'.map f) :=
        congrArg (fun k ↦ A.map f.unop ≫ h ≫ k) (b.naturality f)
      _ = A.map f.unop ≫ (h ≫ b.app n) ≫ B'.map f := by
        simp only [Category.assoc]

/-- The original simplicial map is used in every degree of postcomposition. -/
@[simp]
theorem postcomp_app_apply (A : CosimplicialObject C) {B B' : SimplicialObject C}
    (b : B ⟶ B') (n : SimplexCategoryᵒᵖ) (h : A.obj n.unop ⟶ B.obj n) :
    (postcomp A b).app n h = h ≫ b.app n := rfl

/-- Precomposition by the identity is the identity of the entire complex. -/
@[simp]
theorem precomp_id (A : CosimplicialObject C) (B : SimplicialObject C) :
    precomp (𝟙 A) B = 𝟙 (obj A B) := by
  ext n h
  dsimp only [obj] at h
  change 𝟙 (A.obj n.unop) ≫ h = h
  exact Category.id_comp h

/-- Precomposition reverses composition of the original cosimplicial maps. -/
@[simp]
theorem precomp_comp {A A' A'' : CosimplicialObject C}
    (a : A ⟶ A') (a' : A' ⟶ A'') (B : SimplicialObject C) :
    precomp (a ≫ a') B = precomp a' B ≫ precomp a B := by
  ext n h
  dsimp only [obj] at h
  change (a.app n.unop ≫ a'.app n.unop) ≫ h =
    a.app n.unop ≫ (a'.app n.unop ≫ h)
  exact Category.assoc _ _ _

/-- Postcomposition by the identity is the identity of the entire complex. -/
@[simp]
theorem postcomp_id (A : CosimplicialObject C) (B : SimplicialObject C) :
    postcomp A (𝟙 B) = 𝟙 (obj A B) := by
  ext n h
  dsimp only [obj] at h
  change h ≫ 𝟙 (B.obj n) = h
  exact Category.comp_id h

/-- Postcomposition preserves composition of the original simplicial maps. -/
@[simp]
theorem postcomp_comp (A : CosimplicialObject C) {B B' B'' : SimplicialObject C}
    (b : B ⟶ B') (b' : B' ⟶ B'') :
    postcomp A (b ≫ b') = postcomp A b ≫ postcomp A b' := by
  ext n h
  dsimp only [obj] at h
  change h ≫ (b.app n ≫ b'.app n) = (h ≫ b.app n) ≫ b'.app n
  exact (Category.assoc _ _ _).symm

/-- Both actual resolution-map actions commute as maps of complete complexes. -/
theorem precomp_postcomp {A A' : CosimplicialObject C} (a : A ⟶ A')
    {B B' : SimplicialObject C} (b : B ⟶ B') :
    precomp a B ≫ postcomp A b = postcomp A' b ≫ precomp a B' := by
  ext n h
  dsimp only [obj] at h
  change (a.app n.unop ≫ h) ≫ b.app n = a.app n.unop ≫ (h ≫ b.app n)
  exact Category.assoc _ _ _

/-- The resolution Hom complex as a bifunctor on the actual diagram categories. -/
def bifunctor : (CosimplicialObject C)ᵒᵖ ⥤ SimplicialObject C ⥤ SSet.{v} where
  obj A :=
    { obj B := obj A.unop B
      map b := postcomp A.unop b
      map_id B := postcomp_id A.unop B
      map_comp b b' := postcomp_comp A.unop b b' }
  map a :=
    { app B := precomp a.unop B
      naturality {_ _} b := (precomp_postcomp a.unop b).symm }
  map_id A := by
    apply NatTrans.ext
    funext B
    change precomp (𝟙 A.unop) B = 𝟙 (obj A.unop B)
    exact precomp_id A.unop B
  map_comp a a' := by
    apply NatTrans.ext
    funext B
    change precomp (a ≫ a').unop B = precomp a.unop B ≫ precomp a'.unop B
    rw [unop_comp, precomp_comp]

/-- The left resolution Hom complex, with the target kept constant. -/
abbrev left (A : CosimplicialObject C) (Y : C) : SSet.{v} :=
  obj A ((SimplicialObject.const C).obj Y)

/-- The right resolution Hom complex, with the source kept constant. -/
abbrev right (X : C) (B : SimplicialObject C) : SSet.{v} :=
  obj ((CosimplicialObject.const C).obj X) B

/-- The left complex has the original Hom sets out of each cosimplicial degree. -/
theorem left_obj (A : CosimplicialObject C) (Y : C) (n : SimplexCategoryᵒᵖ) :
    (left A Y).obj n = (A.obj n.unop ⟶ Y) := rfl

/-- The right complex has the original Hom sets into each simplicial degree. -/
theorem right_obj (X : C) (B : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    (right X B).obj n = (X ⟶ B.obj n) := rfl

/-- The simplicial operator in the left complex is the original precomposition. -/
theorem left_map_apply (A : CosimplicialObject C) (Y : C)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (h : A.obj n.unop ⟶ Y) :
    (left A Y).map f h = A.map f.unop ≫ h := by
  change (A.map f.unop ≫ h ≫ 𝟙 Y) = A.map f.unop ≫ h
  simp only [Category.comp_id]

/-- The simplicial operator in the right complex is the original postcomposition. -/
theorem right_map_apply (X : C) (B : SimplicialObject C)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (h : X ⟶ B.obj n) :
    (right X B).map f h = h ≫ B.map f := by
  change (𝟙 X ≫ h ≫ B.map f) = h ≫ B.map f
  exact Category.id_comp (h ≫ B.map f)

/-- The given cosimplicial augmentation compares the right complex with the diagonal. -/
def fromAugmentation {A : CosimplicialObject C} {X : C}
    (a : A ⟶ (CosimplicialObject.const C).obj X) (B : SimplicialObject C) :
    right X B ⟶ obj A B := precomp a B

/-- Formula retaining every component of the original cosimplicial augmentation. -/
@[simp]
theorem fromAugmentation_app_apply {A : CosimplicialObject C} {X : C}
    (a : A ⟶ (CosimplicialObject.const C).obj X) (B : SimplicialObject C)
    (n : SimplexCategoryᵒᵖ) (h : X ⟶ B.obj n) :
    (fromAugmentation a B).app n h = a.app n.unop ≫ h := rfl

/-- The given simplicial coaugmentation compares the left complex with the diagonal. -/
def fromCoaugmentation (A : CosimplicialObject C) {Y : C} {B : SimplicialObject C}
    (b : (SimplicialObject.const C).obj Y ⟶ B) : left A Y ⟶ obj A B :=
  postcomp A b

/-- Formula retaining every component of the original simplicial coaugmentation. -/
@[simp]
theorem fromCoaugmentation_app_apply (A : CosimplicialObject C) {Y : C}
    {B : SimplicialObject C} (b : (SimplicialObject.const C).obj Y ⟶ B)
    (n : SimplexCategoryᵒᵖ) (h : A.obj n.unop ⟶ Y) :
    (fromCoaugmentation A b).app n h = h ≫ b.app n := rfl

/-- The original augmentation comparison is natural in every simplicial resolution map. -/
theorem fromAugmentation_naturality_target {A : CosimplicialObject C} {X : C}
    (a : A ⟶ (CosimplicialObject.const C).obj X) {B B' : SimplicialObject C}
    (b : B ⟶ B') :
    fromAugmentation a B ≫ postcomp A b =
      postcomp ((CosimplicialObject.const C).obj X) b ≫ fromAugmentation a B' :=
  precomp_postcomp a b

/-- An actual augmentation square retains both the original source map and resolution map. -/
theorem fromAugmentation_naturality_source {A A' : CosimplicialObject C} {X X' : C}
    (s : A ⟶ A') (p : X ⟶ X') (a : A ⟶ (CosimplicialObject.const C).obj X)
    (a' : A' ⟶ (CosimplicialObject.const C).obj X')
    (ha : s ≫ a' = a ≫ (CosimplicialObject.const C).map p) (B : SimplicialObject C) :
    precomp ((CosimplicialObject.const C).map p) B ≫ fromAugmentation a B =
      fromAugmentation a' B ≫ precomp s B := by
  change precomp ((CosimplicialObject.const C).map p) B ≫ precomp a B =
    precomp a' B ≫ precomp s B
  rw [← precomp_comp, ← precomp_comp, ha]

/-- The original coaugmentation comparison is natural in every cosimplicial resolution map. -/
theorem fromCoaugmentation_naturality_source {A A' : CosimplicialObject C}
    (a : A ⟶ A') {Y : C} {B : SimplicialObject C}
    (b : (SimplicialObject.const C).obj Y ⟶ B) :
    precomp a ((SimplicialObject.const C).obj Y) ≫ fromCoaugmentation A b =
      fromCoaugmentation A' b ≫ precomp a B := precomp_postcomp a b

/-- An actual coaugmentation square retains both the original target map and resolution map. -/
theorem fromCoaugmentation_naturality_target (A : CosimplicialObject C)
    {Y Y' : C} {B B' : SimplicialObject C} (q : Y ⟶ Y') (t : B ⟶ B')
    (b : (SimplicialObject.const C).obj Y ⟶ B)
    (b' : (SimplicialObject.const C).obj Y' ⟶ B')
    (hb : (SimplicialObject.const C).map q ≫ b' = b ≫ t) :
    fromCoaugmentation A b ≫ postcomp A t =
      postcomp A ((SimplicialObject.const C).map q) ≫ fromCoaugmentation A b' := by
  change postcomp A b ≫ postcomp A t =
    postcomp A ((SimplicialObject.const C).map q) ≫ postcomp A b'
  rw [← postcomp_comp, ← postcomp_comp, hb]

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]

/-- Actual functorial resolution diagrams induce a mapping bifunctor on their input categories. -/
def ofFunctors (A : D ⥤ CosimplicialObject C) (B : E ⥤ SimplicialObject C) :
    Dᵒᵖ ⥤ E ⥤ SSet.{v} :=
  A.op ⋙ bifunctor ⋙ (Functor.whiskeringLeft E (SimplicialObject C) SSet.{v}).obj B

/-- The resolution bifunctor uses the original objects of both input functors. -/
theorem ofFunctors_obj (A : D ⥤ CosimplicialObject C) (B : E ⥤ SimplicialObject C)
    (X : D) (Y : E) :
    ((ofFunctors A B).obj (op X)).obj Y = obj (A.obj X) (B.obj Y) := rfl

/-- Source action of the complete resolution bifunctor uses the given cosimplicial map. -/
theorem ofFunctors_map_source (A : D ⥤ CosimplicialObject C)
    (B : E ⥤ SimplicialObject C) {X X' : D} (f : X ⟶ X') (Y : E) :
    ((ofFunctors A B).map f.op).app Y = precomp (A.map f) (B.obj Y) := rfl

/-- Target action of the complete resolution bifunctor uses the given simplicial map. -/
theorem ofFunctors_map_target (A : D ⥤ CosimplicialObject C)
    (B : E ⥤ SimplicialObject C) (X : D) {Y Y' : E} (g : Y ⟶ Y') :
    ((ofFunctors A B).obj (op X)).map g = postcomp (A.obj X) (B.map g) := rfl

/-- Every original source input morphism retains its original degreewise resolution action. -/
@[simp]
theorem ofFunctors_map_source_app_apply (A : D ⥤ CosimplicialObject C)
    (B : E ⥤ SimplicialObject C) {X X' : D} (f : X ⟶ X') (Y : E)
    (n : SimplexCategoryᵒᵖ) (h : (A.obj X').obj n.unop ⟶ (B.obj Y).obj n) :
    (((ofFunctors A B).map f.op).app Y).app n h = (A.map f).app n.unop ≫ h := rfl

/-- Every original target input morphism retains its original degreewise resolution action. -/
@[simp]
theorem ofFunctors_map_target_app_apply (A : D ⥤ CosimplicialObject C)
    (B : E ⥤ SimplicialObject C) (X : D) {Y Y' : E} (g : Y ⟶ Y')
    (n : SimplexCategoryᵒᵖ) (h : (A.obj X).obj n.unop ⟶ (B.obj Y).obj n) :
    (((ofFunctors A B).obj (op X)).map g).app n h = h ≫ (B.map g).app n := rfl

/-- Both original input morphisms commute on the complete resolution mapping bifunctor. -/
theorem ofFunctors_naturality (A : D ⥤ CosimplicialObject C)
    (B : E ⥤ SimplicialObject C) {X X' : D} (f : X ⟶ X') {Y Y' : E} (g : Y ⟶ Y') :
    ((ofFunctors A B).map f.op).app Y ≫ ((ofFunctors A B).obj (op X)).map g =
      ((ofFunctors A B).obj (op X')).map g ≫ ((ofFunctors A B).map f.op).app Y' :=
  precomp_postcomp (A.map f) (B.map g)

end HomotopicalAlgebra.ResolutionHomComplex

end
end

section



/-!
# Resolution Hom and the canonical enrichment on simplicial objects

The canonical simplicial Hom out of a constant simplicial object is the
original right resolution Hom complex. The full isomorphism uses the native
structured functor Hom: a map into degree n is sent to its compositions with
every original simplex operator, and the inverse evaluates at the identity.
No completeness or model structure on the coefficient category is needed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe u v

open CategoryTheory Opposite

namespace HomotopicalAlgebra.ResolutionHomComplex.CanonicalEnrichment

variable {C : Type u} [Category.{v} C]

/-- The complete represented structured Hom uses all original target simplex maps. -/
def forward (X : C) (B : SimplicialObject C) (n : SimplexCategoryᵒᵖ) (h : X ⟶ B.obj n) :
    (Functor.functorHom ((SimplicialObject.const C).obj X) B).obj n where
  app k g := h ≫ B.map g
  naturality f g := by simp [Category.assoc]

/-- The original degreewise map is recovered by evaluation at the identity. -/
def backward (X : C) (B : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
    (x : (Functor.functorHom ((SimplicialObject.const C).obj X) B).obj n) :
    X ⟶ B.obj n := x.app n (𝟙 n)

/-- Every forward coordinate retains the full original simplex map. -/
@[simp]
theorem forward_app (X : C) (B : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
    (h : X ⟶ B.obj n) (k : SimplexCategoryᵒᵖ) (g : n ⟶ k) :
    (forward X B n h).app k g = h ≫ B.map g := rfl

/-- The inverse coordinate is the original map at the identity simplex operator. -/
@[simp]
theorem backward_eq (X : C) (B : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
    (x : (Functor.functorHom ((SimplicialObject.const C).obj X) B).obj n) :
    backward X B n x = x.app n (𝟙 n) := rfl

/-- Identity evaluation recovers every original degreewise map. -/
theorem backward_forward (X : C) (B : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
    (h : X ⟶ B.obj n) : backward X B n (forward X B n h) = h := by
  simp [backward]

/-- Original structured naturality recovers every entire native functor Hom datum. -/
theorem forward_backward (X : C) (B : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
    (x : (Functor.functorHom ((SimplicialObject.const C).obj X) B).obj n) :
    forward X B n (backward X B n x) = x := by
  apply Functor.functorHom_ext
  intro k g
  simpa [backward] using (x.naturality g (𝟙 n)).symm

/-- The degreewise bijection is the original ordinary represented-Hom bijection. -/
def simplexEquiv (X : C) (B : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    (X ⟶ B.obj n) ≃ (Functor.functorHom ((SimplicialObject.const C).obj X) B).obj n where
  toFun := forward X B n
  invFun := backward X B n
  left_inv := backward_forward X B n
  right_inv := forward_backward X B n

/-- The full native simplicial Hom is isomorphic to the original right resolution complex. -/
def rightIso (X : C) (B : SimplicialObject C) :
    right X B ≅ SimplicialCategory.sHom ((SimplicialObject.const C).obj X) B :=
  NatIso.ofComponents (fun n => (simplexEquiv X B n).toIso) (by
    intro n m f
    ext h
    apply Functor.functorHom_ext
    intro k g
    change (𝟙 X ≫ h ≫ B.map f) ≫ B.map g = h ≫ B.map (f ≫ g)
    rw [B.map_comp, Category.id_comp]
    exact Category.assoc _ _ _)

/-- The forward isomorphism keeps every original represented coordinate. -/
@[simp]
theorem rightIso_hom_app (X : C) (B : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
    (h : X ⟶ B.obj n) (k : SimplexCategoryᵒᵖ) (g : n ⟶ k) :
    ((rightIso X B).hom.app n h).app k g = h ≫ B.map g := rfl

/-- The whole inverse isomorphism evaluates the same original identity coordinate. -/
@[simp]
theorem rightIso_inv_app (X : C) (B : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
    (x : (Functor.functorHom ((SimplicialObject.const C).obj X) B).obj n) :
    (rightIso X B).inv.app n x = x.app n (𝟙 n) := rfl

/-- Every original simplicial operator is preserved by the entire isomorphism. -/
theorem rightIso_naturality (X : C) (B : SimplicialObject C)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (right X B).map f ≫ (rightIso X B).hom.app m =
      (rightIso X B).hom.app n ≫
        (SimplicialCategory.sHom ((SimplicialObject.const C).obj X) B).map f :=
  (rightIso X B).hom.naturality f

/-- Native canonical enriched target whiskering is the original structured-Hom postcomposition. -/
theorem canonical_postcomp_app {F B B' : SimplicialObject C} (b : B ⟶ B')
    (n : SimplexCategoryᵒᵖ) (x : (Functor.functorHom F B).obj n)
    (k : SimplexCategoryᵒᵖ) (g : n ⟶ k) :
    ((((SimplicialCategory.sHomFunctor (SimplicialObject C)).obj (op F)).map b).app n x).app k g =
      x.app k g ≫ b.app k := rfl

/-- Native canonical enriched source whiskering keeps every component of the original source map. -/
theorem canonical_precomp_app {F F' B : SimplicialObject C} (f : F ⟶ F')
    (n : SimplexCategoryᵒᵖ) (x : (Functor.functorHom F' B).obj n)
    (k : SimplexCategoryᵒᵖ) (g : n ⟶ k) :
    ((((SimplicialCategory.sHomFunctor (SimplicialObject C)).map f.op).app B).app n x).app k g =
      f.app k ≫ x.app k g := rfl

/-- The complete original simplicial target map commutes with the entire canonical isomorphism. -/
theorem rightIso_natural_target (X : C) {B B' : SimplicialObject C} (b : B ⟶ B') :
    postcomp ((CosimplicialObject.const C).obj X) b ≫ (rightIso X B').hom =
      (rightIso X B).hom ≫
        ((SimplicialCategory.sHomFunctor (SimplicialObject C)).obj
          (op ((SimplicialObject.const C).obj X))).map b := by
  ext n h
  apply Functor.functorHom_ext
  intro k g
  change (h ≫ b.app n) ≫ B'.map g = (h ≫ B.map g) ≫ b.app k
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => h ≫ f) (b.naturality g).symm).trans (Category.assoc _ _ _).symm)

/-- Every original ordinary source map is preserved as a whole map of the canonical enrichment. -/
theorem rightIso_natural_source {X X' : C} (f : X ⟶ X') (B : SimplicialObject C) :
    precomp ((CosimplicialObject.const C).map f) B ≫ (rightIso X B).hom =
      (rightIso X' B).hom ≫
        ((SimplicialCategory.sHomFunctor (SimplicialObject C)).map
          ((SimplicialObject.const C).map f).op).app B := by
  ext n h
  apply Functor.functorHom_ext
  intro k g
  change (f ≫ h) ≫ B.map g = f ≫ (h ≫ B.map g)
  exact Category.assoc _ _ _

/-- The right resolution bifunctor is the original resolution construction on constant sources. -/
def rightBifunctor : Cᵒᵖ ⥤ SimplicialObject C ⥤ SSet.{v} :=
  (CosimplicialObject.const C).op ⋙ bifunctor

/-- The comparison bifunctor is the actual native simplicial enrichment on the original constants.
-/
def canonicalBifunctor : Cᵒᵖ ⥤ SimplicialObject C ⥤ SSet.{v} :=
  (SimplicialObject.const C).op ⋙ SimplicialCategory.sHomFunctor (SimplicialObject C)

/-- Both original source and target actions give a natural isomorphism of complete bifunctors. -/
def rightBifunctorIso : rightBifunctor (C := C) ≅ canonicalBifunctor (C := C) :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun B => rightIso X.unop B)
      (fun b => rightIso_natural_target X.unop b)) (by
    intro X X' f
    apply NatTrans.ext
    funext B
    exact rightIso_natural_source f.unop B)

/-- The entire natural bifunctor isomorphism uses the original represented-map component. -/
theorem rightBifunctorIso_app (X : C) (B : SimplicialObject C) :
    ((rightBifunctorIso (C := C)).app (op X)).app B = rightIso X B := rfl

/-- The inverse at degree zero is the degree-zero component of the original represented map. -/
theorem rightIso_inv_zero_of_natTrans (X : C) (B : SimplicialObject C)
    (b : (SimplicialObject.const C).obj X ⟶ B) :
    (rightIso X B).inv.app (op (SimplexCategory.mk 0))
      ((SimplicialCategory.homEquiv' ((SimplicialObject.const C).obj X) B) b) =
      b.app (op (SimplexCategory.mk 0)) := rfl

/-- The original represented map also recovers the same forward degree-zero simplex. -/
theorem rightIso_hom_zero_of_natTrans (X : C) (B : SimplicialObject C)
    (b : (SimplicialObject.const C).obj X ⟶ B) :
    (rightIso X B).hom.app (op (SimplexCategory.mk 0)) (b.app (op (SimplexCategory.mk 0))) =
      (SimplicialCategory.homEquiv' ((SimplicialObject.const C).obj X) B) b := by
  apply Functor.functorHom_ext
  intro k g
  change b.app (op (SimplexCategory.mk 0)) ≫ B.map g = b.app k
  simpa using (b.naturality g).symm

end HomotopicalAlgebra.ResolutionHomComplex.CanonicalEnrichment

end
end
end

section



/-!
# Original proper simplex faces and their boundary maps

Every original proper mono latching object maps by the same represented
simplex map into the actual standard boundary. Every original non-surjective
simplex has its actual Reedy epi/image/mono factor in that same face category.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits MorphismProperty Opposite Simplicial

namespace SSet.StandardSimplexBoundaryColimit

/-- An original smaller simplex cannot surject onto the larger original simplex. -/
theorem not_surjective_of_lt {K j : SimplexCategory} (i : K ⟶ j) (hi : K.len < j.len) :
    ¬ Function.Surjective i.toOrderHom := by
  intro hs
  let _ : Epi i := SimplexCategory.epi_iff_surjective.mpr hs
  exact not_le_of_gt hi (SimplexCategory.len_le_of_epi i)

/-- Every actual original latching arrow is an original simplex mono. -/
instance latchingArrow_mono {j : SimplexCategory} (a : SimplexCategory.reedy.Latching j) :
    Mono (SimplexCategory.reedy.latchingArrow a) :=
  (SimplexCategory.reedy_direct _).mp a.obj.hom.property

/-- Every original proper latching face has its actual strictly smaller simplex degree. -/
theorem latchingSource_lt {j : SimplexCategory} (a : SimplexCategory.reedy.Latching j) :
    (SimplexCategory.reedy.latchingSource a).len < j.len := a.property

/-- The original proper mono is an actual object of the same original latching category. -/
@[implicit_reducible]
def faceObject {K j : SimplexCategory} (i : K ⟶ j) [Mono i] (hi : K.len < j.len) :
    SimplexCategory.reedy.Latching j :=
  ⟨Over.mk ⟨i, (SimplexCategory.reedy_direct i).mpr inferInstance⟩, hi⟩

/-- The original proper mono leg factors through the actual standard boundary. -/
def faceMap {K j : SimplexCategory} (i : K ⟶ j) (hi : K.len < j.len) :
    stdSimplex.{u}.obj K ⟶ (boundary j.len : SSet.{u}) :=
  Subcomplex.lift (stdSimplex.map i) (by
    intro m x hx
    obtain ⟨y, rfl⟩ := hx
    change ¬ Function.Surjective (i.toOrderHom.comp (stdSimplex.objEquiv y).toOrderHom)
    intro hs
    exact not_surjective_of_lt i hi (Function.Surjective.of_comp hs))

/-- Every original proper mono leg retains the same complete represented simplex map. -/
@[reassoc]
theorem faceMap_ι {K j : SimplexCategory} (i : K ⟶ j) (hi : K.len < j.len) :
    faceMap.{u} i hi ≫ (boundary j.len).ι = stdSimplex.map i := rfl

/-- Every original incoming face supplies its unchanged mono map to the actual boundary. -/
@[implicit_reducible]
def boundaryCocone (j : SimplexCategory) :
    Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j) where
  pt := boundary j.len
  ι.app a := faceMap (SimplexCategory.reedy.latchingArrow a) (latchingSource_lt a)
  ι.naturality a b f := by
    change stdSimplex.map (SimplexCategory.reedy.latchingComparison f) ≫
      faceMap (SimplexCategory.reedy.latchingArrow b) (latchingSource_lt b) =
        faceMap (SimplexCategory.reedy.latchingArrow a) (latchingSource_lt a) ≫ 𝟙 _
    rw [Category.comp_id]
    apply (cancel_mono (boundary j.len).ι).mp
    rw [Category.assoc, faceMap_ι, faceMap_ι]
    change stdSimplex.map (SimplexCategory.reedy.latchingComparison f) ≫
      stdSimplex.map (SimplexCategory.reedy.latchingArrow b) =
        stdSimplex.map (SimplexCategory.reedy.latchingArrow a)
    rw [← stdSimplex.map_comp, SimplexCategory.reedy.latchingComparison_arrow]

/-- Each actual caller face keeps its full original inclusion into the standard simplex. -/
@[reassoc]
theorem boundaryCocone_ι {j : SimplexCategory} (a : SimplexCategory.reedy.Latching j) :
    (boundaryCocone.{u} j).ι.app a ≫ (boundary j.len).ι =
      stdSimplex.map (SimplexCategory.reedy.latchingArrow a) :=
  faceMap_ι (SimplexCategory.reedy.latchingArrow a) (latchingSource_lt a)

/-- The original Reedy image factor has the actual original mono as its direct map. -/
instance factor_directMap_mono {M j : SimplexCategory} (g : M ⟶ j) :
    Mono (SimplexCategory.reedy.factor g).directMap :=
  (SimplexCategory.reedy_direct _).mp (SimplexCategory.reedy.factor g).direct_mem

/-- The original Reedy image factor has the actual original epi as its inverse map. -/
instance factor_inverseMap_epi {M j : SimplexCategory} (g : M ⟶ j) :
    Epi (SimplexCategory.reedy.factor g).inverseMap :=
  (SimplexCategory.reedy_inverse _).mp (SimplexCategory.reedy.factor g).inverse_mem

/-- Every original non-surjective simplex has a genuinely proper original Reedy image mono. -/
theorem factor_middle_lt {M j : SimplexCategory} (g : M ⟶ j)
    (hg : ¬ Function.Surjective g.toOrderHom) : (SimplexCategory.reedy.factor g).middle.len <
      j.len := by
  have hl := SimplexCategory.len_le_of_mono (SimplexCategory.reedy.factor g).directMap
  apply lt_of_le_of_ne hl
  intro he
  let _ : IsIso (SimplexCategory.reedy.factor g).directMap :=
    (SimplexCategory.isIso_iff_of_mono _).mpr he
  have hi : Epi g := by
    rw [← (SimplexCategory.reedy.factor g).fac]
    infer_instance
  exact hg (SimplexCategory.epi_iff_surjective.mp hi)

/-- Evaluate the original epi factor as a simplex in the caller's original proper-mono face leg. -/
def evaluateFactor {j : SimplexCategory}
    (s : Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j)) {M : SimplexCategory}
    (g : M ⟶ j)
    (f : ReedyFactorization (monomorphisms SimplexCategory) (epimorphisms SimplexCategory) g)
    (hf : f.middle.len < j.len) : s.pt.obj (op M) := by
  let _ : Mono f.directMap := f.direct_mem
  exact (s.ι.app (faceObject f.directMap hf)).app (op M)
    (stdSimplex.objEquiv.symm f.inverseMap)

/-- Original unique epi/mono factorization makes the whole evaluated caller value independent of the
factor. -/
theorem evaluateFactor_unique {j : SimplexCategory}
    (s : Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j)) {M : SimplexCategory}
    (g : M ⟶ j)
    (f f' : ReedyFactorization (monomorphisms SimplexCategory) (epimorphisms SimplexCategory) g)
    (hf : f.middle.len < j.len) (hf' : f'.middle.len < j.len) :
    evaluateFactor s g f hf = evaluateFactor s g f' hf' := by
  have h : f = f' := SimplexCategory.reedy.factor_unique g f f'
  subst f'
  rfl

/-- The actual boundary-simplex value uses its original Reedy epi and proper image mono. -/
def value {j : SimplexCategory}
    (s : Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j)) {M : SimplexCategory}
    (g : M ⟶ j) (hg : ¬ Function.Surjective g.toOrderHom) : s.pt.obj (op M) :=
  evaluateFactor s g (SimplexCategory.reedy.factor g) (factor_middle_lt g hg)

/-- Any actual original proper epi/mono factor gives the same whole boundary-simplex value. -/
theorem value_eq_evaluateFactor {j : SimplexCategory}
    (s : Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j)) {M : SimplexCategory}
    (g : M ⟶ j) (hg : ¬ Function.Surjective g.toOrderHom)
    (f : ReedyFactorization (monomorphisms SimplexCategory) (epimorphisms SimplexCategory) g)
    (hf : f.middle.len < j.len) : value s g hg = evaluateFactor s g f hf :=
  evaluateFactor_unique s g _ f _ hf

end SSet.StandardSimplexBoundaryColimit

end
end
end

section



/-!
# Original epi/image/mono values of the standard boundary colimit

Every incoming simplex is factored through its actual original image. The
original unique Reedy factorization and original face comparison triangles
make its caller-cocone value independent of the chosen factorization and
natural under every original simplex operator.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits MorphismProperty Opposite Simplicial

namespace SSet.StandardSimplexBoundaryColimit

/-- Composing the actual epi/image/mono factor of an incoming simplex with its original face. -/
@[implicit_reducible]
def compositeFactor {M K j : SimplexCategory} (g : M ⟶ j) (x : M ⟶ K)
    (i : K ⟶ j) [Mono i] (hx : x ≫ i = g) :
    ReedyFactorization (monomorphisms SimplexCategory) (epimorphisms SimplexCategory) g where
  Z := (SimplexCategory.reedy.factor x).middle
  i := (SimplexCategory.reedy.factor x).inverseMap
  p := (SimplexCategory.reedy.factor x).directMap ≫ i
  hi := (SimplexCategory.reedy.factor x).inverse_mem
  hp := by
    apply (SimplexCategory.reedy_direct _).mpr
    infer_instance
  fac := by rw [← Category.assoc, (SimplexCategory.reedy.factor x).fac, hx]

/-- The composed factor retains its original actual mono direct map. -/
instance compositeFactor_directMap_mono {M K j : SimplexCategory} (g : M ⟶ j) (x : M ⟶ K)
    (i : K ⟶ j) [Mono i] (hx : x ≫ i = g) : Mono (compositeFactor g x i hx).directMap :=
  (compositeFactor g x i hx).direct_mem

/-- The actual incoming image remains below the original proper face target degree. -/
theorem compositeFactor_middle_lt {M K j : SimplexCategory} (g : M ⟶ j) (x : M ⟶ K)
    (i : K ⟶ j) [Mono i] (hi : K.len < j.len) (hx : x ≫ i = g) :
    (compositeFactor g x i hx).middle.len < j.len :=
  (SimplexCategory.len_le_of_mono (SimplexCategory.reedy.factor x).directMap).trans_lt hi

/-- The actual original image mono gives the unchanged original proper-face comparison triangle. -/
def compositeFaceComparison {M K j : SimplexCategory} (g : M ⟶ j) (x : M ⟶ K)
    (i : K ⟶ j) [Mono i] (hi : K.len < j.len) (hx : x ≫ i = g) :
    faceObject (compositeFactor g x i hx).directMap (compositeFactor_middle_lt g x i hi hx) ⟶
      faceObject i hi :=
  ⟨Over.homMk ⟨(SimplexCategory.reedy.factor x).directMap,
    (SimplexCategory.reedy_direct _).mpr (factor_directMap_mono x)⟩ (by
      apply WideSubcategory.hom_ext
      rfl)⟩

/-- Evaluating the original composed image factor recovers the whole original incoming face value.
-/
theorem evaluateFactor_composite {j : SimplexCategory}
    (s : Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j)) {M K : SimplexCategory}
    (g : M ⟶ j) (x : M ⟶ K) (i : K ⟶ j) [Mono i]
    (hi : K.len < j.len) (hx : x ≫ i = g) :
    evaluateFactor s g (compositeFactor g x i hx) (compositeFactor_middle_lt g x i hi hx) =
      (s.ι.app (faceObject i hi)).app (op M) (stdSimplex.objEquiv.symm x) := by
  let f := SimplexCategory.reedy.factor x
  have H := s.w (compositeFaceComparison g x i hi hx)
  have hv := ConcreteCategory.congr_hom (congrArg (fun z ↦ z.app (op M)) H)
    (stdSimplex.objEquiv.symm f.inverseMap)
  change (s.ι.app (faceObject i hi)).app (op M)
      ((stdSimplex.map f.directMap).app (op M) (stdSimplex.objEquiv.symm f.inverseMap)) =
    (s.ι.app (faceObject (f.directMap ≫ i) (compositeFactor_middle_lt g x i hi hx))).app (op M)
      (stdSimplex.objEquiv.symm f.inverseMap) at hv
  rw [← stdSimplex.objEquiv_symm_comp, f.fac] at hv
  exact hv.symm

/-- Original unique Reedy factorization recovers every incoming simplex on its original proper face.
-/
theorem value_eq_face {j : SimplexCategory}
    (s : Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j)) {M K : SimplexCategory}
    (g : M ⟶ j) (hg : ¬ Function.Surjective g.toOrderHom) (x : M ⟶ K)
    (i : K ⟶ j) [Mono i] (hi : K.len < j.len) (hx : x ≫ i = g) :
    value s g hg = (s.ι.app (faceObject i hi)).app (op M) (stdSimplex.objEquiv.symm x) := by
  rw [value_eq_evaluateFactor s g hg (compositeFactor g x i hx) (compositeFactor_middle_lt g x i hi
    hx)]
  exact evaluateFactor_composite s g x i hi hx

/-- The original identity source comparison retains any original latching face object. -/
def faceToOriginal {j : SimplexCategory} (a : SimplexCategory.reedy.Latching j) :
    faceObject (SimplexCategory.reedy.latchingArrow a) (latchingSource_lt a) ⟶ a :=
  ⟨Over.homMk ⟨𝟙 _, (SimplexCategory.reedy_direct _).mpr inferInstance⟩ (by
    apply WideSubcategory.hom_ext
    exact Category.id_comp _)⟩

/-- The original source identity comparison recovers the same complete caller face leg. -/
theorem faceToOriginal_leg {j : SimplexCategory}
    (s : Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j))
    (a : SimplexCategory.reedy.Latching j) :
    s.ι.app (faceObject (SimplexCategory.reedy.latchingArrow a) (latchingSource_lt a)) = s.ι.app
      a := by
  have H := s.w (faceToOriginal a)
  change stdSimplex.map (𝟙 (SimplexCategory.reedy.latchingSource a)) ≫ s.ι.app a =
    s.ι.app (faceObject (SimplexCategory.reedy.latchingArrow a) (latchingSource_lt a)) at H
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at H
  exact H.symm

/-- Every original caller leg is retained, for every simplex of that original face. -/
theorem value_eq_original_leg {j : SimplexCategory}
    (s : Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j)) {M : SimplexCategory}
    (g : M ⟶ j) (hg : ¬ Function.Surjective g.toOrderHom)
    (a : SimplexCategory.reedy.Latching j) (x : M ⟶ SimplexCategory.reedy.latchingSource a)
    (hx : x ≫ SimplexCategory.reedy.latchingArrow a = g) :
    value s g hg = (s.ι.app a).app (op M) (stdSimplex.objEquiv.symm x) := by
  have H := value_eq_face s g hg x (SimplexCategory.reedy.latchingArrow a) (latchingSource_lt a) hx
  have he := faceToOriginal_leg s a
  exact H.trans (ConcreteCategory.congr_hom (congrArg (fun z ↦ z.app (op M)) he)
    (stdSimplex.objEquiv.symm x))

/-- Every original simplex operator retains the full original image-factor value. -/
theorem value_operator {j : SimplexCategory}
    (s : Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j)) {M M' : SimplexCategory}
    (g : M ⟶ j) (hg : ¬ Function.Surjective g.toOrderHom) (θ : M' ⟶ M)
    (hg' : ¬ Function.Surjective (θ ≫ g).toOrderHom) :
    s.pt.map θ.op (value s g hg) = value s (θ ≫ g) hg' := by
  let f := SimplexCategory.reedy.factor g
  let a := faceObject f.directMap (factor_middle_lt g hg)
  have hv := value_eq_face s (θ ≫ g) hg' (θ ≫ f.inverseMap) f.directMap (factor_middle_lt g hg)
    (by rw [Category.assoc, f.fac])
  have H := (s.ι.app a).naturality θ.op
  have ht := ConcreteCategory.congr_hom H (stdSimplex.objEquiv.symm f.inverseMap)
  change (s.ι.app a).app (op M')
      ((stdSimplex.obj f.middle).map θ.op (stdSimplex.objEquiv.symm f.inverseMap)) =
    s.pt.map θ.op ((s.ι.app a).app (op M) (stdSimplex.objEquiv.symm f.inverseMap)) at ht
  rw [stdSimplex.map_objEquiv_symm] at ht
  exact ht.symm.trans hv.symm

end SSet.StandardSimplexBoundaryColimit

end
end
end

section



/-!
# The actual standard boundary is the original Reedy face colimit

Every boundary simplex is evaluated through its original epi/image/mono
factorization. Original face triangles and unique factorization give all
simplex-operator naturality and every original caller cocone leg. This
constructs the complete colimit uniformly, including the zero boundary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits MorphismProperty Opposite Simplicial

namespace SSet.StandardSimplexBoundaryColimit

/-- The actual mediator evaluates each boundary simplex through its original proper image face. -/
def desc {j : SimplexCategory}
    (s : Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j)) :
    (boundary j.len : SSet.{u}) ⟶ s.pt where
  app m := ↾fun x ↦ value s (stdSimplex.objEquiv x.val) x.property
  naturality m m' θ := by
    apply ConcreteCategory.hom_ext
    intro x
    have hg : ¬ Function.Surjective (stdSimplex.objEquiv x.val).toOrderHom := x.property
    have hg' : ¬ Function.Surjective (θ.unop ≫ stdSimplex.objEquiv x.val).toOrderHom := by
      intro hs
      exact hg (Function.Surjective.of_comp hs)
    change value s (θ.unop ≫ stdSimplex.objEquiv x.val) hg' =
      s.pt.map θ (value s (stdSimplex.objEquiv x.val) hg)
    exact (value_operator s (stdSimplex.objEquiv x.val) hg θ.unop hg').symm

/-- The actual mediator retains every simplex on every original proper mono face. -/
@[reassoc]
theorem desc_fac {j : SimplexCategory}
    (s : Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j))
    (a : SimplexCategory.reedy.Latching j) : (boundaryCocone.{u} j).ι.app a ≫ desc s = s.ι.app
      a := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  let g := stdSimplex.objEquiv x ≫ SimplexCategory.reedy.latchingArrow a
  have hg : ¬ Function.Surjective g.toOrderHom := by
    intro hs
    exact not_surjective_of_lt (SimplexCategory.reedy.latchingArrow a) (latchingSource_lt a)
      (Function.Surjective.of_comp hs)
  change value s g hg = (s.ι.app a).app m x
  have H := value_eq_original_leg s g hg a (stdSimplex.objEquiv x) rfl
  simpa only [Equiv.symm_apply_apply] using H

/-- The original image epi and proper mono represent every boundary simplex on its original face. -/
theorem image_face_simplex {j : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (x : (boundary.{u} j.len).obj m) :
    let g := stdSimplex.objEquiv x.val
    let a := faceObject (SimplexCategory.reedy.factor g).directMap (factor_middle_lt g x.property)
    ((boundaryCocone.{u} j).ι.app a).app m
      (stdSimplex.objEquiv.symm (SimplexCategory.reedy.factor g).inverseMap) = x := by
  dsimp only
  apply Subtype.ext
  change stdSimplex.objEquiv.symm
    ((SimplexCategory.reedy.factor (stdSimplex.objEquiv x.val)).inverseMap ≫
      (SimplexCategory.reedy.factor (stdSimplex.objEquiv x.val)).directMap) = x.val
  rw [(SimplexCategory.reedy.factor (stdSimplex.objEquiv x.val)).fac, Equiv.symm_apply_apply]

/-- Every mediator is uniquely determined by all original proper mono face legs. -/
theorem desc_unique {j : SimplexCategory}
    (s : Cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j))
    (k : (boundary j.len : SSet.{u}) ⟶ s.pt)
    (hk : ∀ a, (boundaryCocone.{u} j).ι.app a ≫ k = s.ι.app a) : k = desc s := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  let g := stdSimplex.objEquiv x.val
  let f := SimplexCategory.reedy.factor g
  let a := faceObject f.directMap (factor_middle_lt g x.property)
  have H := ConcreteCategory.congr_hom (congrArg (fun z ↦ z.app m) (hk a))
    (stdSimplex.objEquiv.symm f.inverseMap)
  change k.app m (((boundaryCocone.{u} j).ι.app a).app m (stdSimplex.objEquiv.symm f.inverseMap)) =
    (s.ι.app a).app m (stdSimplex.objEquiv.symm f.inverseMap) at H
  have hx := image_face_simplex x
  change ((boundaryCocone.{u} j).ι.app a).app m (stdSimplex.objEquiv.symm f.inverseMap) = x at hx
  rw [hx] at H
  exact H

/-- The original standard-simplex Reedy face cocone is genuinely colimiting in every universe and
degree. -/
def isColimit (j : SimplexCategory) : IsColimit (boundaryCocone.{u} j) where
  desc := desc
  fac := desc_fac
  uniq := desc_unique

/-- The actual original latching colimit is the complete original standard boundary. -/
def colimitIso (j : SimplexCategory) :
    colimit (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j) ≅ (boundary j.len :
      SSet.{u}) :=
  colimit.isoColimitCocone ⟨boundaryCocone.{u} j, isColimit.{u} j⟩

/-- Every original colimit injection retains its whole original proper mono boundary leg. -/
@[reassoc]
theorem colimitIso_ι_hom {j : SimplexCategory} (a : SimplexCategory.reedy.Latching j) :
    colimit.ι (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j) a ≫ (colimitIso.{u} j).hom =
      (boundaryCocone.{u} j).ι.app a :=
  colimit.isoColimitCocone_ι_hom ⟨boundaryCocone.{u} j, isColimit.{u} j⟩ a

/-- Every original boundary face recovers the same original latching colimit injection under the
inverse. -/
@[reassoc]
theorem colimitIso_leg_inv {j : SimplexCategory} (a : SimplexCategory.reedy.Latching j) :
    (boundaryCocone.{u} j).ι.app a ≫ (colimitIso.{u} j).inv =
      colimit.ι (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j) a := by
  rw [← colimitIso_ι_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original whole latching map is exactly the original boundary inclusion after the colimit
iso. -/
theorem latchingMap_eq (j : SimplexCategory) :
    ReedyStructure.latchingMap SimplexCategory.reedy stdSimplex.{u} j =
      (colimitIso.{u} j).hom ≫ (boundary j.len).ι := by
  apply colimit.hom_ext
  intro a
  rw [ReedyStructure.latchingMap_ι, ← Category.assoc, colimitIso_ι_hom, boundaryCocone_ι]

/-- The complete inverse colimit map is the same original image-factor mediator. -/
theorem colimitIso_inv_eq (j : SimplexCategory) :
    (colimitIso.{u} j).inv = desc (colimit.cocone (SimplexCategory.reedy.latchingDiagram
      stdSimplex.{u} j)) :=
  rfl

/-- The inverse retains every original boundary simplex's original epi and proper image face. -/
theorem colimitIso_inv_app {j : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (x : (boundary.{u} j.len).obj m) :
    (colimitIso.{u} j).inv.app m x =
      value (colimit.cocone (SimplexCategory.reedy.latchingDiagram stdSimplex.{u} j))
        (stdSimplex.objEquiv x.val) x.property := rfl

end SSet.StandardSimplexBoundaryColimit

end
end
end

section



/-!
# Finite degreewise tensors of the original simplicial objects

Only finite coproducts in C are required. The tensor is the original
coproduct indexed by every actual simplex of K in each degree. Its maps
retain both original diagram actions. The complete tensor--Hom equivalence
uses the actual native structured Hom and its functor Hom correspondence.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe u v

open CategoryTheory Limits Opposite

namespace HomotopicalAlgebra.FiniteResolutionTensor

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]

/-- The tensor retains the original finite coproduct at every simplex degree. -/
def tensor (F : SimplicialObject C) (K : SSet.{v}) [∀ n, Finite (K.obj n)] :
    SimplicialObject C where
  obj n := ∐ fun _ : K.obj n => F.obj n
  map f := Sigma.map' (K.map f) (fun _ => F.map f)
  map_id n := by
    apply Sigma.hom_ext
    intro k
    simp
  map_comp f g := by
    apply Sigma.hom_ext
    intro k
    simp [Category.assoc]

/-- The original inclusion labels each coefficient copy by its original K-simplex. -/
def inclusion (F : SimplicialObject C) (K : SSet.{v}) [∀ n, Finite (K.obj n)]
    (n : SimplexCategoryᵒᵖ) (k : K.obj n) : F.obj n ⟶ (tensor F K).obj n :=
  Sigma.ι (fun _ : K.obj n => F.obj n) k

/-- Every simplex operator uses both original K and F maps. -/
@[reassoc (attr := simp)]
theorem inclusion_tensor_map (F : SimplicialObject C) (K : SSet.{v}) [∀ n, Finite (K.obj n)]
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (k : K.obj n) :
    inclusion F K n k ≫ (tensor F K).map f = F.map f ≫ inclusion F K m (K.map f k) :=
  Sigma.ι_comp_map' _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- All coefficient and simplex-index morphisms act through their original complete functions. -/
def tensorMap {F F' : SimplicialObject C} (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L) :
    tensor F K ⟶ tensor F' L where
  app n := Sigma.map' (j.app n) (fun _ => i.app n)
  naturality {n m} f := by
    apply Sigma.hom_ext
    intro k
    have hj := j.naturality_apply f k
    change Sigma.ι (fun _ : K.obj n => F.obj n) k ≫
        Sigma.map' (K.map f) (fun _ => F.map f) ≫
          Sigma.map' (j.app m) (fun _ => i.app m) =
      Sigma.ι (fun _ : K.obj n => F.obj n) k ≫
        Sigma.map' (j.app n) (fun _ => i.app n) ≫
          Sigma.map' (f := fun _ : L.obj m => F'.obj m)
            (g := fun _ : L.obj n => F'.obj n) (L.map f) (fun _ => F'.map f)
    simp only [Sigma.ι_comp_map'_assoc, Sigma.ι_comp_map']
    rw [hj]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ Sigma.ι (fun _ : L.obj m => F'.obj m)
        (L.map f (j.app n k))) (i.naturality f)).trans (Category.assoc _ _ _))

/-- Every tensor morphism retains the whole original coefficient and simplex-index maps. -/
@[reassoc (attr := simp)]
theorem inclusion_tensorMap {F F' : SimplicialObject C} (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)
    (n : SimplexCategoryᵒᵖ) (k : K.obj n) :
    inclusion F K n k ≫ (tensorMap i j).app n = i.app n ≫ inclusion F' L n (j.app n k) :=
  Sigma.ι_comp_map' _ _ _

/-- Both original identity maps give the same entire tensor identity. -/
@[simp]
theorem tensorMap_id (F : SimplicialObject C) (K : SSet.{v}) [∀ n, Finite (K.obj n)] :
    tensorMap (𝟙 F) (𝟙 K) = 𝟙 (tensor F K) := by
  ext n
  apply Sigma.hom_ext
  intro k
  change inclusion F K n k ≫ (tensorMap (𝟙 F) (𝟙 K)).app n = inclusion F K n k ≫ 𝟙 _
  simp

/-- The complete tensor maps preserve both original compositions. -/
@[simp]
theorem tensorMap_comp {F F' F'' : SimplicialObject C} (i : F ⟶ F') (i' : F' ⟶ F'')
    {K L M : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] [∀ n, Finite (M.obj n)]
    (j : K ⟶ L) (j' : L ⟶ M) :
    tensorMap (i ≫ i') (j ≫ j') = tensorMap i j ≫ tensorMap i' j' := by
  ext n
  apply Sigma.hom_ext
  intro k
  change inclusion F K n k ≫ (tensorMap (i ≫ i') (j ≫ j')).app n =
    inclusion F K n k ≫ (tensorMap i j).app n ≫ (tensorMap i' j').app n
  simp [Category.assoc]

/-- A map out of the actual tensor gives the original structured Hom coordinates. -/
def toStructured {F G : SimplicialObject C} {K : SSet.{v}} [∀ n, Finite (K.obj n)]
    (f : tensor F K ⟶ G) : Functor.HomObj F G K where
  app n k := inclusion F K n k ≫ f.app n
  naturality {n m} g k := by
    have h := congrArg (fun q => inclusion F K n k ≫ q) (f.naturality g)
    simpa only [inclusion_tensor_map_assoc, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original finite coproduct descents recover the complete original tensor map. -/
def fromStructured {F G : SimplicialObject C} {K : SSet.{v}} [∀ n, Finite (K.obj n)]
    (x : Functor.HomObj F G K) : tensor F K ⟶ G where
  app n := Sigma.desc (x.app n)
  naturality {n m} g := by
    apply Sigma.hom_ext
    intro k
    change Sigma.ι (fun _ : K.obj n => F.obj n) k ≫
        Sigma.map' (K.map g) (fun _ => F.map g) ≫ Sigma.desc (x.app m) =
      Sigma.ι (fun _ : K.obj n => F.obj n) k ≫ Sigma.desc (x.app n) ≫ G.map g
    simpa only [Sigma.ι_comp_map'_assoc, Sigma.ι_comp_desc,
      Sigma.ι_comp_desc_assoc] using x.naturality g k

/-- Every original coproduct inclusion recovers its original structured map. -/
@[reassoc (attr := simp)]
theorem inclusion_fromStructured {F G : SimplicialObject C} {K : SSet.{v}}
    [∀ n, Finite (K.obj n)] (x : Functor.HomObj F G K) (n : SimplexCategoryᵒᵖ) (k : K.obj n) :
    inclusion F K n k ≫ (fromStructured x).app n = x.app n k := Sigma.ι_comp_desc _ _

/-- The whole original tensor map is recovered, including every degree and coefficient copy. -/
@[simp]
theorem from_toStructured {F G : SimplicialObject C} {K : SSet.{v}} [∀ n, Finite (K.obj n)]
    (f : tensor F K ⟶ G) : fromStructured (toStructured f) = f := by
  ext n
  apply Sigma.hom_ext
  intro k
  change inclusion F K n k ≫ (fromStructured (toStructured f)).app n =
    inclusion F K n k ≫ f.app n
  simp [toStructured]

/-- Every entire original structured Hom datum is recovered. -/
@[simp]
theorem to_fromStructured {F G : SimplicialObject C} {K : SSet.{v}} [∀ n, Finite (K.obj n)]
    (x : Functor.HomObj F G K) : toStructured (fromStructured x) = x := by
  apply Functor.HomObj.ext
  funext n k
  exact inclusion_fromStructured x n k

/-- Actual finite coproducts represent the native structured Hom, in both directions. -/
def structuredEquiv (F G : SimplicialObject C) (K : SSet.{v}) [∀ n, Finite (K.obj n)] :
    (tensor F K ⟶ G) ≃ Functor.HomObj F G K where
  toFun := toStructured
  invFun := fromStructured
  left_inv := from_toStructured
  right_inv := to_fromStructured

/-- The complete tensor--Hom equivalence targets the actual canonical simplicial Hom. -/
def homEquiv (F G : SimplicialObject C) (K : SSet.{v}) [∀ n, Finite (K.obj n)] :
    (tensor F K ⟶ G) ≃ (K ⟶ Functor.functorHom F G) :=
  (structuredEquiv F G K).trans (Functor.functorHomEquiv F G K).symm

/-- Every forward coordinate retains the original simplex operator, index map and coefficient map.
-/
theorem homEquiv_app {F G : SimplicialObject C} {K : SSet.{v}} [∀ n, Finite (K.obj n)]
    (f : tensor F K ⟶ G) (n : SimplexCategoryᵒᵖ) (k : K.obj n)
    (m : SimplexCategoryᵒᵖ) (g : n ⟶ m) :
    ((homEquiv F G K f).app n k).app m g = inclusion F K m (K.map g k) ≫ f.app m := rfl

/-- Every original structured coordinate remains the inverse's original coproduct inclusion map. -/
@[reassoc (attr := simp)]
theorem homEquiv_symm_inclusion {F G : SimplicialObject C} {K : SSet.{v}}
    [∀ n, Finite (K.obj n)] (x : K ⟶ Functor.functorHom F G)
    (n : SimplexCategoryᵒᵖ) (k : K.obj n) :
    inclusion F K n k ≫ ((homEquiv F G K).symm x).app n = (x.app n k).app n (𝟙 n) :=
  inclusion_fromStructured _ _ _

/-- The entire equivalence is natural in every original simplicial target map. -/
theorem homEquiv_natural_target {F G G' : SimplicialObject C} {K : SSet.{v}}
    [∀ n, Finite (K.obj n)] (f : tensor F K ⟶ G) (p : G ⟶ G') :
    homEquiv F G' K (f ≫ p) = homEquiv F G K f ≫
      ((SimplicialCategory.sHomFunctor (SimplicialObject C)).obj (op F)).map p := by
  ext n k m g
  change inclusion F K m (K.map g k) ≫ (f.app m ≫ p.app m) =
    (inclusion F K m (K.map g k) ≫ f.app m) ≫ p.app m
  exact (Category.assoc _ _ _).symm

/-- Both original coefficient and simplex-index source maps are preserved as whole SSet maps. -/
theorem homEquiv_natural_sources {F F' G : SimplicialObject C} (i : F ⟶ F')
    {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)]
    (j : K ⟶ L) (f : tensor F' L ⟶ G) :
    homEquiv F G K (tensorMap i j ≫ f) = j ≫ homEquiv F' G L f ≫
      ((SimplicialCategory.sHomFunctor (SimplicialObject C)).map i.op).app G := by
  ext n k m g
  change inclusion F K m (K.map g k) ≫ (tensorMap i j).app m ≫ f.app m =
    i.app m ≫ (inclusion F' L m (L.map g (j.app n k)) ≫ f.app m)
  rw [inclusion_tensorMap_assoc, j.naturality_apply g k]

end HomotopicalAlgebra.FiniteResolutionTensor

end
end
end

section



/-! # Original finite-pair tensor pushout products -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe u v

open CategoryTheory Limits Opposite

namespace HomotopicalAlgebra.FiniteResolutionTensor

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
  {F F' : SimplicialObject C} (i : F ⟶ F')
  {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)

/-- Both original tensor-map paths through the finite-pair square coincide. -/
theorem tensorMap_square :
    tensorMap i (𝟙 K) ≫ tensorMap (𝟙 F') j =
      tensorMap (𝟙 F) j ≫ tensorMap i (𝟙 L) := by
  rw [← tensorMap_comp, ← tensorMap_comp]
  simp only [Category.comp_id, Category.id_comp]

variable [HasPushouts C]

/-- The actual native finite-pair pushout product retains both original tensor-map legs. -/
def pushoutProduct :
    pushout (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j) ⟶ tensor F' L :=
  pushout.desc (tensorMap (𝟙 F') j) (tensorMap i (𝟙 L)) (tensorMap_square i j)

/-- The original first pushout inclusion recovers the original scalar tensor-map leg. -/
@[reassoc (attr := simp)]
theorem pushoutProduct_inl :
    pushout.inl (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j) ≫ pushoutProduct i j =
      tensorMap (𝟙 F') j := pushout.inl_desc _ _ _

/-- The original second pushout inclusion recovers the original coefficient tensor-map leg. -/
@[reassoc (attr := simp)]
theorem pushoutProduct_inr :
    pushout.inr (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j) ≫ pushoutProduct i j =
      tensorMap i (𝟙 L) := pushout.inr_desc _ _ _

end HomotopicalAlgebra.FiniteResolutionTensor

end
end
end

section



/-! # Finite-pair tensor and canonical mapping corner transposition -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u v
open CategoryTheory Limits Opposite

namespace HomotopicalAlgebra.FiniteResolutionTensor

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]

/-- Actual coefficient source maps transpose through the entire finite tensor/Hom equivalence. -/
theorem homEquiv_source {F F' G : SimplicialObject C} (i : F ⟶ F')
    {K : SSet.{v}} [∀ n, Finite (K.obj n)] (f : tensor F' K ⟶ G) :
    homEquiv F G K (tensorMap i (𝟙 K) ≫ f) = homEquiv F' G K f ≫
      ((SimplicialCategory.sHomFunctor (SimplicialObject C)).map i.op).app G := by
  simpa using homEquiv_natural_sources i (𝟙 K) f

/-- Actual finite scalar maps transpose through the same whole Hom equivalence. -/
theorem homEquiv_scalar {F G : SimplicialObject C} {K L : SSet.{v}}
    [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L) (f : tensor F L ⟶ G) :
    homEquiv F G K (tensorMap (𝟙 F) j ≫ f) = j ≫ homEquiv F G L f := by
  ext n k m g
  change inclusion F K m (K.map g k) ≫ (tensorMap (𝟙 F) j).app m ≫ f.app m =
    inclusion F L m (L.map g (j.app n k)) ≫ f.app m
  rw [inclusion_tensorMap_assoc, j.naturality_apply g k]
  simp only [NatTrans.id_app, Category.id_comp]

/-- The inverse tensor--Hom function retains every original target map. -/
theorem homEquiv_symm_target {F G G' : SimplicialObject C} {K : SSet.{v}}
    [∀ n, Finite (K.obj n)] (x : K ⟶ Functor.functorHom F G) (p : G ⟶ G') :
    (homEquiv F G' K).symm
        (x ≫ ((SimplicialCategory.sHomFunctor (SimplicialObject C)).obj (op F)).map p) =
      (homEquiv F G K).symm x ≫ p := by
  apply (homEquiv F G' K).injective
  rw [Equiv.apply_symm_apply, homEquiv_natural_target, Equiv.apply_symm_apply]

/-- The inverse tensor--Hom function retains the entire original coefficient map. -/
theorem homEquiv_symm_source {F F' G : SimplicialObject C} (i : F ⟶ F')
    {K : SSet.{v}} [∀ n, Finite (K.obj n)] (x : K ⟶ Functor.functorHom F' G) :
    (homEquiv F G K).symm
        (x ≫ ((SimplicialCategory.sHomFunctor (SimplicialObject C)).map i.op).app G) =
      tensorMap i (𝟙 K) ≫ (homEquiv F' G K).symm x := by
  apply (homEquiv F G K).injective
  rw [Equiv.apply_symm_apply, homEquiv_source, Equiv.apply_symm_apply]

/-- The inverse tensor--Hom function retains the entire original finite scalar map. -/
theorem homEquiv_symm_scalar {F G : SimplicialObject C} {K L : SSet.{v}}
    [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] (j : K ⟶ L)
    (x : L ⟶ Functor.functorHom F G) :
    (homEquiv F G K).symm (j ≫ x) = tensorMap (𝟙 F) j ≫ (homEquiv F G L).symm x := by
  apply (homEquiv F G K).injective
  rw [Equiv.apply_symm_apply, homEquiv_scalar, Equiv.apply_symm_apply]

variable [HasPushouts C]
  {F F' G G' : SimplicialObject C} {i : F ⟶ F'} {p : G ⟶ G'}
  {K L : SSet.{v}} [∀ n, Finite (K.obj n)] [∀ n, Finite (L.obj n)] {j : K ⟶ L}
  (sq : (SimplicialCategory.sHomFunctor (SimplicialObject C)).PullbackObjObj i p)

/-- The full original tensor square transposes to the original canonical mapping corner square. -/
def arrowTo (α : Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p) :
    Arrow.mk j ⟶ Arrow.mk sq.π :=
  Arrow.homMk
    (homEquiv F' G K (pushout.inl _ _ ≫ α.left))
    (sq.isPullback.lift
      (homEquiv F G L (pushout.inr _ _ ≫ α.left)) (homEquiv F' G' L α.right) (by
        have h : (pushout.inr (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j) ≫ α.left) ≫ p =
            tensorMap i (𝟙 L) ≫ α.right := by
          have hc := congrArg (fun q =>
            pushout.inr (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j) ≫ q) α.w
          change _ ≫ (α.left ≫ p) = _ ≫ (pushoutProduct i j ≫ α.right) at hc
          rw [pushoutProduct_inr_assoc] at hc
          exact (Category.assoc _ _ _).trans hc
        have he := congrArg (homEquiv F G' L) h
        rw [homEquiv_source, homEquiv_natural_target] at he
        exact he)) (by
      change homEquiv F' G K (pushout.inl (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j) ≫ α.left) ≫
        sq.π = j ≫ _
      apply sq.isPullback.hom_ext
      · simp only [Category.assoc, IsPullback.lift_fst, sq.π_fst]
        rw [← homEquiv_scalar, ← homEquiv_source]
        congr 1
        rw [← Category.assoc, ← Category.assoc, pushout.condition]
      · simp only [Category.assoc, IsPullback.lift_snd, sq.π_snd]
        rw [← homEquiv_scalar, ← homEquiv_natural_target]
        congr 1
        have h : α.left ≫ p = pushoutProduct i j ≫ α.right := α.w
        rw [Category.assoc, h, pushoutProduct_inl_assoc])

/-- Both original mapping-corner projections determine the entire inverse tensor square. -/
def arrowFrom (β : Arrow.mk j ⟶ Arrow.mk sq.π) :
    Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p :=
  Arrow.homMk
    (pushout.desc ((homEquiv F' G K).symm β.left)
      ((homEquiv F G L).symm (β.right ≫ sq.fst)) (by
        apply (homEquiv F G K).injective
        rw [homEquiv_source, homEquiv_scalar, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        have h := congrArg (fun q => q ≫ sq.fst) β.w
        simpa only [Arrow.mk_hom, Category.assoc, sq.π_fst] using h))
    ((homEquiv F' G' L).symm (β.right ≫ sq.snd)) (by
      change _ ≫ p = pushoutProduct i j ≫ _
      apply pushout.hom_ext
      · simp only [pushoutProduct_inl_assoc, pushout.inl_desc_assoc]
        rw [← homEquiv_symm_scalar, ← homEquiv_symm_target]
        congr 1
        have h := congrArg (fun q => q ≫ sq.snd) β.w
        simpa only [Arrow.mk_hom, Category.assoc, sq.π_snd] using h
      · simp only [pushoutProduct_inr_assoc, pushout.inr_desc_assoc]
        rw [← homEquiv_symm_source, ← homEquiv_symm_target]
        congr 1
        have h := congrArg (fun q => β.right ≫ q) sq.isPullback.w
        simpa only [Category.assoc] using h)

/-- The first entire map in the transposed square is the original first tensor leg curried. -/
@[simp]
theorem arrowTo_left (α : Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p) :
    (arrowTo sq α).left = homEquiv F' G K (pushout.inl _ _ ≫ α.left) := rfl

/-- The first original pullback projection reads back the complete second tensor leg. -/
@[reassoc (attr := simp)]
theorem arrowTo_right_fst (α : Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p) :
    (arrowTo sq α).right ≫ sq.fst = homEquiv F G L (pushout.inr _ _ ≫ α.left) :=
  sq.isPullback.lift_fst _ _ _

/-- The second original pullback projection reads back the complete tensor target map. -/
@[reassoc (attr := simp)]
theorem arrowTo_right_snd (α : Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p) :
    (arrowTo sq α).right ≫ sq.snd = homEquiv F' G' L α.right :=
  sq.isPullback.lift_snd _ _ _

/-- The original first pushout leg reads back the entire inverse's first map. -/
@[reassoc (attr := simp)]
theorem arrowFrom_inl (β : Arrow.mk j ⟶ Arrow.mk sq.π) :
    pushout.inl (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j) ≫ (arrowFrom sq β).left =
      (homEquiv F' G K).symm β.left := pushout.inl_desc _ _ _

/-- The original second pushout leg reads back the entire inverse's first projection. -/
@[reassoc (attr := simp)]
theorem arrowFrom_inr (β : Arrow.mk j ⟶ Arrow.mk sq.π) :
    pushout.inr (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j) ≫ (arrowFrom sq β).left =
      (homEquiv F G L).symm (β.right ≫ sq.fst) := pushout.inr_desc _ _ _

/-- The inverse's target map is the original second pullback projection uncurried. -/
@[simp]
theorem arrowFrom_right (β : Arrow.mk j ⟶ Arrow.mk sq.π) :
    (arrowFrom sq β).right = (homEquiv F' G' L).symm (β.right ≫ sq.snd) := rfl

/-- Both original pushout legs recover the entire initial commutative square. -/
@[simp]
theorem arrowFrom_to (α : Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p) :
    arrowFrom sq (arrowTo sq α) = α := by
  apply Arrow.hom_ext
  · apply pushout.hom_ext
    · rw [arrowFrom_inl, arrowTo_left, Equiv.symm_apply_apply]
    · rw [arrowFrom_inr, arrowTo_right_fst, Equiv.symm_apply_apply]
  · rw [arrowFrom_right, arrowTo_right_snd, Equiv.symm_apply_apply]

/-- Both original pullback projections recover the entire initial mapping-corner square. -/
@[simp]
theorem arrowTo_from (β : Arrow.mk j ⟶ Arrow.mk sq.π) :
    arrowTo sq (arrowFrom sq β) = β := by
  apply Arrow.hom_ext
  · rw [arrowTo_left, arrowFrom_inl, Equiv.apply_symm_apply]
  · apply sq.isPullback.hom_ext
    · rw [arrowTo_right_fst, arrowFrom_inr, Equiv.apply_symm_apply]
    · rw [arrowTo_right_snd, arrowFrom_right, Equiv.apply_symm_apply]

/-- Whole commutative squares for the actual finite-pair product and supplied corner correspond. -/
def arrowEquiv :
    (Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p) ≃ (Arrow.mk j ⟶ Arrow.mk sq.π) where
  toFun := arrowTo sq
  invFun := arrowFrom sq
  left_inv := arrowFrom_to sq
  right_inv := arrowTo_from sq

/-- Currying an actual diagonal preserves both original triangles and the supplied pullback. -/
def liftTo (α : Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p) (δ : Arrow.LiftStruct α) :
    Arrow.LiftStruct (arrowTo sq α) where
  l := homEquiv F' G L δ.l
  fac_left := by
    change j ≫ homEquiv F' G L δ.l = (arrowTo sq α).left
    rw [← homEquiv_scalar, arrowTo_left]
    apply (homEquiv F' G K).congr_arg
    have h := congrArg (fun q =>
      pushout.inl (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j) ≫ q) δ.fac_left
    change _ ≫ (pushoutProduct i j ≫ δ.l) = _ ≫ α.left at h
    simpa only [pushoutProduct_inl_assoc] using h
  fac_right := by
    change homEquiv F' G L δ.l ≫ sq.π = (arrowTo sq α).right
    apply sq.isPullback.hom_ext
    · rw [Category.assoc, sq.π_fst, ← homEquiv_source, arrowTo_right_fst]
      apply (homEquiv F G L).congr_arg
      have h := congrArg (fun q =>
        pushout.inr (tensorMap i (𝟙 K)) (tensorMap (𝟙 F) j) ≫ q) δ.fac_left
      change _ ≫ (pushoutProduct i j ≫ δ.l) = _ ≫ α.left at h
      simpa only [pushoutProduct_inr_assoc] using h
    · rw [Category.assoc, sq.π_snd, ← homEquiv_natural_target, arrowTo_right_snd]
      apply (homEquiv F' G' L).congr_arg
      exact δ.fac_right

/-- Uncurrying a corner diagonal preserves both original triangles of the original tensor square. -/
def liftFrom (α : Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p)
    (δ : Arrow.LiftStruct (arrowTo sq α)) : Arrow.LiftStruct α where
  l := (homEquiv F' G L).symm δ.l
  fac_left := by
    change pushoutProduct i j ≫ (homEquiv F' G L).symm δ.l = α.left
    apply pushout.hom_ext
    · rw [pushoutProduct_inl_assoc, ← homEquiv_symm_scalar]
      have h : j ≫ δ.l = (arrowTo sq α).left := δ.fac_left
      rw [h, arrowTo_left, Equiv.symm_apply_apply]
    · rw [pushoutProduct_inr_assoc, ← homEquiv_symm_source]
      have h := congrArg (fun q => q ≫ sq.fst) δ.fac_right
      change (δ.l ≫ sq.π) ≫ sq.fst = (arrowTo sq α).right ≫ sq.fst at h
      simp only [Category.assoc, sq.π_fst] at h
      rw [h, arrowTo_right_fst, Equiv.symm_apply_apply]
  fac_right := by
    change (homEquiv F' G L).symm δ.l ≫ p = α.right
    rw [← homEquiv_symm_target]
    have h := congrArg (fun q => q ≫ sq.snd) δ.fac_right
    change (δ.l ≫ sq.π) ≫ sq.snd = (arrowTo sq α).right ≫ sq.snd at h
    simp only [Category.assoc, sq.π_snd] at h
    rw [h, arrowTo_right_snd, Equiv.symm_apply_apply]

/-- Every whole original diagonal, including its two triangle proofs, is recovered. -/
@[simp]
theorem liftFrom_to (α : Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p)
    (δ : Arrow.LiftStruct α) : liftFrom sq α (liftTo sq α δ) = δ := by
  apply CommSq.LiftStruct.ext
  exact (homEquiv F' G L).symm_apply_apply δ.l

/-- Every whole original corner diagonal, including its two triangle proofs, is recovered. -/
@[simp]
theorem liftTo_from (α : Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p)
    (δ : Arrow.LiftStruct (arrowTo sq α)) : liftTo sq α (liftFrom sq α δ) = δ := by
  apply CommSq.LiftStruct.ext
  exact (homEquiv F' G L).apply_symm_apply δ.l

/-- Diagonal structures correspond for every original square, with no lifting outcome assumed. -/
def liftEquiv (α : Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p) :
    Arrow.LiftStruct α ≃ Arrow.LiftStruct (arrowTo sq α) where
  toFun := liftTo sq α
  invFun := liftFrom sq α
  left_inv := liftFrom_to sq α
  right_inv := liftTo_from sq α

/-- The whole forward diagonal is the actual original tensor--Hom function. -/
@[simp]
theorem liftTo_l (α : Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p)
    (δ : Arrow.LiftStruct α) : (liftTo sq α δ).l = homEquiv F' G L δ.l := rfl

/-- The whole inverse diagonal is the actual original inverse tensor--Hom function. -/
@[simp]
theorem liftFrom_l (α : Arrow.mk (pushoutProduct i j) ⟶ Arrow.mk p)
    (δ : Arrow.LiftStruct (arrowTo sq α)) :
    (liftFrom sq α δ).l = (homEquiv F' G L).symm δ.l := rfl

/-- Any original corner-square diagonal uncurries into the entire inverse tensor square. -/
def liftFromArrow (β : Arrow.mk j ⟶ Arrow.mk sq.π) (δ : Arrow.LiftStruct β) :
    Arrow.LiftStruct (arrowFrom sq β) where
  l := (homEquiv F' G L).symm δ.l
  fac_left := by
    change pushoutProduct i j ≫ (homEquiv F' G L).symm δ.l = (arrowFrom sq β).left
    apply pushout.hom_ext
    · rw [pushoutProduct_inl_assoc, arrowFrom_inl, ← homEquiv_symm_scalar]
      apply (homEquiv F' G K).symm.congr_arg
      exact δ.fac_left
    · rw [pushoutProduct_inr_assoc, arrowFrom_inr, ← homEquiv_symm_source]
      apply (homEquiv F G L).symm.congr_arg
      have h := congrArg (fun q => q ≫ sq.fst) δ.fac_right
      change (δ.l ≫ sq.π) ≫ sq.fst = β.right ≫ sq.fst at h
      simpa only [Category.assoc, sq.π_fst] using h
  fac_right := by
    change (homEquiv F' G L).symm δ.l ≫ p = (arrowFrom sq β).right
    rw [arrowFrom_right, ← homEquiv_symm_target]
    apply (homEquiv F' G' L).symm.congr_arg
    have h := congrArg (fun q => q ≫ sq.snd) δ.fac_right
    change (δ.l ≫ sq.π) ≫ sq.snd = β.right ≫ sq.snd at h
    simpa only [Category.assoc, sq.π_snd] using h

/-- Every original corner square uses the same whole inverse currying function on diagonals. -/
@[simp]
theorem liftFromArrow_l (β : Arrow.mk j ⟶ Arrow.mk sq.π) (δ : Arrow.LiftStruct β) :
    (liftFromArrow sq β δ).l = (homEquiv F' G L).symm δ.l := rfl

/-- The actual finite-pair tensor arrow and the supplied canonical-Hom corner have the same LLP. -/
theorem hasLiftingProperty_iff :
    HasLiftingProperty (pushoutProduct i j) p ↔ HasLiftingProperty j sq.π := by
  rw [Arrow.hasLiftingProperty_iff, Arrow.hasLiftingProperty_iff]
  constructor
  · intro h β
    obtain ⟨δ⟩ := h (arrowFrom sq β)
    have δ' := liftTo sq (arrowFrom sq β) δ
    rw [arrowTo_from sq β] at δ'
    exact ⟨δ'⟩
  · intro h α
    obtain ⟨δ⟩ := h (arrowTo sq α)
    exact ⟨liftFrom sq α δ⟩

end HomotopicalAlgebra.FiniteResolutionTensor

end
end
end

section



/-!
# Finite copower pushouts against actual injective index maps

Only finite coproducts and pushouts are used. Every original coefficient copy
and original index value is retained. The scalar lifting construction gives
cofibration and trivial cofibration membership from the original coefficient
map and an actual injective finite index function.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits

namespace HomotopicalAlgebra.FiniteCopowerPushout

variable {C : Type u} [Category.{v} C]
  {S T : Type v} [Finite S] [Finite T]

section Geometry

variable [HasFiniteCoproducts C]
  {X Y : C} (i : X ⟶ Y) (j : S → T)

/-- The original coefficient map on every finite coefficient copy. -/
abbrev coefficientMap (U : Type v) [Finite U] :
    (∐ fun _ : U => X) ⟶ ∐ fun _ : U => Y :=
  Sigma.map' (fun u : U => u) (fun _ => i)

/-- The actual finite index map preserves each original coefficient. -/
abbrev indexMap (Z : C) : (∐ fun _ : S => Z) ⟶ ∐ fun _ : T => Z :=
  Sigma.map' j (fun _ => 𝟙 Z)

/-- Every coefficient copy reads back the original coefficient map. -/
@[reassoc]
theorem coefficientMap_ι (U : Type v) [Finite U] (s : U) :
    Sigma.ι (fun _ : U => X) s ≫ coefficientMap i U = i ≫ Sigma.ι (fun _ : U => Y) s :=
  Sigma.ι_comp_map' _ _ _

/-- Every original index copy reads back its original finite index value. -/
@[reassoc]
theorem indexMap_ι (Z : C) (s : S) :
    Sigma.ι (fun _ : S => Z) s ≫ indexMap j Z = Sigma.ι (fun _ : T => Z) (j s) := by
  rw [Sigma.ι_comp_map', Category.id_comp]

/-- The original finite coefficient/index square commutes. -/
theorem square : coefficientMap i S ≫ indexMap j Y = indexMap j X ≫ coefficientMap i T := by
  apply Sigma.hom_ext
  intro s
  rw [coefficientMap_ι_assoc, indexMap_ι, indexMap_ι_assoc, coefficientMap_ι]

variable [HasPushouts C]

/-- The actual finite copower pushout map with both original coefficient/index legs. -/
def map : pushout (coefficientMap i S) (indexMap j X) ⟶ ∐ fun _ : T => Y :=
  pushout.desc (indexMap j Y) (coefficientMap i T) (square i j)

/-- The first original pushout leg is the original finite index map on the target coefficient. -/
@[reassoc (attr := simp)]
theorem inl_map : pushout.inl (coefficientMap i S) (indexMap j X) ≫ map i j = indexMap j Y :=
  pushout.inl_desc _ _ _

/-- The second original pushout leg is the whole original coefficient map. -/
@[reassoc (attr := simp)]
theorem inr_map : pushout.inr (coefficientMap i S) (indexMap j X) ≫ map i j = coefficientMap i T :=
  pushout.inr_desc _ _ _

/-- An injective original index function preserves the source coefficient lifting property. -/
theorem hasLiftingProperty {A B : C} (p : A ⟶ B) [HasLiftingProperty i p]
    (hj : Function.Injective j) : HasLiftingProperty (map i j) p where
  sq_hasLift {f g} sq := by
    classical
    let inl := pushout.inl (coefficientMap i S) (indexMap j X)
    let inr := pushout.inr (coefficientMap i S) (indexMap j X)
    have st (t : T) : CommSq (Sigma.ι (fun _ : T => X) t ≫ inr ≫ f) i p
        (Sigma.ι (fun _ : T => Y) t ≫ g) := by
      constructor
      dsimp only [inr]
      simp only [Category.assoc]
      rw [sq.w, inr_map_assoc, coefficientMap_ι_assoc]
    let a : T → (Y ⟶ A) := fun t =>
      if h : ∃ s : S, j s = t then Sigma.ι (fun _ : S => Y) h.choose ≫ inl ≫ f
      else (st t).lift
    have ha (s : S) : a (j s) = Sigma.ι (fun _ : S => Y) s ≫ inl ≫ f := by
      dsimp only [a]
      split
      · next h =>
          have he : h.choose = s := hj h.choose_spec
          rw [he]
      · next h => exact (h ⟨s, rfl⟩).elim
    have hal (t : T) : i ≫ a t = Sigma.ι (fun _ : T => X) t ≫ inr ≫ f := by
      dsimp only [a]
      split
      · next h =>
          have hs : j h.choose = t := h.choose_spec
          calc
            i ≫ Sigma.ι (fun _ : S => Y) h.choose ≫ inl ≫ f =
                Sigma.ι (fun _ : T => X) (j h.choose) ≫ inr ≫ f := by
              dsimp only [inl, inr]
              rw [← coefficientMap_ι_assoc, pushout.condition_assoc, indexMap_ι_assoc]
            _ = Sigma.ι (fun _ : T => X) t ≫ inr ≫ f :=
              congrArg (fun t : T => Sigma.ι (fun _ : T => X) t ≫ inr ≫ f) hs
      · exact (st t).fac_left
    have har (t : T) : a t ≫ p = Sigma.ι (fun _ : T => Y) t ≫ g := by
      dsimp only [a]
      split
      · next h =>
          have hs : j h.choose = t := h.choose_spec
          simp only [Category.assoc]
          rw [sq.w]
          dsimp only [inl]
          rw [inl_map_assoc, indexMap_ι_assoc, hs]
      · exact (st t).fac_right
    refine CommSq.HasLift.mk' { l := Sigma.desc a, fac_left := ?_, fac_right := ?_ }
    · apply pushout.hom_ext
      · apply Sigma.hom_ext
        intro s
        rw [inl_map_assoc, indexMap_ι_assoc, Sigma.ι_comp_desc]
        exact ha s
      · apply Sigma.hom_ext
        intro t
        rw [inr_map_assoc, coefficientMap_ι_assoc, Sigma.ι_comp_desc]
        exact hal t
    · apply Sigma.hom_ext
      intro t
      rw [Sigma.ι_comp_desc_assoc]
      exact har t

end Geometry

section Model

variable [ModelCategory C] {X Y : C} (i : X ⟶ Y) (j : S → T)

/-- The original finite copower PP is a scalar cofibration when its original coefficient is. -/
theorem cofibration (hi : cofibrations C i) (hj : Function.Injective j) : cofibrations C (map i
  j) := by
  rw [← trivialFibrations_llp]
  intro A B p hp
  let _ := MorphismProperty.hasLiftingProperty_of_wfs i p hi hp
  exact hasLiftingProperty i j p hj

/-- The original finite copower PP is a scalar trivial cofibration when its original coefficient is.
-/
theorem trivialCofibration (hi : trivialCofibrations C i) (hj : Function.Injective j) :
    trivialCofibrations C (map i j) := by
  rw [← fibrations_llp]
  intro A B p hp
  let _ := MorphismProperty.hasLiftingProperty_of_wfs i p hi hp
  exact hasLiftingProperty i j p hj

end Model

end HomotopicalAlgebra.FiniteCopowerPushout

end
end
end
