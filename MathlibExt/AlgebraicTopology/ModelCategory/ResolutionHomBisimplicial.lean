/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FiniteResolutionTensor
public import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialRows

/-!
# The genuine bisimplicial Hom of two resolution diagrams

The outer simplex variable is the cosimplicial source degree, and the inner
variable is the simplicial target degree.  Every bisimplex is an original
coefficient map, and the two directions use its original precomposition and
postcomposition.  The canonical diagonal is identified with the existing
resolution Hom complex by identity functions on all its simplices.

The augmentation and coaugmentation comparisons retain the whole original
diagram maps.  This file uses only the coefficient category; their weak
equivalence laws are proved from actual frames separately.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace HomotopicalAlgebra.ResolutionHomBisimplicial

variable {C : Type u} [Category.{v} C]

/-- The actual Hom sets out of every source degree and into every target degree. -/
def obj (A : CosimplicialObject C) (B : SimplicialObject C) : SimplicialObject SSet.{v} where
  obj n := ResolutionHomComplex.right (A.obj n.unop) B
  map f := ResolutionHomComplex.precomp ((CosimplicialObject.const C).map (A.map f.unop)) B
  map_id n := by
    change ResolutionHomComplex.precomp
      ((CosimplicialObject.const C).map (A.map (𝟙 n.unop))) B = _
    rw [A.map_id, (CosimplicialObject.const C).map_id]
    exact ResolutionHomComplex.precomp_id _ _
  map_comp f g := by
    simp only [unop_comp, A.map_comp, CategoryTheory.Functor.map_comp,
      ResolutionHomComplex.precomp_comp]

/-- Every original bisimplex retains the original coefficient Hom type. -/
@[simp]
theorem obj_obj (A : CosimplicialObject C) (B : SimplicialObject C)
    (n m : SimplexCategoryᵒᵖ) :
    ((obj A B).obj n).obj m = (A.obj n.unop ⟶ B.obj m) := rfl

/-- The whole outer row is the original right resolution Hom. -/
theorem outerRow (A : CosimplicialObject C) (B : SimplicialObject C)
    (n : SimplexCategoryᵒᵖ) :
    (obj A B).obj n = ResolutionHomComplex.right (A.obj n.unop) B := rfl

/-- Each outer simplicial operator uses exactly the original source map. -/
theorem outer_map_app_apply (A : CosimplicialObject C) (B : SimplicialObject C)
    {n n' : SimplexCategoryᵒᵖ} (f : n ⟶ n') (m : SimplexCategoryᵒᵖ)
    (h : A.obj n.unop ⟶ B.obj m) :
    ((obj A B).map f).app m h = A.map f.unop ≫ h := rfl

/-- Each inner simplicial operator uses exactly the original target map. -/
theorem inner_map_apply (A : CosimplicialObject C) (B : SimplicialObject C)
    (n : SimplexCategoryᵒᵖ) {m m' : SimplexCategoryᵒᵖ} (g : m ⟶ m')
    (h : A.obj n.unop ⟶ B.obj m) :
    ((obj A B).obj n).map g h = h ≫ B.map g :=
  ResolutionHomComplex.right_map_apply _ _ _ _

/-- All original outer faces are the original cosimplicial cofaces. -/
theorem outer_face_apply (A : CosimplicialObject C) (B : SimplicialObject C)
    {n : ℕ} (i : Fin (n + 2)) (m : SimplexCategoryᵒᵖ)
    (h : A.obj ⦋n + 1⦌ ⟶ B.obj m) :
    ((obj A B).δ i).app m h = A.δ i ≫ h := rfl

/-- All original outer degeneracies are the original cosimplicial codegeneracies. -/
theorem outer_degeneracy_apply (A : CosimplicialObject C) (B : SimplicialObject C)
    {n : ℕ} (i : Fin (n + 1)) (m : SimplexCategoryᵒᵖ)
    (h : A.obj ⦋n⦌ ⟶ B.obj m) :
    ((obj A B).σ i).app m h = A.σ i ≫ h := rfl

/-- All original inner faces are the original simplicial target faces. -/
theorem inner_face_apply (A : CosimplicialObject C) (B : SimplicialObject C)
    (n : SimplexCategoryᵒᵖ) {m : ℕ} (i : Fin (m + 2))
    (h : A.obj n.unop ⟶ B.obj (op ⦋m + 1⦌)) :
    ((obj A B).obj n).δ i h = h ≫ B.δ i :=
  inner_map_apply _ _ _ _ _

/-- All original inner degeneracies are the original simplicial target degeneracies. -/
theorem inner_degeneracy_apply (A : CosimplicialObject C) (B : SimplicialObject C)
    (n : SimplexCategoryᵒᵖ) {m : ℕ} (i : Fin (m + 1))
    (h : A.obj n.unop ⟶ B.obj (op ⦋m⦌)) :
    ((obj A B).obj n).σ i h = h ≫ B.σ i :=
  inner_map_apply _ _ _ _ _

/-- The two independent original simplex actions commute on every coefficient map. -/
theorem outer_inner_commute (A : CosimplicialObject C) (B : SimplicialObject C)
    {n n' m m' : SimplexCategoryᵒᵖ} (f : n ⟶ n') (g : m ⟶ m')
    (h : A.obj n.unop ⟶ B.obj m) :
    ((obj A B).map f).app m' (((obj A B).obj n).map g h) =
      ((obj A B).obj n').map g (((obj A B).map f).app m h) := by
  exact congrArg
    (fun t : ((obj A B).obj n).obj m ⟶ ((obj A B).obj n').obj m' => t h)
    (((obj A B).map f).naturality g)

/-- A whole original cosimplicial map induces precomposition in both-variable Hom. -/
def precomp {A A' : CosimplicialObject C} (a : A ⟶ A') (B : SimplicialObject C) :
    obj A' B ⟶ obj A B where
  app n := ResolutionHomComplex.precomp ((CosimplicialObject.const C).map (a.app n.unop)) B
  naturality {n m} f := by
    ext k h
    change A'.obj n.unop ⟶ B.obj k at h
    change a.app m.unop ≫ (A'.map f.unop ≫ h) =
      A.map f.unop ≫ (a.app n.unop ≫ h)
    calc
      a.app m.unop ≫ (A'.map f.unop ≫ h) = (a.app m.unop ≫ A'.map f.unop) ≫ h :=
        (Category.assoc _ _ _).symm
      _ = (A.map f.unop ≫ a.app n.unop) ≫ h :=
        congrArg (fun t : A.obj m.unop ⟶ A'.obj n.unop => t ≫ h) (a.naturality f.unop).symm
      _ = A.map f.unop ≫ (a.app n.unop ≫ h) := Category.assoc _ _ _

/-- A whole original simplicial map induces postcomposition in both-variable Hom. -/
def postcomp (A : CosimplicialObject C) {B B' : SimplicialObject C} (b : B ⟶ B') :
    obj A B ⟶ obj A B' where
  app n := ResolutionHomComplex.postcomp ((CosimplicialObject.const C).obj (A.obj n.unop)) b
  naturality {n m} f := by
    ext k h
    change A.obj n.unop ⟶ B.obj k at h
    change (A.map f.unop ≫ h) ≫ b.app k = A.map f.unop ≫ (h ≫ b.app k)
    exact Category.assoc _ _ _

/-- Every source transformation acts by its unchanged original coefficient component. -/
theorem precomp_app_apply {A A' : CosimplicialObject C} (a : A ⟶ A')
    (B : SimplicialObject C) (n m : SimplexCategoryᵒᵖ)
    (h : A'.obj n.unop ⟶ B.obj m) :
    ((precomp a B).app n).app m h = a.app n.unop ≫ h := rfl

/-- Every target transformation acts by its unchanged original coefficient component. -/
theorem postcomp_app_apply (A : CosimplicialObject C) {B B' : SimplicialObject C}
    (b : B ⟶ B') (n m : SimplexCategoryᵒᵖ) (h : A.obj n.unop ⟶ B.obj m) :
    ((postcomp A b).app n).app m h = h ≫ b.app m := rfl

/-- The whole bisimplicial source action preserves identities. -/
@[simp]
theorem precomp_id (A : CosimplicialObject C) (B : SimplicialObject C) :
    precomp (𝟙 A) B = 𝟙 (obj A B) := by
  ext n m h
  change A.obj n.unop ⟶ B.obj m at h
  change 𝟙 (A.obj n.unop) ≫ h = h
  exact Category.id_comp h

/-- The whole bisimplicial source action reverses composition. -/
@[simp]
theorem precomp_comp {A A' A'' : CosimplicialObject C}
    (a : A ⟶ A') (a' : A' ⟶ A'') (B : SimplicialObject C) :
    precomp (a ≫ a') B = precomp a' B ≫ precomp a B := by
  ext n m h
  change A''.obj n.unop ⟶ B.obj m at h
  change (a.app n.unop ≫ a'.app n.unop) ≫ h = a.app n.unop ≫ (a'.app n.unop ≫ h)
  exact Category.assoc _ _ _

/-- The whole bisimplicial target action preserves identities. -/
@[simp]
theorem postcomp_id (A : CosimplicialObject C) (B : SimplicialObject C) :
    postcomp A (𝟙 B) = 𝟙 (obj A B) := by
  ext n m h
  change A.obj n.unop ⟶ B.obj m at h
  change h ≫ 𝟙 (B.obj m) = h
  exact Category.comp_id h

/-- The whole bisimplicial target action preserves composition. -/
@[simp]
theorem postcomp_comp (A : CosimplicialObject C) {B B' B'' : SimplicialObject C}
    (b : B ⟶ B') (b' : B' ⟶ B'') :
    postcomp A (b ≫ b') = postcomp A b ≫ postcomp A b' := by
  ext n m h
  change A.obj n.unop ⟶ B.obj m at h
  change h ≫ (b.app m ≫ b'.app m) = (h ≫ b.app m) ≫ b'.app m
  exact (Category.assoc _ _ _).symm

/-- All original source and target transformations commute on the entire bisimplicial object. -/
theorem precomp_postcomp {A A' : CosimplicialObject C} (a : A ⟶ A')
    {B B' : SimplicialObject C} (b : B ⟶ B') :
    precomp a B ≫ postcomp A b = postcomp A' b ≫ precomp a B' := by
  ext n m h
  change A'.obj n.unop ⟶ B.obj m at h
  change (a.app n.unop ≫ h) ≫ b.app m = a.app n.unop ≫ (h ≫ b.app m)
  exact Category.assoc _ _ _

/-- Fixing an inner degree gives the original left resolution Hom by identity on Hom sets. -/
def innerRowIso (A : CosimplicialObject C) (B : SimplicialObject C)
    (m : SimplexCategoryᵒᵖ) :
    SSet.simplicialRow (obj A B) m ≅ ResolutionHomComplex.left A (B.obj m) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n n' f
    ext h
    change A.obj n.unop ⟶ B.obj m at h
    change A.map f.unop ≫ h = A.map f.unop ≫ h ≫ 𝟙 (B.obj m)
    exact congrArg (fun t : A.obj n.unop ⟶ B.obj m => A.map f.unop ≫ t)
      (Category.comp_id h).symm)

/-- The inner-row identification retains every whole original target transformation. -/
theorem innerRowIso_postcomp (A : CosimplicialObject C) {B B' : SimplicialObject C}
    (b : B ⟶ B') (m : SimplexCategoryᵒᵖ) :
    (SSet.simplicialTransposeFunctor.map (postcomp A b)).app m ≫ (innerRowIso A B' m).hom =
      (innerRowIso A B m).hom ≫
        ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map (b.app m)) := by
  ext n h
  rfl

/-- The actual canonical diagonal has exactly the existing resolution Hom simplices. -/
def diagonalIso (A : CosimplicialObject C) (B : SimplicialObject C) :
    SSet.simplicialDiagonalFunctor.obj (obj A B) ≅ ResolutionHomComplex.obj A B :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m f
    ext h
    change A.obj n.unop ⟶ B.obj n at h
    change A.map f.unop ≫ (𝟙 (A.obj n.unop) ≫ h ≫ B.map f) =
      A.map f.unop ≫ h ≫ B.map f
    simp only [Category.id_comp])

/-- The diagonal identification is the identity function in every original degree. -/
@[simp]
theorem diagonalIso_hom_app_apply (A : CosimplicialObject C) (B : SimplicialObject C)
    (n : SimplexCategoryᵒᵖ) (h : A.obj n.unop ⟶ B.obj n) :
    (diagonalIso A B).hom.app n h = h := rfl

/-- Its inverse is the same identity function on every original coefficient map. -/
@[simp]
theorem diagonalIso_inv_app_apply (A : CosimplicialObject C) (B : SimplicialObject C)
    (n : SimplexCategoryᵒᵖ) (h : A.obj n.unop ⟶ B.obj n) :
    (diagonalIso A B).inv.app n h = h := rfl

/-- The diagonal retains the complete original cosimplicial source action. -/
theorem diagonal_precomp {A A' : CosimplicialObject C} (a : A ⟶ A')
    (B : SimplicialObject C) :
    SSet.simplicialDiagonalFunctor.map (precomp a B) ≫ (diagonalIso A B).hom =
      (diagonalIso A' B).hom ≫ ResolutionHomComplex.precomp a B := by
  ext n h
  rfl

/-- The diagonal retains the complete original simplicial target action. -/
theorem diagonal_postcomp (A : CosimplicialObject C) {B B' : SimplicialObject C}
    (b : B ⟶ B') :
    SSet.simplicialDiagonalFunctor.map (postcomp A b) ≫ (diagonalIso A B').hom =
      (diagonalIso A B).hom ≫ ResolutionHomComplex.postcomp A b := by
  ext n h
  rfl

/-- The original augmentation comparison lands in the genuine canonical diagonal. -/
def fromAugmentation {A : CosimplicialObject C} {X : C}
    (a : A ⟶ (CosimplicialObject.const C).obj X) (B : SimplicialObject C) :
    ResolutionHomComplex.right X B ⟶ SSet.simplicialDiagonalFunctor.obj (obj A B) :=
  ResolutionHomComplex.fromAugmentation a B ≫ (diagonalIso A B).inv

/-- The original coaugmentation comparison lands in the same genuine canonical diagonal. -/
def fromCoaugmentation (A : CosimplicialObject C) {Y : C} {B : SimplicialObject C}
    (b : (SimplicialObject.const C).obj Y ⟶ B) :
    ResolutionHomComplex.left A Y ⟶ SSet.simplicialDiagonalFunctor.obj (obj A B) :=
  ResolutionHomComplex.fromCoaugmentation A b ≫ (diagonalIso A B).inv

/-- Every augmentation comparison simplex uses the original augmentation component. -/
theorem fromAugmentation_app_apply {A : CosimplicialObject C} {X : C}
    (a : A ⟶ (CosimplicialObject.const C).obj X) (B : SimplicialObject C)
    (n : SimplexCategoryᵒᵖ) (h : X ⟶ B.obj n) :
    (fromAugmentation a B).app n h = a.app n.unop ≫ h := rfl

/-- Every coaugmentation comparison simplex uses the original coaugmentation component. -/
theorem fromCoaugmentation_app_apply (A : CosimplicialObject C) {Y : C}
    {B : SimplicialObject C} (b : (SimplicialObject.const C).obj Y ⟶ B)
    (n : SimplexCategoryᵒᵖ) (h : A.obj n.unop ⟶ Y) :
    (fromCoaugmentation A b).app n h = h ≫ b.app n := rfl

/-- The whole original augmentation comparison is recovered through the identity diagonal map. -/
@[simp]
theorem fromAugmentation_diagonalIso {A : CosimplicialObject C} {X : C}
    (a : A ⟶ (CosimplicialObject.const C).obj X) (B : SimplicialObject C) :
    fromAugmentation a B ≫ (diagonalIso A B).hom =
      ResolutionHomComplex.fromAugmentation a B := by
  simp only [fromAugmentation, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The whole original coaugmentation comparison is recovered through the identity diagonal map. -/
@[simp]
theorem fromCoaugmentation_diagonalIso (A : CosimplicialObject C) {Y : C}
    {B : SimplicialObject C} (b : (SimplicialObject.const C).obj Y ⟶ B) :
    fromCoaugmentation A b ≫ (diagonalIso A B).hom =
      ResolutionHomComplex.fromCoaugmentation A b := by
  simp only [fromCoaugmentation, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every original source square is retained by the augmentation-to-diagonal map. -/
theorem fromAugmentation_source_naturality {A A' : CosimplicialObject C} {X X' : C}
    (a : A ⟶ (CosimplicialObject.const C).obj X)
    (a' : A' ⟶ (CosimplicialObject.const C).obj X') (t : A ⟶ A') (p : X ⟶ X')
    (ha : a ≫ (CosimplicialObject.const C).map p = t ≫ a') (B : SimplicialObject C) :
    ResolutionHomComplex.precomp ((CosimplicialObject.const C).map p) B ≫
        fromAugmentation a B =
      fromAugmentation a' B ≫ SSet.simplicialDiagonalFunctor.map (precomp t B) := by
  ext n h
  change X' ⟶ B.obj n at h
  have hn := congrArg (fun q => q.app n.unop) ha
  change a.app n.unop ≫ p = t.app n.unop ≫ a'.app n.unop at hn
  change a.app n.unop ≫ (p ≫ h) = t.app n.unop ≫ (a'.app n.unop ≫ h)
  rw [← Category.assoc, hn, Category.assoc]

/-- Every original target diagram map is retained by the augmentation-to-diagonal map. -/
theorem fromAugmentation_target_naturality {A : CosimplicialObject C} {X : C}
    (a : A ⟶ (CosimplicialObject.const C).obj X) {B B' : SimplicialObject C} (b : B ⟶ B') :
    fromAugmentation a B ≫ SSet.simplicialDiagonalFunctor.map (postcomp A b) =
      ResolutionHomComplex.postcomp ((CosimplicialObject.const C).obj X) b ≫
        fromAugmentation a B' := by
  ext n h
  change X ⟶ B.obj n at h
  exact Category.assoc _ _ _

/-- Every original source diagram map is retained by the coaugmentation-to-diagonal map. -/
theorem fromCoaugmentation_source_naturality {A A' : CosimplicialObject C} (a : A ⟶ A')
    {Y : C} {B : SimplicialObject C} (b : (SimplicialObject.const C).obj Y ⟶ B) :
    ResolutionHomComplex.precomp a ((SimplicialObject.const C).obj Y) ≫
        fromCoaugmentation A b =
      fromCoaugmentation A' b ≫ SSet.simplicialDiagonalFunctor.map (precomp a B) := by
  ext n h
  change A'.obj n.unop ⟶ Y at h
  exact Category.assoc _ _ _

/-- Every original target square is retained by the coaugmentation-to-diagonal map. -/
theorem fromCoaugmentation_target_naturality (A : CosimplicialObject C) {Y Y' : C}
    {B B' : SimplicialObject C} (b : (SimplicialObject.const C).obj Y ⟶ B)
    (b' : (SimplicialObject.const C).obj Y' ⟶ B') (q : Y ⟶ Y') (t : B ⟶ B')
    (hb : (SimplicialObject.const C).map q ≫ b' = b ≫ t) :
    ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map q) ≫
        fromCoaugmentation A b' =
      fromCoaugmentation A b ≫ SSet.simplicialDiagonalFunctor.map (postcomp A t) := by
  ext n h
  change A.obj n.unop ⟶ Y at h
  have hn := congrArg (fun r => r.app n) hb
  change q ≫ b'.app n = b.app n ≫ t.app n at hn
  change (h ≫ q) ≫ b'.app n = (h ≫ b.app n) ≫ t.app n
  rw [Category.assoc, hn, Category.assoc]

end HomotopicalAlgebra.ResolutionHomBisimplicial

end
