/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes

/-!
# Actual group-valued points of a p-divisible scheme tower

Every level is the native group of scheme-valued maps to that group
scheme. The functor is their pointwise filtered colimit in commutative groups.
On affine/quasicompact tests this agrees with the p-divisible sheaf.
General-scheme fppf sheafification is a separate construction.
Precomposition and the level inclusions are the prescribed morphisms.
This retains infinitesimal test algebras; field-valued points would erase
mu_p and cannot define its crystalline or tangent realization.

Scholze--Weinstein, arXiv:1211.6357v2, Sections1-2. Generic module Tate
limits and finite Cartier duality remain separate source-covered inputs.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisiblePointFunctors

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj
open PDivisibleGroupSchemes

variable (p : ℕ) [Fact p.Prime] (S : Scheme.{0}) (G : PDivisibleGroup S p)

/-- Native filtered commutative-group colimits, installed for this sequence shape. -/
instance commGrpSequenceColimits : HasColimitsOfShape ℕ CommGrpCat.{0} where
  has_colimit F := HasColimit.mk
    ⟨CommGrpCat.FilteredColimits.colimitCocone F,
      CommGrpCat.FilteredColimits.colimitCoconeIsColimit F⟩

/-- The actual commutative group Yoneda functor at a scheme level. -/
def levelPoints (n : ℕ) : (Over S)ᵒᵖ ⥤ CommGrpCat.{0} where
  obj T := CommGrpCat.of (T.unop ⟶ G.levels.obj n)
  map f := CommGrpCat.ofHom
    { toFun x := f.unop ≫ x
      map_one' := MonObj.comp_one _
      map_mul' x y := MonObj.comp_mul _ x y }
  map_id _ := by ext x; exact Category.id_comp _
  map_comp _ _ := by ext x; exact Category.assoc _ _ _

/-- The geometric level inclusions induce exactly these maps on all points. -/
def pointTower : ℕ ⥤ ((Over S)ᵒᵖ ⥤ CommGrpCat.{0}) where
  obj := levelPoints (p := p) (S := S) G
  map {n m} f := by
    letI : IsMonHom (G.levels.map f) := by
      have h : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
      rw [h]
      exact G.transition_group (leOfHom f)
    exact
      { app T := CommGrpCat.ofHom
          { toFun x := x ≫ G.levels.map f
            map_one' := MonObj.one_comp _
            map_mul' x y := MonObj.mul_comp x y _ }
        naturality {T U} g := by
          ext x
          change (g.unop ≫ x) ≫ G.levels.map f =
            g.unop ≫ (x ≫ G.levels.map f)
          exact Category.assoc _ _ _ }
  map_id n := by
    apply NatTrans.ext
    funext T
    ext x
    change x ≫ G.levels.map (𝟙 n) = x
    exact (congrArg (fun f : G.levels.obj n ⟶ G.levels.obj n ↦ x ≫ f)
      (G.levels.map_id n)).trans (Category.comp_id x)
  map_comp {n m k} f g := by
    apply NatTrans.ext
    funext T
    ext x
    change x ≫ G.levels.map (f ≫ g) =
      (x ≫ G.levels.map f) ≫ G.levels.map g
    exact (congrArg (fun h : G.levels.obj n ⟶ G.levels.obj k ↦ x ≫ h)
      (G.levels.map_comp f g)).trans (Category.assoc _ _ _).symm

/-- The pointwise level colimit; affine tests retain all infinitesimal points. -/
def pointwisePoints : (Over S)ᵒᵖ ⥤ CommGrpCat.{0} :=
  colimit (pointTower (p := p) (S := S) G)

/-- Each finite level maps into the actual group-valued colimit. -/
def levelInclusion (n : ℕ) : levelPoints (p := p) (S := S) G n ⟶
    pointwisePoints (p := p) (S := S) G :=
  colimit.ι (pointTower (p := p) (S := S) G) n

end MathlibExt.AlgebraicGeometry.PDivisiblePointFunctors
