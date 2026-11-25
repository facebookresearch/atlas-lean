/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Full original cosimplicial Hom input category

Every complete represented Hom simplex is the same actual
cosimplicial source object mapped to the original target. Both inverse
functors retain every source operator and original map. Category object
and Hom universes are independent; the canonical standard-simplex
universe equals the supplied Hom universe.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The full original Hom simplicial object of a cosimplicial source at the supplied target. -/
def homSpace (D : CosimplicialObject C) (K : C) : SSet.{v} := D.op ⋙ yoneda.obj K

private theorem homSpace_yoneda_precomp (D : CosimplicialObject C) (K : C)
    {n m : SimplexCategory} (θ : n ⟶ m) (g : SSet.stdSimplex.{v}.obj m ⟶ homSpace D K) :
    SSet.yonedaEquiv (SSet.stdSimplex.map θ ≫ g) = D.map θ ≫ SSet.yonedaEquiv g := by
  have h := g.naturality θ.op
  have ht := ConcreteCategory.congr_hom h (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.{v}.obj m)))
  exact ht

/-- The same full original represented Hom simplex evaluated at its original cosimplicial source. -/
def inputOfSimplex (D : CosimplicialObject C) (K : C)
    (s : CostructuredArrow SSet.stdSimplex.{v} (homSpace D K)) : CostructuredArrow D K :=
  CostructuredArrow.mk (SSet.yonedaEquiv s.hom)

/-- Every whole original simplex operator is the same actual cosimplicial input arrow. -/
def simplexToInput (D : CosimplicialObject C) (K : C) :
    CostructuredArrow SSet.stdSimplex.{v} (homSpace D K) ⥤ CostructuredArrow D K where
  obj := inputOfSimplex D K
  map {s t} f := CostructuredArrow.homMk f.left (by
    have h := congrArg SSet.yonedaEquiv (CostructuredArrow.w f)
    exact (homSpace_yoneda_precomp D K f.left t.hom).symm.trans h)
  map_id s := by
    apply CostructuredArrow.hom_ext
    rfl
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    rfl

/-- The inverse keeps the same original complete Hom as its represented simplex. -/
def inputToSimplex (D : CosimplicialObject C) (K : C) :
    CostructuredArrow D K ⥤ CostructuredArrow SSet.stdSimplex.{v} (homSpace D K) where
  obj s := CostructuredArrow.mk (SSet.yonedaEquiv.symm s.hom)
  map {s t} f := CostructuredArrow.homMk f.left (by
    apply SSet.yonedaEquiv.injective
    change SSet.yonedaEquiv (SSet.stdSimplex.map f.left ≫
      (SSet.yonedaEquiv (X := homSpace D K)).symm t.hom) =
        SSet.yonedaEquiv ((SSet.yonedaEquiv (X := homSpace D K)).symm s.hom)
    exact (homSpace_yoneda_precomp D K f.left (SSet.yonedaEquiv.symm t.hom)).trans
      ((congrArg (fun g => D.map f.left ≫ g)
        (Equiv.apply_symm_apply (SSet.yonedaEquiv (X := homSpace D K)) t.hom)).trans
        ((CostructuredArrow.w f).trans
          (Equiv.apply_symm_apply (SSet.yonedaEquiv (X := homSpace D K)) s.hom).symm)))
  map_id s := by
    apply CostructuredArrow.hom_ext
    rfl
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    rfl

/-- Both full original input functors are inverse through the literal complete original Hom maps. -/
def homInputEquivalence (D : CosimplicialObject C) (K : C) :
    CostructuredArrow SSet.stdSimplex.{v} (homSpace D K) ≌ CostructuredArrow D K where
  functor := simplexToInput D K
  inverse := inputToSimplex D K
  unitIso := NatIso.ofComponents
    (fun s => CostructuredArrow.isoMk (Iso.refl _)
      (by
        change SSet.stdSimplex.map (𝟙 s.left) ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv s.hom) =
          s.hom
        exact (congrArg (fun f => f ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv s.hom))
          (SSet.stdSimplex.{v}.map_id s.left)).trans
            ((Category.id_comp _).trans (Equiv.symm_apply_apply SSet.yonedaEquiv s.hom))))
    (by
      intro s t f
      apply CostructuredArrow.hom_ext
      change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents
    (fun s => CostructuredArrow.isoMk (Iso.refl _)
      (by
        change D.map (𝟙 s.left) ≫ s.hom = SSet.yonedaEquiv
          ((SSet.yonedaEquiv (X := homSpace D K)).symm s.hom)
        exact (congrArg (fun f => f ≫ s.hom) (D.map_id s.left)).trans
          ((Category.id_comp _).trans
            (Equiv.apply_symm_apply (SSet.yonedaEquiv (X := homSpace D K)) s.hom).symm)))
    (by
      intro s t f
      apply CostructuredArrow.hom_ext
      change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

end CategoryTheory.CosimplicialObject
