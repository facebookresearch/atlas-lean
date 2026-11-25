/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.UniverseScalarRestriction
public import MathlibExt.CategoryTheory.GradedObject.TensorAntidiagonal
public import MathlibExt.CategoryTheory.GradedObject.Preadditive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Actual graded tensor transport under original-ring scalar restriction

Native biproduct preservation and the actual balanced tensor isomorphisms
give the comparison. Its injection formula is literally the original
module tensor comparison followed by the mapped original graded injection.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ModuleCat.UniverseScalarRestriction

variable (R : Type u) [CommRing R]


local instance highFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{max u v} (LiftedRing.{u,v} R)) :=
  Abelian.hasFiniteBiproducts
local instance lowFiniteBiproducts : HasFiniteBiproducts (Modules.{u,v} R) := Abelian.hasFiniteBiproducts

/-- The actual pointwise scalar-restriction functor on native graded objects. -/
abbrev gradedFunctor : (GradedObject ℕ (ModuleCat.{max u v} (LiftedRing.{u,v} R))) ⥤
  (GradedObject ℕ (Modules.{u,v} R)) where
  obj X n := (toOriginal.{u,v} R).obj (X n)
  map f n := (toOriginal.{u,v} R).map (f n)
  map_id X := by funext n; exact (toOriginal.{u,v} R).map_id (X n)
  map_comp f g := by funext n; exact (toOriginal.{u,v} R).map_comp (f n) (g n)

/-- The actual component tensor comparison uses native finite biproduct
preservation, not a chosen inverse Künneth certificate. -/
def gradedTensorIsoComponent (X Y : (GradedObject ℕ (ModuleCat.{max u v} (LiftedRing.{u,v} R)))) (n : ℕ) :
    ((gradedFunctor.{u,v} R).obj X ⊗ (gradedFunctor.{u,v} R).obj Y) n ≅
      (toOriginal.{u,v} R).obj ((X ⊗ Y) n) :=
  GradedObject.TensorAntidiagonal.iso ((gradedFunctor.{u,v} R).obj X)
      ((gradedFunctor.{u,v} R).obj Y) n ≪≫
    biproduct.mapIso (fun ij : GradedObject.TensorAntidiagonal.Index n =>
      tensorIso.{u,v} R (X ij.val.1) (Y ij.val.2)) ≪≫
    ((toOriginal.{u,v} R).mapBiproduct (fun ij : GradedObject.TensorAntidiagonal.Index n =>
      X ij.val.1 ⊗ Y ij.val.2)).symm ≪≫
    (toOriginal.{u,v} R).mapIso (GradedObject.TensorAntidiagonal.iso X Y n).symm

/-- These component comparisons give an actual graded tensor isomorphism. -/
def gradedTensorIso (X Y : (GradedObject ℕ (ModuleCat.{max u v} (LiftedRing.{u,v} R)))) :
    (gradedFunctor.{u,v} R).obj X ⊗ (gradedFunctor.{u,v} R).obj Y ≅
      (gradedFunctor.{u,v} R).obj (X ⊗ Y) :=
  GradedObject.isoMk _ _ (gradedTensorIsoComponent.{u,v} R X Y)

@[reassoc (attr := simp)]
theorem ι_gradedTensorIso_hom (X Y : (GradedObject ℕ (ModuleCat.{max u v} (LiftedRing.{u,v} R)))) (p q n : ℕ)
  (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj ((gradedFunctor.{u,v} R).obj X)
      ((gradedFunctor.{u,v} R).obj Y) p q n h ≫ (gradedTensorIso.{u,v} R X Y).hom n =
      (tensorIso.{u,v} R (X p) (Y q)).hom ≫
        (toOriginal.{u,v} R).map (GradedObject.Monoidal.ιTensorObj X Y p q n h) := by
  change GradedObject.Monoidal.ιTensorObj ((gradedFunctor.{u,v} R).obj X)
      ((gradedFunctor.{u,v} R).obj Y) p q n h ≫
      (gradedTensorIsoComponent.{u,v} R X Y n).hom = _
  simp only [gradedTensorIsoComponent, GradedObject.TensorAntidiagonal.iso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [GradedObject.TensorAntidiagonal.ι_toBiproduct_assoc,
    biproduct.mapIso_hom, biproduct.ι_map_assoc, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc,
    ← Functor.map_comp, GradedObject.TensorAntidiagonal.ι_fromBiproduct]

/-- The actual graded tensor comparison is natural in both original graded maps. -/
@[reassoc]
theorem gradedTensorIso_naturality {X Y X' Y' : (GradedObject ℕ (ModuleCat.{max u v} (LiftedRing.{u,v} R)))}
  (f : X ⟶ X') (g : Y ⟶ Y') :
    ((gradedFunctor.{u,v} R).map f ⊗ₘ (gradedFunctor.{u,v} R).map g) ≫
      (gradedTensorIso.{u,v} R X' Y').hom =
    (gradedTensorIso.{u,v} R X Y).hom ≫ (gradedFunctor.{u,v} R).map (f ⊗ₘ g) := by
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  change GradedObject.Monoidal.ιTensorObj ((gradedFunctor.{u,v} R).obj X)
      ((gradedFunctor.{u,v} R).obj Y) p q n h ≫
      GradedObject.Monoidal.tensorHom ((gradedFunctor.{u,v} R).map f)
        ((gradedFunctor.{u,v} R).map g) n ≫ (gradedTensorIso.{u,v} R X' Y').hom n =
    GradedObject.Monoidal.ιTensorObj ((gradedFunctor.{u,v} R).obj X)
      ((gradedFunctor.{u,v} R).obj Y) p q n h ≫ (gradedTensorIso.{u,v} R X Y).hom n ≫
        (toOriginal.{u,v} R).map (GradedObject.Monoidal.tensorHom f g n)
  rw [GradedObject.Monoidal.ι_tensorHom_assoc, ι_gradedTensorIso_hom]
  have hs := congrArg (fun z => z ≫
    (toOriginal.{u,v} R).map (GradedObject.Monoidal.tensorHom f g n))
      (ι_gradedTensorIso_hom.{u,v} R X Y p q n h)
  refine Eq.trans ?_ hs.symm
  rw [tensorIso_naturality_assoc, Category.assoc, ← Functor.map_comp,
    ← GradedObject.Monoidal.ι_tensorHom, Functor.map_comp]

end ModuleCat.UniverseScalarRestriction
