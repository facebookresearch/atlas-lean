/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.Algebra.Category.ModuleCat.NativeTorLongExactUniverse
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import MathlibExt.Algebra.Category.ModuleCat.ChangeOfRings
/-!
# Scalar tensor association for restricted coefficients

The coefficient order is N first. The scalar triangle R to S to Q gives
S-linear tensor cancellation and its naturality. The module tensor
associator commutes with both bicomplex differentials.
Flatness and finite length are not required.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor
universe u v
namespace ModuleCat.UniverseTensor
/-- The original S-linear cancellation keeps N first and uses the actual R to S to Q scalar
triangle. -/
def extendRestrictTensorComponentIso
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (a : R →+* S) (f : R →+* Q) (g : S →+* Q) (h : g.comp a = f)
    (N M : ModuleCat.{max u v} R) :
    ((tensoringLeft (ModuleCat.{max u v} S)).obj
        ((ModuleCat.extendScalars.{u,u,max u v} f ⋙ ModuleCat.restrictScalars.{max u v,u,u} g).obj N)).obj
          ((ModuleCat.extendScalars.{u,u,max u v} a).obj M) ≅
      (ModuleCat.extendScalars.{u,u,max u v} f ⋙ ModuleCat.restrictScalars.{max u v,u,u} g).obj (N ⊗ M) := by
  letI : Algebra R S := a.toAlgebra
  letI : Algebra S Q := g.toAlgebra
  letI : Algebra R Q := f.toAlgebra
  letI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq' h.symm
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (Q ⊗[R] N) M ≪≫ₗ
    TensorProduct.AlgebraTensorModule.assoc R R S Q N M).toModuleIso

/-- Scalar tensor cancellation is natural in the original second R-module, with its actual maps. -/
def extendRestrictTensorNatIso
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (a : R →+* S) (f : R →+* Q) (g : S →+* Q) (h : g.comp a = f)
    (N : ModuleCat.{max u v} R) :
    ModuleCat.extendScalars.{u,u,max u v} a ⋙
        (tensoringLeft (ModuleCat.{max u v} S)).obj
          ((ModuleCat.extendScalars.{u,u,max u v} f ⋙ ModuleCat.restrictScalars.{max u v,u,u} g).obj N) ≅
      (tensoringLeft (ModuleCat.{max u v} R)).obj N ⋙
        (ModuleCat.extendScalars.{u,u,max u v} f ⋙ ModuleCat.restrictScalars.{max u v,u,u} g) := by
  letI : Algebra R S := a.toAlgebra
  letI : Algebra S Q := g.toAlgebra
  letI : Algebra R Q := f.toAlgebra
  letI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq' h.symm
  exact NatIso.ofComponents (fun M => extendRestrictTensorComponentIso R S Q a f g h N M)
    (fun {X Y} k => by
      apply ModuleCat.hom_ext
      let cX := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (Q ⊗[R] N) X ≪≫ₗ
        TensorProduct.AlgebraTensorModule.assoc R R S Q N X
      let cY := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (Q ⊗[R] N) Y ≪≫ₗ
        TensorProduct.AlgebraTensorModule.assoc R R S Q N Y
      change cY.toLinearMap ∘ₗ TensorProduct.map (LinearMap.id (R := S) (M := Q ⊗[R] N))
          (k.hom.baseChange S) =
        ((k.hom.lTensor N).baseChange Q).restrictScalars S ∘ₗ cX.toLinearMap
      apply TensorProduct.ext
      apply LinearMap.ext
      intro z
      apply LinearMap.ext
      intro sm
      induction z using TensorProduct.inductionOn with
      | tmul q n =>
        induction sm using TensorProduct.inductionOn with
        | tmul s m => rfl
        | add z₁ z₂ h₁ h₂ =>
          simp only [map_add]
          rw [h₁, h₂]
      | add z₁ z₂ h₁ h₂ =>
        simp only [map_add, LinearMap.add_apply]
        rw [h₁, h₂])

/-- The scalar natural isomorphism compares the literal original coefficient complexes. -/
def extendRestrictTensorComplexIso
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (a : R →+* S) (f : R →+* Q) (g : S →+* Q) (h : g.comp a = f)
    (N : ModuleCat.{max u v} R) (C : ChainComplex (ModuleCat.{max u v} R) ℕ) :
    ((ModuleCat.extendScalars.{u,u,max u v} f ⋙ ModuleCat.restrictScalars.{max u v,u,u} g).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
      ((((tensoringLeft (ModuleCat.{max u v} R)).obj N).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C) ≅
      ((((tensoringLeft (ModuleCat.{max u v} S)).obj
        ((ModuleCat.extendScalars.{u,u,max u v} f ⋙
          ModuleCat.restrictScalars.{max u v,u,u} g).obj N)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
            (((ModuleCat.extendScalars.{u,u,max u v} a).mapHomologicalComplex (ComplexShape.down ℕ)).obj C)) := by
  let e := extendRestrictTensorNatIso R S Q a f g h N
  exact ((NatIso.mapHomologicalComplex e (ComplexShape.down ℕ)).app C).symm

/-- The original module tensor bifunctor applied to both original nonnegative chain complexes. -/
def tensorBicomplex (R : Type u) [CommRing R]
    (A B : ChainComplex (ModuleCat.{max u v} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) := by
  let F := curriedTensor (ModuleCat.{max u v} R)
  let : F.Additive := by dsimp [F]; infer_instance
  let : ∀ N : ModuleCat.{max u v} R, (F.obj N).Additive := fun N => CategoryTheory.tensorLeft_additive N
  exact ((F.mapBifunctorHomologicalComplex (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj A).obj B

/-- Tensor the original coefficient on the left in every term and both differentials of this
bicomplex. -/
def tensorLeftBicomplex (R : Type u) [CommRing R] (N : ModuleCat.{max u v} R)
    (B : HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) := by
  let T := (tensoringLeft (ModuleCat.{max u v} R)).obj N
  let : T.Additive := CategoryTheory.tensoringLeft_additive N
  exact ((T.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj B

/-- The actual module associator commutes with both original bicomplex differentials. -/
def tensorLeftBicomplexAssociator (R : Type u) [CommRing R]
    (N : ModuleCat.{max u v} R) (A B : ChainComplex (ModuleCat.{max u v} R) ℕ) :
    tensorBicomplex R ((((tensoringLeft (ModuleCat.{max u v} R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj A) B ≅ tensorLeftBicomplex R N (tensorBicomplex R A B) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun p => ?_) ?_
  · exact HomologicalComplex.Hom.isoOfComponents
      (fun q => α_ N (A.X p) (B.X q)) (fun q q' _ => by
        change (α_ N (A.X p) (B.X q)).hom ≫
            (𝟙 N ⊗ₘ (𝟙 (A.X p) ⊗ₘ B.d q q')) =
          (𝟙 (N ⊗ A.X p) ⊗ₘ B.d q q') ≫ (α_ N (A.X p) (B.X q')).hom
        exact (associator_naturality_right N (A.X p) (B.d q q')).symm)
  · intro p p' _
    apply HomologicalComplex.Hom.ext
    funext q
    change (α_ N (A.X p) (B.X q)).hom ≫
        (𝟙 N ⊗ₘ (A.d p p' ⊗ₘ 𝟙 (B.X q))) =
      ((𝟙 N ⊗ₘ A.d p p') ⊗ₘ 𝟙 (B.X q)) ≫ (α_ N (A.X p') (B.X q)).hom
    exact (associator_naturality_middle N (A.d p p') (B.X q)).symm

end ModuleCat.UniverseTensor
