/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Homology.SpectralObject.Page

/-!
# Maps between the E-objects of spectral objects

A morphism of abelian spectral objects maps the three-term short complex
defining an `E` object to the corresponding short complex of the target.  Its
components are the morphism on `H` in the three consecutive degrees, and the
required squares are exactly the connecting-map compatibility stored in the
spectral-object morphism.  Taking short-complex homology gives the induced map
on `E` objects.

This file does not construct page complexes or a morphism of spectral
sequences.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ComposableArrows

universe v u vι uι

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Category.{vι} ι]
variable {X Y Z : SpectralObject C ι}

namespace Hom

/-- A morphism of spectral objects maps the short complex defining an `E`
object to the corresponding short complex of the target spectral object. -/
@[simps]
def shortComplexMap (phi : X ⟶ Y)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶
      Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ where
  τ₁ := (phi.hom n₀).app (mk₁ f₃)
  τ₂ := (phi.hom n₁).app (mk₁ f₂)
  τ₃ := (phi.hom n₂).app (mk₁ f₁)
  comm₁₂ := (phi.comm n₀ n₁ hn₁ f₂ f₃).symm
  comm₂₃ := (phi.comm n₁ n₂ hn₂ f₁ f₂).symm

@[simp]
theorem shortComplexMap_id (X : SpectralObject C ι)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    shortComplexMap (𝟙 X) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ := by
  apply ShortComplex.Hom.ext <;> rfl

@[reassoc, simp]
theorem shortComplexMap_comp (phi : X ⟶ Y) (psi : Y ⟶ Z)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    shortComplexMap (phi ≫ psi) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      shortComplexMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        shortComplexMap psi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  apply ShortComplex.Hom.ext <;> rfl

/-- The map on an `E` object induced by a morphism of spectral objects. -/
noncomputable def EMap (phi : X ⟶ Y)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶
      Y.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  ShortComplex.homologyMap
    (shortComplexMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

@[simp]
theorem EMap_id (X : SpectralObject C ι)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    EMap (𝟙 X) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ := by
  change ShortComplex.homologyMap
      (shortComplexMap (𝟙 X) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) =
    𝟙 (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homology
  rw [shortComplexMap_id X f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂,
    ShortComplex.homologyMap_id]

@[reassoc, simp]
theorem EMap_comp (phi : X ⟶ Y) (psi : Y ⟶ Z)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    EMap (phi ≫ psi) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      EMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        EMap psi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  change ShortComplex.homologyMap
      (shortComplexMap (phi ≫ psi) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) =
    ShortComplex.homologyMap
        (shortComplexMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
      ShortComplex.homologyMap
        (shortComplexMap psi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)
  rw [shortComplexMap_comp phi psi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂,
    ShortComplex.homologyMap_comp]

end Hom

/-- Evaluation of spectral objects at a fixed `E` object is functorial. -/
noncomputable def EFunctor
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    SpectralObject C ι ⥤ C where
  obj X := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  map phi := phi.EMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  map_id X := Hom.EMap_id X f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  map_comp phi psi :=
    Hom.EMap_comp phi psi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂

end CategoryTheory.Abelian.SpectralObject

end
