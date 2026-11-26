/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.SpectralObjectMap

public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Naturality of maps between spectral-object E-objects

The same-object map on an `E` object induced by a morphism of indexing
three-arrows commutes with the cross-object map induced by a morphism of
spectral objects.  We first prove the corresponding interchange law for the
defining short complexes and then pass to homology.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComposableArrows

universe v u vι uι

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Category.{vι} ι]
variable {X Y : SpectralObject C ι}

namespace Hom

/-- Mapping a defining short complex in its indexing three-arrow and mapping
it along a morphism of spectral objects commute. -/
@[reassoc]
theorem shortComplexMap_naturality
    (phi : X ⟶ Y)
    {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (g₁ : j₀ ⟶ j₁) (g₂ : j₁ ⟶ j₂) (g₃ : j₂ ⟶ j₃)
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplexMap f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ ≫
        shortComplexMap phi g₁ g₂ g₃ n₀ n₁ n₂ hn₁ hn₂ =
      shortComplexMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        Y.shortComplexMap f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ := by
  apply ShortComplex.Hom.ext
  · exact (phi.hom n₀).naturality _
  · exact (phi.hom n₁).naturality _
  · exact (phi.hom n₂).naturality _

/-- The same-object map on an `E` object commutes with the map induced by a
morphism of spectral objects. -/
@[reassoc]
theorem map_EMap
    (phi : X ⟶ Y)
    {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (g₁ : j₀ ⟶ j₁) (g₂ : j₁ ⟶ j₂) (g₃ : j₂ ⟶ j₃)
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ ≫
        EMap phi g₁ g₂ g₃ n₀ n₁ n₂ hn₁ hn₂ =
      EMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        Y.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ := by
  change ShortComplex.homologyMap
        (X.shortComplexMap f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂) ≫
      ShortComplex.homologyMap
        (shortComplexMap phi g₁ g₂ g₃ n₀ n₁ n₂ hn₁ hn₂) =
    ShortComplex.homologyMap
        (shortComplexMap phi f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
      ShortComplex.homologyMap
        (Y.shortComplexMap f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂)
  exact ShortComplex.homologyMap_square
    (shortComplexMap_naturality phi f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂)

end Hom

end CategoryTheory.Abelian.SpectralObject

end
