/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.SpectralObjectMapNaturality

/-! # Tests for naturality of spectral-object E-maps -/

@[expose] public section

noncomputable section

open CategoryTheory ComposableArrows

universe v u vι uι

namespace MathlibExtTest.SpectralObjectMapNaturality

open CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Category.{vι} ι]
variable {X Y : SpectralObject C ι}

#check SpectralObject.Hom.shortComplexMap_naturality
#check SpectralObject.Hom.shortComplexMap_naturality_assoc
#check SpectralObject.Hom.map_EMap
#check SpectralObject.Hom.map_EMap_assoc

-- Boundary check: all indices coincide and the indexing three-arrow map is
-- the identity.
example (phi : X ⟶ Y) (i : ι) :
    X.map (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 _)
          (-1) 0 1 (by omega) (by omega) ≫
        phi.EMap (𝟙 i) (𝟙 i) (𝟙 i) (-1) 0 1 (by omega) (by omega) =
      phi.EMap (𝟙 i) (𝟙 i) (𝟙 i) (-1) 0 1 (by omega) (by omega) ≫
        Y.map (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 _)
          (-1) 0 1 (by omega) (by omega) :=
  phi.map_EMap (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 _)
    (-1) 0 1 (by omega) (by omega)

-- Boundary check: the spectral-object morphism may be the identity for an
-- arbitrary indexing three-arrow map.
example (X : SpectralObject C ι)
    {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (g₁ : j₀ ⟶ j₁) (g₂ : j₁ ⟶ j₂) (g₃ : j₂ ⟶ j₃)
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃) :
    X.map f₁ f₂ f₃ g₁ g₂ g₃ α (-1) 0 1 (by omega) (by omega) ≫
        SpectralObject.Hom.EMap (𝟙 X) g₁ g₂ g₃ (-1) 0 1 (by omega) (by omega) =
      SpectralObject.Hom.EMap (𝟙 X) f₁ f₂ f₃ (-1) 0 1 (by omega) (by omega) ≫
        X.map f₁ f₂ f₃ g₁ g₂ g₃ α (-1) 0 1 (by omega) (by omega) :=
  SpectralObject.Hom.map_EMap (𝟙 X) f₁ f₂ f₃ g₁ g₂ g₃ α
    (-1) 0 1 (by omega) (by omega)

#print axioms SpectralObject.Hom.shortComplexMap_naturality
#print axioms SpectralObject.Hom.map_EMap

end MathlibExtTest.SpectralObjectMapNaturality

end
