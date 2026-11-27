/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.SpectralObjectMap

/-! # Tests for maps between spectral-object E-objects -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ComposableArrows

universe v u vι uι

namespace MathlibExtTest.SpectralObjectMap

open CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Category.{vι} ι]
variable {X Y Z : SpectralObject C ι}

#check SpectralObject.Hom.shortComplexMap
#check SpectralObject.Hom.EMap
#check SpectralObject.EFunctor

example (phi : X ⟶ Y)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶
      Y.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  phi.EMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂

-- Boundary check: all four indices may coincide and all three arrows may be
-- identities; the induced map of an identity spectral morphism is identity.
example (X : SpectralObject C ι) (i : ι) :
    SpectralObject.Hom.EMap (𝟙 X) (𝟙 i) (𝟙 i) (𝟙 i)
        (-1) 0 1 (by omega) (by omega) = 𝟙 _ :=
  SpectralObject.Hom.EMap_id X (𝟙 i) (𝟙 i) (𝟙 i)
    (-1) 0 1 (by omega) (by omega)

example (phi : X ⟶ Y) (psi : Y ⟶ Z) (i : ι) :
    SpectralObject.Hom.EMap (phi ≫ psi) (𝟙 i) (𝟙 i) (𝟙 i)
        (-1) 0 1 (by omega) (by omega) =
      SpectralObject.Hom.EMap phi (𝟙 i) (𝟙 i) (𝟙 i)
          (-1) 0 1 (by omega) (by omega) ≫
        SpectralObject.Hom.EMap psi (𝟙 i) (𝟙 i) (𝟙 i)
          (-1) 0 1 (by omega) (by omega) :=
  SpectralObject.Hom.EMap_comp phi psi (𝟙 i) (𝟙 i) (𝟙 i)
    (-1) 0 1 (by omega) (by omega)

#print axioms SpectralObject.Hom.shortComplexMap
#print axioms SpectralObject.Hom.EMap
#print axioms SpectralObject.EFunctor

end MathlibExtTest.SpectralObjectMap

end
