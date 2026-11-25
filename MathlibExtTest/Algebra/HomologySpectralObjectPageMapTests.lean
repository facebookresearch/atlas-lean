/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.SpectralObjectPageMap

/-! # Tests for maps between spectral-object pages -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ComposableArrows

universe v u vι uι uκ

namespace MathlibExtTest.SpectralObjectPageMap

open CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Category.{vι} ι]
variable {X Y : SpectralObject C ι}

#check SpectralObject.Hom.EMap_d

-- Degenerate-index boundary: differential naturality allows every index
-- arrow to be an identity.
example (phi : X ⟶ Y) (i : ι) :
    SpectralObject.Hom.EMap phi (𝟙 i) (𝟙 i) (𝟙 i)
          (-1) 0 1 (by omega) (by omega) ≫
        Y.d (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i)
          (-1) 0 1 2 (by omega) (by omega) (by omega) =
      X.d (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i)
          (-1) 0 1 2 (by omega) (by omega) (by omega) ≫
        SpectralObject.Hom.EMap phi (𝟙 i) (𝟙 i) (𝟙 i)
          0 1 2 (by omega) (by omega) :=
  SpectralObject.Hom.EMap_d phi (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i) (𝟙 i)
    (-1) 0 1 2 (by omega) (by omega) (by omega)

#print axioms SpectralObject.Hom.EMap_d

end MathlibExtTest.SpectralObjectPageMap

namespace MathlibExtTest.SpectralObjectPageMap

open CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Preorder ι]
variable {κ : Type uκ} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
variable {X Y Z : SpectralObject C ι}

#check SpectralObject.Hom.pageMapComponent
#check SpectralObject.Hom.pageMapComponent_comm
#check SpectralObject.Hom.pageMap
#check SpectralObject.spectralObjectPageFunctor

example (phi : X ⟶ Y)
    (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
    (r : ℤ) (hr : r₀ ≤ r) :
    SpectralObject.SpectralSequence.page X data r hr ⟶
      SpectralObject.SpectralSequence.page Y data r hr :=
  phi.pageMap data r hr

example (phi : X ⟶ Y)
    (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) :
    phi.pageMapComponent data r hr pq ≫
        SpectralObject.SpectralSequence.pageD Y data r pq pq' hr =
      SpectralObject.SpectralSequence.pageD X data r pq pq' hr ≫
        phi.pageMapComponent data r hr pq' :=
  phi.pageMapComponent_comm data r hr pq pq'

-- Non-Rel boundary: the page differential is definitionally the zero branch.
example (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ)
    (hpq : ¬(c r).Rel pq pq') :
    SpectralObject.SpectralSequence.pageD X data r pq pq' hr = 0 := by
  simp [SpectralObject.SpectralSequence.pageD, hpq]

example (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
    (r : ℤ) (hr : r₀ ≤ r) :
    SpectralObject C ι ⥤ HomologicalComplex C (c r) :=
  SpectralObject.spectralObjectPageFunctor data r hr

#print axioms SpectralObject.Hom.pageMap
#print axioms SpectralObject.spectralObjectPageFunctor

end MathlibExtTest.SpectralObjectPageMap

end
