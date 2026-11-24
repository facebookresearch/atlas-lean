/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.SpectralObjectPageMapNaturality

/-! # Tests for naturality of spectral-object page transports -/

@[expose] public section

noncomputable section

open CategoryTheory ComposableArrows

universe v u uι uκ

namespace MathlibExtTest.SpectralObjectPageMapNaturality

open CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Preorder ι]
variable {κ : Type uκ} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
variable {X Y Z : SpectralObject C ι}

#check SpectralObject.Hom.EMap_EIsoH_hom
#check SpectralObject.Hom.EMap_EIsoH_hom_assoc
#check SpectralObject.Hom.pageMapComponent_pageXIso_hom
#check SpectralObject.Hom.pageMapComponent_pageXIso_hom_assoc
#check SpectralObject.Hom.pageMapComponent_spectralSequenceFirstPageXIso_hom
#check SpectralObject.Hom.pageMapComponent_spectralSequenceFirstPageXIso_hom_assoc
#check SpectralObject.Hom.EMap_pageXIso_inv
#check SpectralObject.Hom.EMap_pageXIso_inv_assoc

section EMapToHomology

example (phi : X ⟶ Y) {i j : ι} (f : i ⟶ j)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    phi.EMap (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ ≫
        (Y.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom =
      (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫
        (phi.hom n₁).app (mk₁ f) :=
  phi.EMap_EIsoH_hom f n₀ n₁ n₂ hn₁ hn₂

-- Identity spectral-object maps use the same left-to-right orientation.
example (X : SpectralObject C ι) {i j : ι} (f : i ⟶ j) :
    SpectralObject.Hom.EMap (𝟙 X) (𝟙 i) f (𝟙 j)
          (-1) 0 1 (by omega) (by omega) ≫
        (X.EIsoH f (-1) 0 1 (by omega) (by omega)).hom =
      (X.EIsoH f (-1) 0 1 (by omega) (by omega)).hom ≫
        ((𝟙 X : X ⟶ X).hom 0).app (mk₁ f) :=
  SpectralObject.Hom.EMap_EIsoH_hom (𝟙 X) f
    (-1) 0 1 (by omega) (by omega)

-- Composite spectral-object maps are accepted without changing endpoints.
example (phi : X ⟶ Y) (psi : Y ⟶ Z) {i j : ι} (f : i ⟶ j)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (phi ≫ psi).EMap (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ ≫
        (Z.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom =
      (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫
        ((phi ≫ psi).hom n₁).app (mk₁ f) :=
  (phi ≫ psi).EMap_EIsoH_hom f n₀ n₁ n₂ hn₁ hn₂

end EMapToHomology

section FirstPage

variable (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
  [data.HasFirstPageComputation]
  [X.HasSpectralSequence data] [Y.HasSpectralSequence data]

-- The canonical indices and degrees recover the direct first-page square.
unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
example (phi : X ⟶ Y) (pq : κ) :
    phi.pageMapComponent data r₀ (by rfl) pq ≫
        (Y.spectralSequenceFirstPageXIso data pq
          (data.i₁ pq) (data.i₂ pq) rfl rfl
          (data.deg pq) rfl).hom =
      (X.spectralSequenceFirstPageXIso data pq
          (data.i₁ pq) (data.i₂ pq) rfl rfl
          (data.deg pq) rfl).hom ≫
        (phi.hom (data.deg pq)).app
          (mk₁ (homOfLE (data.le₁₂' pq rfl rfl))) :=
  phi.pageMapComponent_spectralSequenceFirstPageXIso_hom data pq
    (data.i₁ pq) (data.i₂ pq) rfl rfl
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
    rfl (by omega) (by omega)

-- Arbitrary equal presentations exercise all index and degree casts.
unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
example (phi : X ⟶ Y) (pq : κ) (i₁ i₂ : ι)
    (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    phi.pageMapComponent data r₀ (by rfl) pq ≫
        (Y.spectralSequenceFirstPageXIso data pq
          i₁ i₂ h₁ h₂ n₁ h).hom =
      (X.spectralSequenceFirstPageXIso data pq
          i₁ i₂ h₁ h₂ n₁ h).hom ≫
        (phi.hom n₁).app
          (mk₁ (homOfLE (data.le₁₂' pq h₁ h₂))) :=
  phi.pageMapComponent_spectralSequenceFirstPageXIso_hom data pq
    i₁ i₂ h₁ h₂ n₀ n₁ n₂ h hn₁ hn₂

end FirstPage

#guard_msgs (error, substring := true) in
#check SpectralObject.Hom.EMap_heq_of_eq

-- Boundary check: the canonical indices and degrees recover the raw page
-- presentation itself.
example (phi : X ⟶ Y) (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    phi.pageMapComponent data r hr pq ≫
        (SpectralObject.SpectralSequence.pageXIso Y data r hr pq
          (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq)
          rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
          rfl (by omega) (by omega)).hom =
      (SpectralObject.SpectralSequence.pageXIso X data r hr pq
          (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq)
          rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
          rfl (by omega) (by omega)).hom ≫
        phi.EMap
          (homOfLE (data.le₀₁' r hr pq rfl rfl))
          (homOfLE (data.le₁₂' pq rfl rfl))
          (homOfLE (data.le₂₃' r hr pq rfl rfl))
          (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
          (by omega) (by omega) :=
  phi.pageMapComponent_pageXIso_hom data r hr pq
    (data.i₀ r pq) (data.i₁ pq) (data.i₂ pq) (data.i₃ r pq)
    rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
    rfl (by omega) (by omega)

-- Boundary check: all four chosen preorder indices may coincide.  This also
-- exercises the inverse orientation.
example (phi : X ⟶ Y) (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ) (i : ι)
    (h₀ : i = data.i₀ r pq) (h₁ : i = data.i₁ pq)
    (h₂ : i = data.i₂ pq) (h₃ : i = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    phi.EMap
          (homOfLE (data.le₀₁' r hr pq h₀ h₁))
          (homOfLE (data.le₁₂' pq h₁ h₂))
          (homOfLE (data.le₂₃' r hr pq h₂ h₃))
          n₀ n₁ n₂ hn₁ hn₂ ≫
        (SpectralObject.SpectralSequence.pageXIso Y data r hr pq
          i i i i h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv =
      (SpectralObject.SpectralSequence.pageXIso X data r hr pq
          i i i i h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
        phi.pageMapComponent data r hr pq :=
  phi.EMap_pageXIso_inv data r hr pq i i i i h₀ h₁ h₂ h₃
    n₀ n₁ n₂ h hn₁ hn₂

#print axioms SpectralObject.Hom.pageMapComponent_pageXIso_hom
#print axioms SpectralObject.Hom.EMap_EIsoH_hom
#print axioms
  SpectralObject.Hom.pageMapComponent_spectralSequenceFirstPageXIso_hom
#print axioms SpectralObject.Hom.EMap_pageXIso_inv

end MathlibExtTest.SpectralObjectPageMapNaturality

end
