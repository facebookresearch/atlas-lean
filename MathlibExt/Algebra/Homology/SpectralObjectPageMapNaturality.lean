/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.SpectralObjectPageMap
public import Mathlib.Algebra.Homology.SpectralObject.FirstPage

/-!
# Naturality of spectral-object page transports

The component of a fixed-page map commutes with the canonical transport from
the raw page object to any equal presentation as an `E` object.  This file
also identifies the identity-outer `EMap` through `EIsoH`, yielding naturality
of the canonical first-page homology presentation.  It isolates the dependent
equality casts needed by later page-level naturality arguments.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComposableArrows

universe v u uι uκ

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} [Preorder ι]
variable {κ : Type uκ} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
variable {X Y : SpectralObject C ι}

namespace Hom

private theorem EMap_heq_of_eq (phi : X ⟶ Y)
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ι}
    (ha₀ : a₀ = b₀) (ha₁ : a₁ = b₁)
    (ha₂ : a₂ = b₂) (ha₃ : a₃ = b₃)
    (f₁ : a₀ ⟶ a₁) (f₂ : a₁ ⟶ a₂) (f₃ : a₂ ⟶ a₃)
    (g₁ : b₀ ⟶ b₁) (g₂ : b₁ ⟶ b₂) (g₃ : b₂ ⟶ b₃)
    {m₀ m₁ m₂ n₀ n₁ n₂ : ℤ}
    (hm₀ : m₀ = n₀) (hm₁ : m₁ = n₁) (hm₂ : m₂ = n₂)
    (hm₁' : m₀ + 1 = m₁) (hm₂' : m₁ + 1 = m₂)
    (hn₁' : n₀ + 1 = n₁) (hn₂' : n₁ + 1 = n₂) :
    HEq (EMap phi f₁ f₂ f₃ m₀ m₁ m₂ hm₁' hm₂')
      (EMap phi g₁ g₂ g₃ n₀ n₁ n₂ hn₁' hn₂') := by
  subst b₀
  subst b₁
  subst b₂
  subst b₃
  subst n₀
  subst n₁
  subst n₂
  have hf₁ : f₁ = g₁ := Subsingleton.elim _ _
  have hf₂ : f₂ = g₂ := Subsingleton.elim _ _
  have hf₃ : f₃ = g₃ := Subsingleton.elim _ _
  subst g₁
  subst g₂
  subst g₃
  exact HEq.rfl

/-- Under the canonical `EIsoH` comparisons, the map on an `E` object with
identity outer arrows is the corresponding component of the spectral-object
morphism. -/
@[reassoc]
theorem EMap_EIsoH_hom
    (phi : X ⟶ Y) {i j : ι} (f : i ⟶ j)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    EMap phi (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ ≫
        (Y.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom =
      (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫
        (phi.hom n₁).app (mk₁ f) := by
  exact (ShortComplex.LeftHomologyMapData.ofZeros
    (shortComplexMap phi (𝟙 i) f (𝟙 j)
      n₀ n₁ n₂ hn₁ hn₂) ..).homologyMap_comm

private theorem EMap_EIsoH_hom_of_outer
    (phi : X ⟶ Y) {i j : ι}
    (f₁ : i ⟶ i) (f : i ⟶ j) (f₃ : j ⟶ j)
    (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    EMap phi f₁ f f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        (Y.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom =
      (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫
        (phi.hom n₁).app (mk₁ f) := by
  have hf₁ : f₁ = 𝟙 i := Subsingleton.elim _ _
  have hf₃ : f₃ = 𝟙 j := Subsingleton.elim _ _
  subst f₁
  subst f₃
  exact EMap_EIsoH_hom phi f n₀ n₁ n₂ hn₁ hn₂

/-- A fixed-page map component commutes with the canonical isomorphism from
the raw page object to an equal presentation as an `E` object. -/
@[reassoc]
theorem pageMapComponent_pageXIso_hom
    (phi : X ⟶ Y)
    (data : SpectralSequenceDataCore ι c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι)
    (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    pageMapComponent phi data r hr pq ≫
        (SpectralSequence.pageXIso Y data r hr pq
          i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom =
      (SpectralSequence.pageXIso X data r hr pq
          i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom ≫
        EMap phi
          (homOfLE (data.le₀₁' r hr pq h₀ h₁))
          (homOfLE (data.le₁₂' pq h₁ h₂))
          (homOfLE (data.le₂₃' r hr pq h₂ h₃))
          n₀ n₁ n₂ hn₁ hn₂ := by
  dsimp [pageMapComponent, SpectralSequence.pageXIso]
  apply eq_of_heq
  refine HEq.trans (comp_eqToHom_heq _ _) ?_
  refine HEq.trans ?_ (eqToHom_comp_heq _ _).symm
  exact EMap_heq_of_eq phi h₀.symm h₁.symm h₂.symm h₃.symm
    (homOfLE (data.le₀₁ r pq))
    (homOfLE (data.le₁₂ pq))
    (homOfLE (data.le₂₃ r pq))
    (homOfLE (data.le₀₁' r hr pq h₀ h₁))
    (homOfLE (data.le₁₂' pq h₁ h₂))
    (homOfLE (data.le₂₃' r hr pq h₂ h₃))
    (by lia) h.symm (by lia) (by lia) (by lia) hn₁ hn₂

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- A first-page map component commutes with the canonical identification of
the first-page object as the spectral-object homology of its middle index
arrow. -/
@[reassoc]
theorem pageMapComponent_spectralSequenceFirstPageXIso_hom
    (phi : X ⟶ Y)
    (data : SpectralSequenceDataCore ι c r₀)
    [data.HasFirstPageComputation]
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (pq : κ) (i₁ i₂ : ι)
    (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    pageMapComponent phi data r₀ (by rfl) pq ≫
        (Y.spectralSequenceFirstPageXIso data pq
          i₁ i₂ h₁ h₂ n₁ h).hom =
      (X.spectralSequenceFirstPageXIso data pq
          i₁ i₂ h₁ h₂ n₁ h).hom ≫
        (phi.hom n₁).app
          (mk₁ (homOfLE (data.le₁₂' pq h₁ h₂))) := by
  let h₀ : i₁ = data.i₀ r₀ pq := h₁.trans (data.hi₀₁ pq).symm
  let h₃ : i₂ = data.i₃ r₀ pq := h₂.trans (data.hi₂₃ pq)
  let ePX := SpectralSequence.pageXIso X data r₀ (by rfl) pq
    i₁ i₁ i₂ i₂ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂
  let ePY := SpectralSequence.pageXIso Y data r₀ (by rfl) pq
    i₁ i₁ i₂ i₂ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂
  let f := homOfLE (data.le₁₂' pq h₁ h₂)
  let eHX := X.EIsoH f n₀ n₁ n₂ hn₁ hn₂
  let eHY := Y.EIsoH f n₀ n₁ n₂ hn₁ hn₂
  let eMap := EMap phi
    (homOfLE (data.le₀₁' r₀ (by rfl) pq h₀ h₁)) f
    (homOfLE (data.le₂₃' r₀ (by rfl) pq h₂ h₃))
    n₀ n₁ n₂ hn₁ hn₂
  have hPage : pageMapComponent phi data r₀ (by rfl) pq ≫ ePY.hom =
      ePX.hom ≫ eMap :=
    pageMapComponent_pageXIso_hom phi data r₀ (by rfl) pq
      i₁ i₁ i₂ i₂ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂
  have hE : eMap ≫ eHY.hom =
      eHX.hom ≫ (phi.hom n₁).app (mk₁ f) := by
    simpa only [eMap, eHX, eHY, f] using
      EMap_EIsoH_hom_of_outer phi
        (homOfLE (data.le₀₁' r₀ (by rfl) pq h₀ h₁)) f
        (homOfLE (data.le₂₃' r₀ (by rfl) pq h₂ h₃))
        n₀ n₁ n₂ hn₁ hn₂
  rw [Y.spectralSequenceFirstPageXIso_hom data pq
      i₁ i₂ h₁ h₂ n₀ n₁ n₂ h hn₁ hn₂,
    X.spectralSequenceFirstPageXIso_hom data pq
      i₁ i₂ h₁ h₂ n₀ n₁ n₂ h hn₁ hn₂]
  change pageMapComponent phi data r₀ (by rfl) pq ≫
      (ePY.hom ≫ eHY.hom) =
    (ePX.hom ≫ eHX.hom) ≫
      (phi.hom n₁).app (mk₁ f)
  rw [← Category.assoc, hPage, Category.assoc, hE, ← Category.assoc]

/-- Inverse orientation of `pageMapComponent_pageXIso_hom`: the map on the
chosen `E` presentation commutes with transport back to the raw page. -/
@[reassoc]
theorem EMap_pageXIso_inv
    (phi : X ⟶ Y)
    (data : SpectralSequenceDataCore ι c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι)
    (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    EMap phi
          (homOfLE (data.le₀₁' r hr pq h₀ h₁))
          (homOfLE (data.le₁₂' pq h₁ h₂))
          (homOfLE (data.le₂₃' r hr pq h₂ h₃))
          n₀ n₁ n₂ hn₁ hn₂ ≫
        (SpectralSequence.pageXIso Y data r hr pq
          i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv =
      (SpectralSequence.pageXIso X data r hr pq
          i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
        pageMapComponent phi data r hr pq := by
  let eX := SpectralSequence.pageXIso X data r hr pq
    i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂
  let eY := SpectralSequence.pageXIso Y data r hr pq
    i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂
  let eMap := EMap phi
    (homOfLE (data.le₀₁' r hr pq h₀ h₁))
    (homOfLE (data.le₁₂' pq h₁ h₂))
    (homOfLE (data.le₂₃' r hr pq h₂ h₃))
    n₀ n₁ n₂ hn₁ hn₂
  change eMap ≫ eY.inv = eX.inv ≫ pageMapComponent phi data r hr pq
  have hforward :
      pageMapComponent phi data r hr pq ≫ eY.hom = eX.hom ≫ eMap :=
    pageMapComponent_pageXIso_hom phi data r hr pq
      i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂
  apply (cancel_epi eX.hom).mp
  calc
    eX.hom ≫ (eMap ≫ eY.inv) =
        (eX.hom ≫ eMap) ≫ eY.inv := (Category.assoc _ _ _).symm
    _ = (pageMapComponent phi data r hr pq ≫ eY.hom) ≫ eY.inv := by
      rw [hforward]
    _ = pageMapComponent phi data r hr pq := by simp
    _ = eX.hom ≫ (eX.inv ≫ pageMapComponent phi data r hr pq) := by simp

end Hom

end CategoryTheory.Abelian.SpectralObject

end
